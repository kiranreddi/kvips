#!/usr/bin/env python3
"""Build and run a KVIPS cocotb+UVM example under Verilator with custom DPI."""

from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path
from typing import Sequence


def ensure_uvm(root: Path) -> Path:
    import subprocess

    env = os.environ.copy()
    env["ROOT"] = str(root)
    cmd = (
        f'source "{root}/scripts/ensure-verilator-uvm.sh" && '
        "ensure_verilator_uvm && printf %s \"$UVM_HOME\""
    )
    out = subprocess.check_output(["bash", "-lc", cmd], env=env, text=True).strip()
    uvm_home = Path(out.splitlines()[-1])
    if not uvm_home.is_dir():
        raise SystemExit(f"UVM_HOME not found: {uvm_home}")
    return uvm_home


def abs_sources(root: Path, filelist: Path) -> tuple[list[Path], list[str]]:
    sources: list[Path] = []
    includes: list[str] = []
    for raw in filelist.read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("+incdir+"):
            p = line[len("+incdir+") :]
            includes.append(str(root / p if not p.startswith("/") else Path(p)))
            continue
        if line.startswith("+") or line.startswith("-"):
            continue
        sources.append(root / line if not line.startswith("/") else Path(line))
    return sources, includes


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--protocol", choices=["apb", "axi4", "ahb"], required=True)
    ap.add_argument("--test-module", default=None)
    ap.add_argument("--testcase", default=None, help="Optional single cocotb test name")
    ap.add_argument("--jobs", type=int, default=max(1, (os.cpu_count() or 2) // 2))
    ap.add_argument("--waves", action="store_true")
    args = ap.parse_args()

    root = Path(__file__).resolve().parents[1]
    os.environ["KVIPS_ROOT"] = str(root)
    vbin = Path("/opt/verilator-5.048/bin")
    if vbin.is_dir():
        os.environ["PATH"] = f"{vbin}:{os.environ.get('PATH', '')}"

    py_path = root / "common" / "cocotb" / "python"
    os.environ["PYTHONPATH"] = (
        f"{py_path}:{os.environ['PYTHONPATH']}" if os.environ.get("PYTHONPATH") else str(py_path)
    )

    ex_dir = root / args.protocol / "examples" / "cocotb_dut"
    filelist = ex_dir / "sim" / "filelist.f"
    tests_dir = ex_dir / "tests"
    build_dir = ex_dir / "sim" / "out" / "cocotb_verilator"

    uvm_home = ensure_uvm(root)
    sources, includes = abs_sources(root, filelist)
    sources = [uvm_home / "uvm_pkg.sv"] + sources
    includes = [str(uvm_home), str(root / "common" / "cocotb" / "sv")] + includes

    dpi_c = root / "common" / "cocotb" / "sv" / "kvips_cocotb_dpi.c"
    dpi_h_dir = root / "common" / "cocotb" / "sv"

    test_module = args.test_module or f"test_{args.protocol}"
    sys.path.insert(0, str(tests_dir))
    sys.path.insert(0, str(py_path))

    from cocotb.runner import Verilator

    class KvipsVerilator(Verilator):
        """Verilator runner that avoids --public-flat-rw (breaks UVM process)."""

        @staticmethod
        def _get_define_options(defines):
            opts = []
            for name, value in defines.items():
                if value is None or value is True or value == "":
                    opts.append(f"-D{name}")
                else:
                    opts.append(f"-D{name}={value}")
            return opts

        def _build_command(self) -> Sequence[Sequence[str]]:
            cmds = super()._build_command()
            fixed = []
            for cmd in cmds:
                new_cmd = []
                i = 0
                while i < len(cmd):
                    tok = cmd[i]
                    if tok == "--public-flat-rw":
                        i += 1
                        continue
                    if tok == "-LDFLAGS" and i + 1 < len(cmd):
                        # Export DPI symbols so Python ctypes can resolve them.
                        ld = cmd[i + 1]
                        if "--export-dynamic" not in ld and "-rdynamic" not in ld:
                            ld = ld + " -Wl,--export-dynamic"
                        new_cmd.extend([tok, ld])
                        i += 2
                        continue
                    new_cmd.append(tok)
                    i += 1
                fixed.append(new_cmd)
            return fixed

    runner = KvipsVerilator()

    defines = {
        "UVM_NO_DPI": True,  # Accellera UVM DPI off (Verilator-safe)
        "UVM_USE_PROCESS_CONTAINER": True,
        "KVIPS_COCOTB_DPI": True,  # our custom DPI enabled
    }
    if args.protocol == "ahb":
        # Match uvm_dut Verilator timing path for the AHB master/DUT.
        defines["KVIPS_AHB_DUT_RAW_TIMING"] = True


    build_args = [
        "--timing",
        "--bbox-unsup",
        "--no-unlimited-stack",
        "-Wno-fatal",
        "-Wno-PKGNODECL",
        "-Wno-UNDRIVEN",
        "-Wno-TIMESCALEMOD",
        "-Wno-SYNCASYNCNET",
        "-Wno-MISINDENT",
        "-Wno-WIDTHTRUNC",
        "-Wno-WIDTHEXPAND",
        "-Wno-CASTCONST",
        "-Wno-REALCVT",
        "-Wno-CONSTRAINTIGN",
        "-Wno-SELRANGE",
        "-Wno-REDEFMACRO",
        "-j",
        str(args.jobs),
        "-CFLAGS",
        f"-Wno-deprecated-declarations -I{dpi_h_dir}",
        str(dpi_c),
    ]

    toplevel = "tb_top" if args.protocol == "apb" else "top"

    plusargs = ["+UVM_NO_RELNOTES", "+UVM_VERBOSITY=UVM_LOW"]
    if args.protocol == "apb":
        plusargs.append("+APB_PROTOCOL=APB4")

    if args.testcase:
        os.environ["TESTCASE"] = args.testcase

    runner.build(
        verilog_sources=sources,
        includes=includes,
        defines=defines,
        hdl_toplevel=toplevel,
        build_dir=str(build_dir),
        build_args=build_args,
        always=True,
        waves=args.waves,
        timescale=("1ns", "1ps"),
        verbose=True,
    )

    # Also mark clk/rst public via plusargs? cocotb needs rising_edge on bridge.clk
    # bridge.clk is a port — make top-level clocks public with verilator public in top.

    runner.test(
        hdl_toplevel=toplevel,
        test_module=test_module,
        build_dir=str(build_dir),
        plusargs=plusargs,
        waves=args.waves,
        verbose=True,
        extra_env={
            "KVIPS_ROOT": str(root),
            "PYTHONPATH": os.environ["PYTHONPATH"],
        },
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
