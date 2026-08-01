"""APB cocotb tests — real traffic through UVM VIP into RTL DUT."""

from __future__ import annotations

import os
import sys

import cocotb
from cocotb.triggers import Timer

# Make kvips_cocotb importable from the repo tree
ROOT = os.environ.get(
    "KVIPS_ROOT",
    os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", "..")),
)
sys.path.insert(0, os.path.join(ROOT, "common", "cocotb", "python"))

from kvips_cocotb import ApbMaster, DpiMonitor, KVIPS_PROTO_APB  # noqa: E402


async def _setup(dut):
    apb = ApbMaster(dut)
    await apb.wait_ready()
    return apb


@cocotb.test()
async def test_apb_python_write_readback(dut):
    """Python-driven single writes/reads through UVM APB master + DUT RAM."""
    apb = await _setup(dut)
    mon = DpiMonitor()
    mon.reset()

    patterns = [
        (0x0000, 0xA5A5_5A5A),
        (0x0004, 0x1234_5678),
        (0x0010, 0xDEAD_BEEF),
        (0x00FC, 0x0110_CAFE),
    ]
    for addr, data in patterns:
        got = await apb.write_readback(addr, data)
        assert got == data, f"mismatch addr=0x{addr:x} exp=0x{data:x} got=0x{got:x}"

    # Strobe-masked write: write full, then masked update, then read
    await apb.write(0x0020, 0xFFFF_FFFF, strb=0xF)
    await apb.write(0x0020, 0x0000_00AA, strb=0x1)
    got = await apb.read(0x0020)
    assert (got & 0xFF) == 0xAA, f"strobe low-byte failed got=0x{got:x}"

    events = mon.drain()
    assert len(events) >= len(patterns) * 2, f"DPI monitor too few events: {len(events)}"
    assert all(e.proto == KVIPS_PROTO_APB for e in events)

    cmds, mons, *_ = await apb.bridge.get_stats()
    assert cmds >= 1
    assert mons >= len(patterns)


@cocotb.test()
async def test_apb_uvm_sequences(dut):
    """Launch real UVM sequence library entries from Python."""
    apb = await _setup(dut)

    await apb.run_sequence("smoke", num_txns=12, base_addr=0x0100)
    await apb.run_sequence("stress", num_txns=40, base_addr=0x0200, span_bytes=256, wr_pct=60)
    await apb.run_sequence(
        "strobe",
        addr=0x0030,
        full_data=0xA5A55A5A,
        mask_data=0x11223344,
        strb=0x5,
        prot=1,
    )

    # Independent Python check that sequence traffic left data behind
    await apb.write(0x0400, 0x55AA_33CC)
    got = await apb.read(0x0400)
    assert got == 0x55AA_33CC


@cocotb.test()
async def test_apb_dpi_monitor_path(dut):
    """Verify DPI ring buffer receives monitor pushes for Python traffic."""
    apb = await _setup(dut)
    mon = DpiMonitor()
    mon.reset()
    before = mon.total()

    for i in range(8):
        addr = 0x0800 + i * 4
        data = 0x1000_0000 + i
        await apb.write(addr, data)
        got = await apb.read(addr)
        assert got == data

    await Timer(100, units="ns")
    after = mon.total()
    events = mon.drain()
    assert after >= before + 16, f"DPI total did not advance: before={before} after={after}"
    assert len(events) >= 16, f"expected >=16 DPI events, got {len(events)}"
    writes = [e for e in events if e.write]
    reads = [e for e in events if not e.write]
    assert len(writes) >= 8 and len(reads) >= 8
    # Graceful UVM shutdown after the last Python test
    await apb.finish()
