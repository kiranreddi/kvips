"""AHB cocotb tests — real traffic through UVM VIP into RTL DUT."""

from __future__ import annotations

import os
import sys

import cocotb
from cocotb.triggers import Timer

ROOT = os.environ.get(
    "KVIPS_ROOT",
    os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", "..")),
)
sys.path.insert(0, os.path.join(ROOT, "common", "cocotb", "python"))

from kvips_cocotb import AhbMaster, DpiMonitor, KVIPS_PROTO_AHB  # noqa: E402


async def _setup(dut):
    ahb = AhbMaster(dut)
    await ahb.wait_ready()
    return ahb


@cocotb.test()
async def test_ahb_python_write_readback(dut):
    """Python-driven SINGLE transfers through UVM AHB master + DUT RAM."""
    ahb = await _setup(dut)
    mon = DpiMonitor()
    mon.reset()

    patterns = [
        (0x0000, 0xA5A55A5A),
        (0x0004, 0x12345678),
        (0x0040, 0xDEADBEEF),
        (0x00C0, 0x0110CAFE),
    ]
    for addr, data in patterns:
        got = await ahb.write_readback(addr, data)
        assert got == data, f"mismatch addr=0x{addr:x} exp=0x{data:x} got=0x{got:x}"

    events = mon.drain()
    assert len(events) >= len(patterns) * 2, f"DPI monitor too few events: {len(events)}"
    assert all(e.proto == KVIPS_PROTO_AHB for e in events)


@cocotb.test()
async def test_ahb_uvm_sequences(dut):
    """Launch the full RAM-DUT-compatible AHB sequence surface from Python.

    Sequence base addresses must be 1KB-aligned so legal_addr() stays within
    a single AHB 1KB burst window. boundary is the legal 1KB-edge INCR4 at 0x3F0.
    """
    ahb = await _setup(dut)
    await ahb.run_sequence("smoke", num_txns=12, base_addr=0x0000, wr_pct=50)
    await ahb.run_sequence("single", num_txns=10, base_addr=0x0400, wr_pct=60)
    await ahb.run_sequence("incr", num_txns=6, base_addr=0x0800)
    await ahb.run_sequence("wait", num_txns=8, base_addr=0x0C00)
    await ahb.run_sequence("b2b", num_txns=8, base_addr=0x1000, wr_pct=50)
    await ahb.run_sequence("wrap", num_txns=4, base_addr=0x1400)
    await ahb.run_sequence("busy", base_addr=0x0000)
    await ahb.run_sequence("stress", num_txns=20, base_addr=0x1800, wr_pct=55)
    await ahb.run_sequence("boundary")
    await ahb.run_sequence("endian")
    await ahb.run_sequence("full_resp")

    await ahb.write(0x1C00, 0x55AA33CC)
    got, _ = await ahb.read(0x1C00)
    assert got == 0x55AA33CC


@cocotb.test()
async def test_ahb_unsupported_on_ram_dut(dut):
    """Security/error opcodes return RSP_INVAL on the RAM DUT."""
    ahb = await _setup(dut)
    await ahb.run_sequence("security", allow_inval=True)
    await ahb.run_sequence("error", allow_inval=True)


@cocotb.test()
async def test_ahb_dpi_monitor_path(dut):
    """Verify DPI ring buffer receives monitor pushes for Python traffic."""
    ahb = await _setup(dut)
    mon = DpiMonitor()
    mon.reset()
    before = mon.total()

    for i in range(8):
        addr = 0x2000 + i * 4
        data = 0x10000000 + i
        await ahb.write(addr, data)
        got, _ = await ahb.read(addr)
        assert got == data

    await Timer(100, units="ns")
    after = mon.total()
    events = mon.drain()
    assert after >= before + 16, f"DPI total did not advance: before={before} after={after}"
    assert len(events) >= 16, f"expected >=16 DPI events, got {len(events)}"
    writes = [e for e in events if e.write]
    reads = [e for e in events if not e.write]
    assert len(writes) >= 8 and len(reads) >= 8
    await ahb.finish()
