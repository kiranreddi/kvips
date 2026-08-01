"""AXI4 cocotb tests — real traffic through UVM VIP into RTL DUT."""

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

from kvips_cocotb import Axi4Master, DpiMonitor, KVIPS_PROTO_AXI4  # noqa: E402


async def _setup(dut):
    axi = Axi4Master(dut, data_bytes=8)
    await axi.wait_ready()
    return axi


@cocotb.test()
async def test_axi4_python_write_readback(dut):
    """Python-driven single-beat and burst traffic through UVM AXI4 master + DUT."""
    axi = await _setup(dut)
    mon = DpiMonitor()
    mon.reset()

    patterns = [
        (0x0000_1000, 0xA5A5_5A5A_1234_5678),
        (0x0000_1008, 0xDEAD_BEEF_CAFE_BABE),
        (0x0000_1080, 0x0123_4567_89AB_CDEF),
    ]
    for addr, data in patterns:
        got = await axi.write_readback(addr, data)
        assert got == data, f"mismatch addr=0x{addr:x} exp=0x{data:x} got=0x{got:x}"

    beats = [0x1111_1111_1111_1111 + i for i in range(4)]
    bresp = await axi.write_burst(0x0000_2000, beats)
    assert bresp == 0
    got_beats, rresp = await axi.read_burst(0x0000_2000, 4)
    assert rresp == 0
    assert got_beats == beats, f"burst mismatch exp={beats} got={got_beats}"

    events = mon.drain()
    assert len(events) >= 8, f"DPI monitor too few events: {len(events)}"
    assert all(e.proto == KVIPS_PROTO_AXI4 for e in events)


@cocotb.test()
async def test_axi4_uvm_sequences(dut):
    """Launch the full RAM-DUT-compatible AXI4 sequence surface from Python."""
    axi = await _setup(dut)

    # Keep max_len small for deterministic Verilator runtime.
    await axi.run_sequence("write_readback", num_txns=8, base_addr=0x3000, max_len=0)
    await axi.run_sequence("write_burst", num_txns=4, start_addr=0x4000, max_len=0)
    await axi.run_sequence("read_burst", num_txns=4, start_addr=0x4000, max_len=0)
    await axi.run_sequence("stress", num_pairs=6, base_addr=0x5000, max_len=0)
    await axi.run_sequence("lane", base_addr=0x6000)
    await axi.run_sequence("strobe", base_addr=0x7000)
    await axi.run_sequence("concurrent", num_prefill=4, num_mixed=8, base_a=0xA000)
    await axi.run_sequence("unaligned", base_addr=0xB000)
    await axi.run_sequence("corner", base_addr=0xE000)
    await axi.run_sequence("incr256", num_txns=1, base_addr=0xC000)
    await axi.run_sequence("phase_api", base_addr=0xD000)
    await axi.run_sequence("wr_expect", addr=0x0010_0000, expected_bresp=2)  # DECERR
    await axi.run_sequence("rd_expect", addr=0x0010_0000, expected_rresp=2)
    await axi.run_sequence("same_id", num_txns=6, base_addr=0x7100)
    await axi.run_sequence("sideband", base_addr=0x8100)
    await axi.run_sequence("error_write", addr=0x0010_0000)
    await axi.run_sequence("error_read", addr=0x0010_0000)
    await axi.run_sequence("pipe_stress", num_pairs=4, base_addr=0x9000, max_len=0)

    await axi.write(0x0000_8000, 0x55AA_33CC_77EE_11FF)
    got, _ = await axi.read(0x0000_8000)
    assert got == 0x55AA_33CC_77EE_11FF


@cocotb.test()
async def test_axi4_unsupported_on_ram_dut(dut):
    """Exclusive/reset/timeout opcodes return RSP_INVAL on the RAM DUT."""
    axi = await _setup(dut)
    for name in (
        "exclusive_basic",
        "exclusive_fail",
        "exclusive_cross_id",
        "exclusive_illegal",
        "reset_recovery",
        "nonpipelined_reset",
        "timeout_recovery",
    ):
        await axi.run_sequence(name, allow_inval=True)


@cocotb.test()
async def test_axi4_dpi_monitor_path(dut):
    """Verify DPI ring buffer receives monitor pushes for Python traffic."""
    axi = await _setup(dut)
    mon = DpiMonitor()
    mon.reset()
    before = mon.total()

    for i in range(6):
        addr = 0x0000_9000 + i * 8
        data = 0xABC0_0000_0000_0000 + i
        await axi.write(addr, data)
        got, _ = await axi.read(addr)
        assert got == data

    await Timer(200, units="ns")
    after = mon.total()
    events = mon.drain()
    assert after >= before + 12, f"DPI total did not advance: before={before} after={after}"
    assert len(events) >= 12, f"expected >=12 DPI events, got {len(events)}"
    writes = [e for e in events if e.write]
    reads = [e for e in events if not e.write]
    assert len(writes) >= 6 and len(reads) >= 6
    await axi.finish()
