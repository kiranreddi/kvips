"""AXI4 master facade — issues commands that UVM AXI4 VIP executes."""

from __future__ import annotations

from .bridge import CocotbBridge, BridgeError
from .opcodes import (
    KVIPS_AXI4_WRITE,
    KVIPS_AXI4_READ,
    KVIPS_AXI4_WRITE_BURST,
    KVIPS_AXI4_READ_BURST,
    KVIPS_AXI4_SEQ_WRB,
    KVIPS_AXI4_SEQ_WBRST,
    KVIPS_AXI4_SEQ_RBRST,
    KVIPS_AXI4_SEQ_STRESS,
    KVIPS_AXI4_SEQ_LANE,
    KVIPS_AXI4_SEQ_STROBE,
    KVIPS_AXI4_SEQ_CONCURRENT,
    KVIPS_AXI4_SEQ_UNALIGNED,
    KVIPS_AXI4_SEQ_CORNER,
    KVIPS_AXI4_SEQ_INCR256,
    KVIPS_AXI4_SEQ_PHASE_API,
    KVIPS_AXI4_SEQ_WR_EXPECT,
    KVIPS_AXI4_SEQ_RD_EXPECT,
    KVIPS_AXI4_SEQ_SAME_ID,
    KVIPS_AXI4_SEQ_SIDEBAND,
    KVIPS_AXI4_SEQ_EXCL_BASIC,
    KVIPS_AXI4_SEQ_EXCL_FAIL,
    KVIPS_AXI4_SEQ_EXCL_XID,
    KVIPS_AXI4_SEQ_EXCL_ILL,
    KVIPS_AXI4_SEQ_ERR_WR,
    KVIPS_AXI4_SEQ_ERR_RD,
    KVIPS_AXI4_SEQ_RESET,
    KVIPS_AXI4_SEQ_NP_RESET,
    KVIPS_AXI4_SEQ_TIMEOUT,
    KVIPS_AXI4_SEQ_PIPE_STRESS,
    KVIPS_RSP_OK,
    KVIPS_RSP_INVAL,
)

# Sequences that require VIP-slave / mid-run-reset features not present on the RAM DUT.
_UNSUPPORTED_ON_RAM_DUT = {
    "exclusive_basic",
    "exclusive_fail",
    "exclusive_cross_id",
    "exclusive_illegal",
    "reset_recovery",
    "nonpipelined_reset",
    "timeout_recovery",
}


class Axi4Master:
    def __init__(self, dut, bridge_name: str = "bridge", data_bytes: int = 8):
        self.bridge = CocotbBridge(dut, bridge_name=bridge_name)
        self.data_bytes = data_bytes

    async def wait_ready(self) -> None:
        await self.bridge.wait_ready()
        await self.bridge.ping()

    async def write(
        self,
        addr: int,
        data: int,
        *,
        size: int | None = None,
        burst_id: int = 0,
        strb: int | None = None,
    ) -> int:
        if size is None:
            size = self.data_bytes.bit_length() - 1
        if strb is None:
            strb = (1 << self.data_bytes) - 1
        status, bresp, *_ = await self.bridge.call(
            KVIPS_AXI4_WRITE, a0=addr, a1=data, a2=size, a3=burst_id, a4=strb
        )
        if status != KVIPS_RSP_OK:
            raise BridgeError(f"AXI4 write failed status={status} addr=0x{addr:x}")
        return bresp

    async def read(
        self,
        addr: int,
        *,
        size: int | None = None,
        burst_id: int = 0,
    ) -> tuple[int, int]:
        if size is None:
            size = self.data_bytes.bit_length() - 1
        status, data, rresp, *_ = await self.bridge.call(
            KVIPS_AXI4_READ, a0=addr, a2=size, a3=burst_id
        )
        if status != KVIPS_RSP_OK:
            raise BridgeError(f"AXI4 read failed status={status} addr=0x{addr:x}")
        return data, rresp

    async def write_burst(
        self,
        addr: int,
        beats: list[int],
        *,
        size: int | None = None,
        burst_id: int = 0,
        strb: int | None = None,
    ) -> int:
        if not 1 <= len(beats) <= 16:
            raise BridgeError("AXI4 write_burst supports 1..16 beats")
        if size is None:
            size = self.data_bytes.bit_length() - 1
        if strb is None:
            strb = (1 << self.data_bytes) - 1
        for i, d in enumerate(beats):
            await self.bridge.set_beat(i, d, strb)
        status, bresp, *_ = await self.bridge.call(
            KVIPS_AXI4_WRITE_BURST,
            a0=addr,
            a1=len(beats) - 1,
            a2=size,
            a3=burst_id,
            a4=strb,
        )
        if status != KVIPS_RSP_OK:
            raise BridgeError(f"AXI4 write_burst failed status={status}")
        return bresp

    async def read_burst(
        self,
        addr: int,
        num_beats: int,
        *,
        size: int | None = None,
        burst_id: int = 0,
    ) -> tuple[list[int], int]:
        if not 1 <= num_beats <= 16:
            raise BridgeError("AXI4 read_burst supports 1..16 beats")
        if size is None:
            size = self.data_bytes.bit_length() - 1
        status, rresp, *_ = await self.bridge.call(
            KVIPS_AXI4_READ_BURST,
            a0=addr,
            a1=num_beats - 1,
            a2=size,
            a3=burst_id,
        )
        if status != KVIPS_RSP_OK:
            raise BridgeError(f"AXI4 read_burst failed status={status}")
        data = [self.bridge.get_rsp_beat(i) for i in range(num_beats)]
        return data, rresp

    async def write_readback(self, addr: int, data: int) -> int:
        await self.write(addr, data)
        got, _ = await self.read(addr)
        return got

    async def run_sequence(self, name: str, **kwargs) -> None:
        name = name.lower().replace("-", "_")
        allow_inval = bool(kwargs.pop("allow_inval", False))

        if name in ("write_readback", "wrb", "smoke", "axi4_write_readback_seq"):
            op, a0, a1, a2 = (
                KVIPS_AXI4_SEQ_WRB,
                int(kwargs.get("num_txns", 16)),
                int(kwargs.get("base_addr", 0x1000)),
                int(kwargs.get("max_len", 3)),
            )
        elif name in ("write_burst", "axi4_write_burst_seq"):
            op, a0, a1, a2 = (
                KVIPS_AXI4_SEQ_WBRST,
                int(kwargs.get("num_txns", 8)),
                int(kwargs.get("start_addr", kwargs.get("base_addr", 0x2000))),
                int(kwargs.get("max_len", 3)),
            )
        elif name in ("read_burst", "axi4_read_burst_seq"):
            op, a0, a1, a2 = (
                KVIPS_AXI4_SEQ_RBRST,
                int(kwargs.get("num_txns", 8)),
                int(kwargs.get("start_addr", kwargs.get("base_addr", 0x2000))),
                int(kwargs.get("max_len", 3)),
            )
        elif name in ("stress", "pipelined_stress", "axi4_pipelined_stress_seq", "pipe_stress"):
            op, a0, a1, a2 = (
                KVIPS_AXI4_SEQ_STRESS if name != "pipe_stress" else KVIPS_AXI4_SEQ_PIPE_STRESS,
                int(kwargs.get("num_pairs", kwargs.get("num_txns", 16))),
                int(kwargs.get("base_addr", 0x1000)),
                int(kwargs.get("max_len", 3)),
            )
        elif name in ("lane", "lane_sweep", "axi4_lane_sweep_seq"):
            op, a0, a1, a2 = KVIPS_AXI4_SEQ_LANE, int(kwargs.get("base_addr", 0x2000)), 0, 0
        elif name in ("strobe", "strobe_patterns", "axi4_strobe_patterns_seq"):
            op, a0, a1, a2 = KVIPS_AXI4_SEQ_STROBE, int(kwargs.get("base_addr", 0x3000)), 0, 0
        elif name in ("concurrent", "concurrent_rw", "axi4_concurrent_rw_seq"):
            op, a0, a1, a2 = (
                KVIPS_AXI4_SEQ_CONCURRENT,
                int(kwargs.get("num_prefill", 8)),
                int(kwargs.get("num_mixed", 32)),
                int(kwargs.get("base_a", 0xA000)),
            )
        elif name in ("unaligned", "unaligned_byte", "axi4_unaligned_byte_seq"):
            op, a0, a1, a2 = KVIPS_AXI4_SEQ_UNALIGNED, int(kwargs.get("base_addr", 0x5000)), 0, 0
        elif name in ("corner", "corner_case", "axi4_corner_case_seq"):
            op, a0, a1, a2 = KVIPS_AXI4_SEQ_CORNER, int(kwargs.get("base_addr", 0xE000)), 0, 0
        elif name in ("incr256", "incr_256b", "axi4_incr_256b_seq"):
            op, a0, a1, a2 = (
                KVIPS_AXI4_SEQ_INCR256,
                int(kwargs.get("num_txns", 2)),
                int(kwargs.get("base_addr", 0x6000)),
                0,
            )
        elif name in ("phase_api", "axi4_phase_api_seq"):
            op, a0, a1, a2 = KVIPS_AXI4_SEQ_PHASE_API, int(kwargs.get("base_addr", 0xD000)), 0, 0
        elif name in ("wr_expect", "write_expect", "axi4_write_expect_resp_seq"):
            op, a0, a1, a2 = (
                KVIPS_AXI4_SEQ_WR_EXPECT,
                int(kwargs.get("addr", 0x0010_0000)),
                int(kwargs.get("expected_bresp", 3)),  # AXI4_RESP_DECERR = 2'b11
                0,
            )
        elif name in ("rd_expect", "read_expect", "axi4_read_expect_resp_seq"):
            op, a0, a1, a2 = (
                KVIPS_AXI4_SEQ_RD_EXPECT,
                int(kwargs.get("addr", 0x0010_0000)),
                int(kwargs.get("expected_rresp", 3)),  # AXI4_RESP_DECERR
                0,
            )
        elif name in ("same_id", "same_id_pipeline", "axi4_same_id_pipeline_seq"):
            op, a0, a1, a2 = (
                KVIPS_AXI4_SEQ_SAME_ID,
                int(kwargs.get("num_txns", 8)),
                int(kwargs.get("base_addr", 0x7000)),
                0,
            )
        elif name in ("sideband", "sideband_policy", "axi4_sideband_policy_seq"):
            op, a0, a1, a2 = KVIPS_AXI4_SEQ_SIDEBAND, int(kwargs.get("base_addr", 0x8000)), 0, 0
        elif name in ("exclusive_basic", "axi4_exclusive_basic_seq"):
            op, a0, a1, a2 = KVIPS_AXI4_SEQ_EXCL_BASIC, int(kwargs.get("addr", 0x2000)), 0, 0
        elif name in ("exclusive_fail", "axi4_exclusive_fail_seq"):
            op, a0, a1, a2 = KVIPS_AXI4_SEQ_EXCL_FAIL, int(kwargs.get("addr", 0x3000)), 0, 0
        elif name in ("exclusive_cross_id", "axi4_exclusive_cross_id_seq"):
            op, a0, a1, a2 = KVIPS_AXI4_SEQ_EXCL_XID, int(kwargs.get("addr", 0x3800)), 0, 0
        elif name in ("exclusive_illegal", "axi4_exclusive_illegal_seq"):
            op, a0, a1, a2 = KVIPS_AXI4_SEQ_EXCL_ILL, int(kwargs.get("addr", 0x7000)), 0, 0
        elif name in ("error_write", "axi4_error_write_seq"):
            op, a0, a1, a2 = KVIPS_AXI4_SEQ_ERR_WR, int(kwargs.get("addr", 0x0010_0000)), 0, 0
        elif name in ("error_read", "axi4_error_read_seq"):
            op, a0, a1, a2 = KVIPS_AXI4_SEQ_ERR_RD, int(kwargs.get("addr", 0x0010_0000)), 0, 0
        elif name in ("reset_recovery", "axi4_reset_recovery_seq"):
            op, a0, a1, a2 = KVIPS_AXI4_SEQ_RESET, 0, 0, 0
        elif name in ("nonpipelined_reset", "axi4_nonpipelined_reset_recovery_seq"):
            op, a0, a1, a2 = KVIPS_AXI4_SEQ_NP_RESET, 0, 0, 0
        elif name in ("timeout_recovery", "axi4_timeout_recovery_seq"):
            op, a0, a1, a2 = KVIPS_AXI4_SEQ_TIMEOUT, 0, 0, 0
        else:
            raise BridgeError(f"Unknown AXI4 sequence: {name}")

        status, *_ = await self.bridge.call(op, a0=a0, a1=a1, a2=a2)
        if status == KVIPS_RSP_INVAL and (allow_inval or name in _UNSUPPORTED_ON_RAM_DUT):
            return
        if status != KVIPS_RSP_OK:
            raise BridgeError(f"AXI4 sequence {name} failed status={status}")

    async def finish(self) -> None:
        await self.bridge.finish()
