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
    KVIPS_RSP_OK,
)


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
        """Single-beat write. Returns bresp."""
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
        """Single-beat read. Returns (data, rresp)."""
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
            a1=len(beats) - 1,  # awlen
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
        if name in ("write_readback", "wrb", "smoke", "axi4_write_readback_seq"):
            op = KVIPS_AXI4_SEQ_WRB
            a0 = int(kwargs.get("num_txns", 16))
            a1 = int(kwargs.get("base_addr", 0x1000))
            a2 = int(kwargs.get("max_len", 3))
        elif name in ("write_burst", "axi4_write_burst_seq"):
            op = KVIPS_AXI4_SEQ_WBRST
            a0 = int(kwargs.get("num_txns", 8))
            a1 = int(kwargs.get("start_addr", 0x2000))
            a2 = int(kwargs.get("max_len", 3))
        elif name in ("read_burst", "axi4_read_burst_seq"):
            op = KVIPS_AXI4_SEQ_RBRST
            a0 = int(kwargs.get("num_txns", 8))
            a1 = int(kwargs.get("start_addr", 0x2000))
            a2 = int(kwargs.get("max_len", 3))
        elif name in ("stress", "pipelined_stress", "axi4_pipelined_stress_seq"):
            op = KVIPS_AXI4_SEQ_STRESS
            a0 = int(kwargs.get("num_pairs", 16))
            a1 = int(kwargs.get("base_addr", 0x1000))
            a2 = int(kwargs.get("max_len", 3))
        elif name in ("lane", "lane_sweep", "axi4_lane_sweep_seq"):
            op = KVIPS_AXI4_SEQ_LANE
            a0 = int(kwargs.get("base_addr", 0x2000))
            a1 = 0
            a2 = 0
        elif name in ("strobe", "strobe_patterns", "axi4_strobe_patterns_seq"):
            op = KVIPS_AXI4_SEQ_STROBE
            a0 = int(kwargs.get("base_addr", 0x3000))
            a1 = 0
            a2 = 0
        elif name in ("concurrent", "concurrent_rw", "axi4_concurrent_rw_seq"):
            op = KVIPS_AXI4_SEQ_CONCURRENT
            a0 = int(kwargs.get("num_prefill", 8))
            a1 = int(kwargs.get("num_mixed", 32))
            a2 = int(kwargs.get("base_a", 0xA000))
        else:
            raise BridgeError(f"Unknown AXI4 sequence: {name}")
        status, *_ = await self.bridge.call(op, a0=a0, a1=a1, a2=a2)
        if status != KVIPS_RSP_OK:
            raise BridgeError(f"AXI4 sequence {name} failed status={status}")

    async def finish(self) -> None:
        await self.bridge.finish()
