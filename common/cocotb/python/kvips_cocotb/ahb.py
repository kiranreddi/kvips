"""AHB master facade — issues commands that UVM AHB VIP executes."""

from __future__ import annotations

from .bridge import CocotbBridge, BridgeError
from .opcodes import (
    KVIPS_AHB_WRITE,
    KVIPS_AHB_READ,
    KVIPS_AHB_SEQ_SMOKE,
    KVIPS_AHB_SEQ_SINGLE,
    KVIPS_AHB_SEQ_INCR,
    KVIPS_AHB_SEQ_WRAP,
    KVIPS_AHB_SEQ_B2B,
    KVIPS_AHB_SEQ_WAIT,
    KVIPS_AHB_SEQ_STRESS,
    KVIPS_AHB_SEQ_BUSY,
    KVIPS_AHB_SEQ_BOUNDARY,
    KVIPS_RSP_OK,
)

# AHB size encoding (HSIZE)
AHB_SIZE_8 = 0
AHB_SIZE_16 = 1
AHB_SIZE_32 = 2
AHB_SIZE_64 = 3

# AHB burst encoding
AHB_SINGLE = 0
AHB_INCR = 1
AHB_WRAP4 = 2
AHB_INCR4 = 3
AHB_WRAP8 = 4
AHB_INCR8 = 5
AHB_WRAP16 = 6
AHB_INCR16 = 7


class AhbMaster:
    def __init__(self, dut, bridge_name: str = "bridge"):
        self.bridge = CocotbBridge(dut, bridge_name=bridge_name)

    async def wait_ready(self) -> None:
        await self.bridge.wait_ready()
        await self.bridge.ping()

    async def write(
        self,
        addr: int,
        data: int,
        *,
        size: int = AHB_SIZE_32,
        burst: int = AHB_SINGLE,
        prot: int = 0,
        nonsec: int = 0,
    ) -> int:
        """Single transfer write (or first beat data for simple SINGLE). Returns resp."""
        status, resp, *_ = await self.bridge.call(
            KVIPS_AHB_WRITE,
            a0=addr,
            a1=data,
            a2=size,
            a3=burst,
            a4=prot,
            a5=nonsec,
        )
        if status != KVIPS_RSP_OK:
            raise BridgeError(f"AHB write failed status={status} addr=0x{addr:x}")
        return resp

    async def read(
        self,
        addr: int,
        *,
        size: int = AHB_SIZE_32,
        burst: int = AHB_SINGLE,
        prot: int = 0,
        nonsec: int = 0,
    ) -> tuple[int, int]:
        status, data, resp, *_ = await self.bridge.call(
            KVIPS_AHB_READ,
            a0=addr,
            a2=size,
            a3=burst,
            a4=prot,
            a5=nonsec,
        )
        if status != KVIPS_RSP_OK:
            raise BridgeError(f"AHB read failed status={status} addr=0x{addr:x}")
        return data & 0xFFFFFFFF, resp

    async def write_readback(self, addr: int, data: int) -> int:
        await self.write(addr, data)
        got, _ = await self.read(addr)
        return got

    async def run_sequence(self, name: str, **kwargs) -> None:
        name = name.lower().replace("-", "_")
        mapping = {
            "smoke": KVIPS_AHB_SEQ_SMOKE,
            "ahb_smoke_seq": KVIPS_AHB_SEQ_SMOKE,
            "single": KVIPS_AHB_SEQ_SINGLE,
            "single_rw": KVIPS_AHB_SEQ_SINGLE,
            "ahb_single_rw_seq": KVIPS_AHB_SEQ_SINGLE,
            "incr": KVIPS_AHB_SEQ_INCR,
            "incr_burst": KVIPS_AHB_SEQ_INCR,
            "ahb_incr_burst_seq": KVIPS_AHB_SEQ_INCR,
            "wrap": KVIPS_AHB_SEQ_WRAP,
            "wrap_burst": KVIPS_AHB_SEQ_WRAP,
            "ahb_wrap_burst_seq": KVIPS_AHB_SEQ_WRAP,
            "b2b": KVIPS_AHB_SEQ_B2B,
            "back_to_back": KVIPS_AHB_SEQ_B2B,
            "ahb_back_to_back_seq": KVIPS_AHB_SEQ_B2B,
            "wait": KVIPS_AHB_SEQ_WAIT,
            "wait_state": KVIPS_AHB_SEQ_WAIT,
            "ahb_wait_state_seq": KVIPS_AHB_SEQ_WAIT,
            "stress": KVIPS_AHB_SEQ_STRESS,
            "random_stress": KVIPS_AHB_SEQ_STRESS,
            "ahb_random_stress_seq": KVIPS_AHB_SEQ_STRESS,
            "busy": KVIPS_AHB_SEQ_BUSY,
            "ahb_busy_seq": KVIPS_AHB_SEQ_BUSY,
            "boundary": KVIPS_AHB_SEQ_BOUNDARY,
            "ahb_boundary_seq": KVIPS_AHB_SEQ_BOUNDARY,
        }
        if name not in mapping:
            raise BridgeError(f"Unknown AHB sequence: {name}")
        num = int(kwargs.get("num_txns", 16))
        base = int(kwargs.get("base_addr", 0))
        wr_pct = int(kwargs.get("wr_pct", 50))
        status, *_ = await self.bridge.call(mapping[name], a0=num, a1=base, a2=wr_pct)
        if status != KVIPS_RSP_OK:
            raise BridgeError(f"AHB sequence {name} failed status={status}")

    async def finish(self) -> None:
        await self.bridge.finish()
