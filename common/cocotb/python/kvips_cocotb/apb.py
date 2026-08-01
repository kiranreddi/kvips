"""APB master facade — issues commands that UVM APB VIP executes."""

from __future__ import annotations

from .bridge import CocotbBridge, BridgeError
from .opcodes import (
    KVIPS_APB_WRITE,
    KVIPS_APB_READ,
    KVIPS_APB_SEQ_SMOKE,
    KVIPS_APB_SEQ_STRESS,
    KVIPS_APB_SEQ_STROBE,
    KVIPS_RSP_OK,
)


class ApbMaster:
    def __init__(self, dut, bridge_name: str = "bridge"):
        self.bridge = CocotbBridge(dut, bridge_name=bridge_name)

    async def wait_ready(self) -> None:
        await self.bridge.wait_ready()
        await self.bridge.ping()

    async def write(self, addr: int, data: int, strb: int = 0xF, prot: int = 0) -> None:
        status, *_ = await self.bridge.call(KVIPS_APB_WRITE, a0=addr, a1=data, a2=strb, a3=prot)
        if status != KVIPS_RSP_OK:
            raise BridgeError(f"APB write failed status={status} addr=0x{addr:x}")

    async def read(self, addr: int, prot: int = 0) -> int:
        status, data, *_ = await self.bridge.call(KVIPS_APB_READ, a0=addr, a3=prot)
        if status != KVIPS_RSP_OK:
            raise BridgeError(f"APB read failed status={status} addr=0x{addr:x}")
        return data & 0xFFFFFFFF

    async def write_readback(self, addr: int, data: int, strb: int = 0xF, prot: int = 0) -> int:
        await self.write(addr, data, strb=strb, prot=prot)
        return await self.read(addr, prot=prot)

    async def run_sequence(self, name: str, **kwargs) -> None:
        name = name.lower().replace("-", "_")
        if name in ("smoke", "smoke_rw", "apb_smoke_rw_seq"):
            num = int(kwargs.get("num_txns", 16))
            base = int(kwargs.get("base_addr", 0))
            status, *_ = await self.bridge.call(KVIPS_APB_SEQ_SMOKE, a0=num, a1=base)
        elif name in ("stress", "random_stress", "apb_random_stress_seq"):
            num = int(kwargs.get("num_txns", 64))
            base = int(kwargs.get("base_addr", 0x100))
            span = int(kwargs.get("span_bytes", 512))
            wr_pct = int(kwargs.get("wr_pct", 55))
            status, *_ = await self.bridge.call(
                KVIPS_APB_SEQ_STRESS, a0=num, a1=base, a2=span, a3=wr_pct
            )
        elif name in ("strobe", "apb4_strobe", "apb_apb4_strobe_mask_seq"):
            addr = int(kwargs.get("addr", 0x20))
            full = int(kwargs.get("full_data", 0xA5A55A5A))
            mask = int(kwargs.get("mask_data", 0x11223344))
            strb = int(kwargs.get("strb", 0x5))
            prot = int(kwargs.get("prot", 1))
            status, *_ = await self.bridge.call(
                KVIPS_APB_SEQ_STROBE, a0=addr, a1=full, a2=mask, a3=strb, a4=prot
            )
        else:
            raise BridgeError(f"Unknown APB sequence: {name}")
        if status != KVIPS_RSP_OK:
            raise BridgeError(f"APB sequence {name} failed status={status}")

    async def finish(self) -> None:
        await self.bridge.finish()
