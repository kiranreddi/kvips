"""Low-level cocotb driver for kvips_cocotb_bridge_if."""

from __future__ import annotations

import ctypes
import os
from typing import Optional

import cocotb
from cocotb.triggers import RisingEdge, ClockCycles

from .opcodes import KVIPS_RSP_OK, KVIPS_OP_PING, KVIPS_OP_FINISH, KVIPS_OP_GET_STATS


class BridgeError(RuntimeError):
    pass


class _DpiRsp(ctypes.Structure):
    _fields_ = [
        ("status", ctypes.c_uint32),
        ("pad", ctypes.c_uint32),
        ("d0", ctypes.c_uint64),
        ("d1", ctypes.c_uint64),
        ("d2", ctypes.c_uint64),
        ("d3", ctypes.c_uint64),
    ]


class _DpiRspMailbox:
    """ctypes access to kvips_dpi_rsp_* symbols in the running sim."""

    def __init__(self) -> None:
        self._lib = None
        last_err: Optional[BaseException] = None
        for cand in ("", os.environ.get("KVIPS_DPI_LIB", "")):
            if cand is None:
                continue
            try:
                self._lib = ctypes.CDLL(cand) if cand else ctypes.CDLL(None)
                self._lib.kvips_dpi_rsp_pending.restype = ctypes.c_int
                self._lib.kvips_dpi_rsp_pop.argtypes = [ctypes.POINTER(_DpiRsp)]
                self._lib.kvips_dpi_rsp_pop.restype = ctypes.c_int
                break
            except (OSError, AttributeError) as exc:
                last_err = exc
                self._lib = None
        if self._lib is None:
            raise BridgeError(f"Unable to bind DPI response mailbox: {last_err}")

    def pending(self) -> bool:
        return bool(self._lib.kvips_dpi_rsp_pending())

    def pop(self) -> Optional[tuple[int, int, int, int, int]]:
        ev = _DpiRsp()
        if self._lib.kvips_dpi_rsp_pop(ctypes.byref(ev)) == 0:
            return None
        return int(ev.status), int(ev.d0), int(ev.d1), int(ev.d2), int(ev.d3)

    def drain(self) -> None:
        while self.pop() is not None:
            pass


class CocotbBridge:
    def __init__(
        self,
        dut,
        bridge_name: str = "bridge",
        clk_name: str | None = None,
        rst_name: str | None = None,
    ):
        self.dut = dut
        self.bridge = getattr(dut, bridge_name)
        # Interface port handles are not always visible under the IF instance in
        # Verilator+cocotb; use top-level clock/reset instead.
        if clk_name is not None:
            self.clk = getattr(dut, clk_name)
        else:
            for cand in ("PCLK", "HCLK", "aclk", "clk"):
                if hasattr(dut, cand):
                    self.clk = getattr(dut, cand)
                    break
            else:
                raise BridgeError("Could not find top-level clock on dut")
        if rst_name is not None:
            self.rst_n = getattr(dut, rst_name)
        else:
            for cand in ("PRESETn", "HRESETn", "areset_n", "rst_n"):
                if hasattr(dut, cand):
                    self.rst_n = getattr(dut, cand)
                    break
            else:
                self.rst_n = None
        self._dpi_rsp = _DpiRspMailbox()
        self._init_host_outputs()

    def _init_host_outputs(self) -> None:
        self.bridge.req_valid.value = 0
        self.bridge.req_opcode.value = 0
        for name in ("req_a0", "req_a1", "req_a2", "req_a3", "req_a4", "req_a5", "req_a6", "req_a7"):
            getattr(self.bridge, name).value = 0
        self.bridge.rsp_ready.value = 1
        self.bridge.mon_ready.value = 1
        self._dpi_rsp.drain()

    async def wait_ready(self, timeout_cycles: int = 20000) -> None:
        for _ in range(timeout_cycles):
            await RisingEdge(self.clk)
            if self.rst_n is not None and int(self.rst_n.value) == 0:
                continue
            try:
                ready = int(self.bridge.bridge_ready.value)
            except ValueError:
                # Still 'x'/'z' during early time
                continue
            if ready == 1:
                return
        raise BridgeError("Timed out waiting for UVM bridge_ready")

    async def call(
        self,
        opcode: int,
        a0: int = 0,
        a1: int = 0,
        a2: int = 0,
        a3: int = 0,
        a4: int = 0,
        a5: int = 0,
        a6: int = 0,
        a7: int = 0,
        timeout_cycles: int = 10_000_000,
    ) -> tuple[int, int, int, int, int]:
        """Issue one command and wait for response. Returns (status, d0, d1, d2, d3)."""
        self.bridge.rsp_ready.value = 1
        self._dpi_rsp.drain()
        await RisingEdge(self.clk)
        self.bridge.req_opcode.value = opcode
        self.bridge.req_a0.value = a0
        self.bridge.req_a1.value = a1
        self.bridge.req_a2.value = a2
        self.bridge.req_a3.value = a3
        self.bridge.req_a4.value = a4
        self.bridge.req_a5.value = a5
        self.bridge.req_a6.value = a6
        self.bridge.req_a7.value = a7
        self.bridge.req_valid.value = 1

        # Wait for ready handshake (keep args stable until accepted)
        for _ in range(timeout_cycles):
            await RisingEdge(self.clk)
            if int(self.bridge.req_ready.value) == 1:
                break
        else:
            self.bridge.req_valid.value = 0
            raise BridgeError(f"Timed out waiting req_ready for opcode=0x{opcode:02x}")

        self.bridge.req_valid.value = 0

        # Prefer DPI mailbox (reliable across long UVM sequences); also accept
        # the IF rsp_valid pulse when VPI sampling catches it.
        for _ in range(timeout_cycles):
            await RisingEdge(self.clk)
            dpi = self._dpi_rsp.pop()
            if dpi is not None:
                return dpi
            try:
                rsp_v = int(self.bridge.rsp_valid.value)
            except ValueError:
                continue
            if rsp_v == 1:
                status = int(self.bridge.rsp_status.value)
                d0 = int(self.bridge.rsp_d0.value)
                d1 = int(self.bridge.rsp_d1.value)
                d2 = int(self.bridge.rsp_d2.value)
                d3 = int(self.bridge.rsp_d3.value)
                self._dpi_rsp.drain()
                await RisingEdge(self.clk)
                return status, d0, d1, d2, d3
        raise BridgeError(f"Timed out waiting rsp_valid for opcode=0x{opcode:02x}")

    async def set_beat(self, index: int, data: int, strb: int = 0xFF) -> None:
        if not 0 <= index < 16:
            raise BridgeError(f"beat index out of range: {index}")
        self.bridge.beat_data[index].value = data
        self.bridge.beat_strb[index].value = strb
        await RisingEdge(self.clk)

    def get_rsp_beat(self, index: int) -> int:
        return int(self.bridge.rsp_beat[index].value)

    async def ping(self) -> None:
        status, d0, *_ = await self.call(KVIPS_OP_PING)
        if status != KVIPS_RSP_OK or d0 != 0x4B564950:  # 'KVIP'
            raise BridgeError(f"PING failed status={status} d0=0x{d0:x}")

    async def get_stats(self) -> tuple[int, int, int, int]:
        status, d0, d1, d2, d3 = await self.call(KVIPS_OP_GET_STATS)
        if status != KVIPS_RSP_OK:
            raise BridgeError(f"GET_STATS failed status={status}")
        return d0, d1, d2, d3

    async def finish(self) -> None:
        status, *_ = await self.call(KVIPS_OP_FINISH)
        if status != KVIPS_RSP_OK:
            raise BridgeError(f"FINISH failed status={status}")
        await ClockCycles(self.clk, 10)

    async def poll_mon_if(self) -> dict | None:
        """Non-blocking sample of monitor IF (signal path, complements DPI)."""
        await RisingEdge(self.clk)
        if int(self.bridge.mon_valid.value) == 0:
            return None
        ev = {
            "proto": int(self.bridge.mon_proto.value),
            "write": bool(int(self.bridge.mon_write.value)),
            "addr": int(self.bridge.mon_addr.value),
            "data": int(self.bridge.mon_data.value),
            "resp": int(self.bridge.mon_resp.value),
            "strb": int(self.bridge.mon_strb.value),
            "len": int(self.bridge.mon_len.value),
            "id": int(self.bridge.mon_id.value),
        }
        return ev
