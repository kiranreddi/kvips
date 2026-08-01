"""DPI monitor ring-buffer reader (ctypes into the linked sim)."""

from __future__ import annotations

import ctypes
import os
from dataclasses import dataclass
from typing import Optional


@dataclass
class MonitorEvent:
    proto: int
    write: bool
    addr: int
    data: int
    resp: int
    strb: int
    length: int
    txn_id: int


class _MonEvent(ctypes.Structure):
    _fields_ = [
        ("proto", ctypes.c_uint8),
        ("write", ctypes.c_uint8),
        ("pad0", ctypes.c_uint8),
        ("pad1", ctypes.c_uint8),
        ("resp", ctypes.c_uint32),
        ("strb", ctypes.c_uint32),
        ("len", ctypes.c_uint32),
        ("id", ctypes.c_uint32),
        ("addr", ctypes.c_uint64),
        ("data", ctypes.c_uint64),
    ]


class DpiMonitor:
    """Access kvips_dpi_* symbols from the running Verilator+cocotb process."""

    def __init__(self, lib_path: Optional[str] = None):
        self._lib = None
        self._load(lib_path)

    def _load(self, lib_path: Optional[str]) -> None:
        candidates = []
        if lib_path:
            candidates.append(lib_path)
        env = os.environ.get("KVIPS_DPI_LIB")
        if env:
            candidates.append(env)
        # cocotb/verilator typically leaves symbols in the main process
        candidates.extend(["", "libkvips_cocotb_dpi.so"])

        last_err = None
        for cand in candidates:
            try:
                if cand == "":
                    self._lib = ctypes.CDLL(None)  # current process
                else:
                    self._lib = ctypes.CDLL(cand)
                # Probe a required symbol
                self._lib.kvips_dpi_mon_pending.restype = ctypes.c_int
                break
            except OSError as exc:
                last_err = exc
                self._lib = None
        if self._lib is None:
            raise RuntimeError(f"Unable to load KVIPS DPI library: {last_err}")

        self._lib.kvips_dpi_mon_pop.argtypes = [ctypes.POINTER(_MonEvent)]
        self._lib.kvips_dpi_mon_pop.restype = ctypes.c_int
        self._lib.kvips_dpi_mon_pending.restype = ctypes.c_int
        self._lib.kvips_dpi_mon_total.restype = ctypes.c_uint64
        self._lib.kvips_dpi_reset.restype = None

    def reset(self) -> None:
        self._lib.kvips_dpi_reset()

    def pending(self) -> bool:
        return bool(self._lib.kvips_dpi_mon_pending())

    def total(self) -> int:
        return int(self._lib.kvips_dpi_mon_total())

    def pop(self) -> Optional[MonitorEvent]:
        ev = _MonEvent()
        if self._lib.kvips_dpi_mon_pop(ctypes.byref(ev)) == 0:
            return None
        return MonitorEvent(
            proto=int(ev.proto),
            write=bool(ev.write),
            addr=int(ev.addr),
            data=int(ev.data),
            resp=int(ev.resp),
            strb=int(ev.strb),
            length=int(ev.len),
            txn_id=int(ev.id),
        )

    def drain(self) -> list[MonitorEvent]:
        out: list[MonitorEvent] = []
        while True:
            ev = self.pop()
            if ev is None:
                break
            out.append(ev)
        return out
