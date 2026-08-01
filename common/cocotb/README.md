# KVIPS cocotb ↔ UVM bridge

Python (cocotb) drives the existing KVIPS UVM VIP agents/sequences through a
shared command/response bridge. Custom DPI is enabled for monitor events and
reliable response completion; Accellera UVM DPI stays off (`UVM_NO_DPI`) for
Verilator.

## Layout

| Path | Role |
|------|------|
| `sv/kvips_cocotb_bridge_if.sv` | Host↔UVM handshake IF (`public_flat_rw`) |
| `sv/kvips_cocotb_opcodes.svh` | Shared opcodes |
| `sv/kvips_cocotb_dpi.{c,h,pkg.sv}` | Monitor ring + response mailbox DPI |
| `python/kvips_cocotb/` | `ApbMaster` / `Axi4Master` / `AhbMaster` + `DpiMonitor` |

## Examples

- `apb/examples/cocotb_dut`
- `axi4/examples/cocotb_dut`
- `ahb/examples/cocotb_dut`

Each example reuses the protocol’s `uvm_dut` RAM slave and a bridge UVM test
that serves Python opcodes by starting the real VIP sequences/drivers.

## Run (Verilator)

```bash
# one-time
python3 -m venv .venv-cocotb
source .venv-cocotb/bin/activate
pip install 'cocotb==1.9.2'
# Verilator 5.048+ on PATH (CI builds the pinned release)

python3 scripts/run_cocotb_verilator.py --protocol apb   # or axi4 / ahb
```

DPI is linked automatically (`KVIPS_COCOTB_DPI`) with `-Wl,--export-dynamic` so
Python `ctypes` can resolve `kvips_dpi_*` symbols in-process.

## Sequence surface

Python `run_sequence(name, ...)` maps to VIP library sequences (or directed
stand-ins when the RAM DUT / non-pipelined master cannot host the library body).

| Protocol | OK on RAM DUT | Returns `RSP_INVAL` (needs VIP slave / reset / err policy) |
|----------|---------------|--------------------------------------------------------------|
| APB | smoke, stress, strobe | — |
| AXI4 | wrb, write/read_burst*, stress*, lane, strobe, concurrent*, unaligned, corner*, incr256*, phase_api, wr/rd_expect, same_id*, sideband*, err_wr/rd*, pipe_stress* | exclusive_*, reset_*, timeout |
| AHB | smoke, single, incr, wrap, b2b, wait, stress, busy, boundary (1KB-edge), endian, full_resp | security, error |

`*` = directed / non-pipe stand-in of the library class (same opcode, safe on this DUT).

## Notes

- Prefer directed / `$urandom` sequence paths under Verilator; full
  `randomize() with {}` needs an external solver.
- AHB sequence base addresses should be 1KB-aligned.
- Pass `allow_inval=True` (or use the unsupported-name lists) when probing
  opcodes that intentionally return `RSP_INVAL` on the RAM DUT.
