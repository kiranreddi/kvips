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

## Notes

- Prefer directed / `$urandom` sequence paths under Verilator; full
  `randomize() with {}` needs an external solver.
- AHB sequence base addresses should be 1KB-aligned.
- `ahb_boundary_seq` is a negative legality check and is not run against the RAM DUT.
