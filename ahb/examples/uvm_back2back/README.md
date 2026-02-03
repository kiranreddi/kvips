# KVIPS AHB example — UVM back-to-back

This is a self-contained example testbench for the KVIPS AHB VIP.

## Quick start

From `kvips/ahb/examples/`:

- List tests: `make list-tests`
- Run (Questa): `make questa TEST=ahb_smoke_test SEED=1`
- Run (VCS): `make vcs TEST=ahb_smoke_test SEED=1`
- Run (Xcelium): `make xcelium TEST=ahb_smoke_test SEED=1`
- Run (Verilator): `make verilator TEST=ahb_smoke_test`

## Protocol mode

Select mode at runtime:
- `+AHB_MODE=AHB_LITE` (default)
- `+AHB_MODE=AHB_FULL`

## Notes

- This example instantiates one master agent and one slave agent on a single `ahb_if`.
- Data integrity is checked with a lightweight scoreboard (monitor-based reference model).

## Verilator regression

From `kvips/ahb/examples/`:

- `make regress-verilator`

