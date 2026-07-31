# KVIPS AHB example — UVM back-to-back

This is a self-contained example testbench for the KVIPS AHB VIP.

## Quick start

From `kvips/ahb/examples/`:

- List tests: `make list-tests`
- Run (Questa): `make questa TEST=ahb_smoke_test SEED=1`
- Run (VCS): `make vcs TEST=ahb_smoke_test SEED=1`
- Run (Xcelium): `make xcelium TEST=ahb_smoke_test SEED=1`
- Run (Verilator): `make verilator TEST=ahb_smoke_test`
- Run complete Questa/VCS/Xcelium lists: `make regress-questa`, `make regress-vcs`, or `make regress-xcelium`

## Protocol mode

Select mode at runtime:
- `+AHB_MODE=AHB_LITE` (default)
- `+AHB_MODE=AHB_FULL`

The Full RETRY/SPLIT tests add `+AHB_MODE=AHB_FULL` automatically in the
regression scripts. BUSY and reset recovery are covered by
`ahb_busy_test` and `ahb_reset_recovery_test`.

## Notes

- This example instantiates one master agent and one slave agent on a single `ahb_if`.
- Data integrity is checked with a lightweight scoreboard (monitor-based reference model).

## Verilator regression

From `kvips/ahb/examples/`:

- `make regress-verilator`
