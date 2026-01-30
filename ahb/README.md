## KVIPS AHB (AHB-Lite/AHB Full) VIP

This directory provides an AMBA AHB VIP supporting both AHB-Lite and AHB Full in a single compiled image, selectable at runtime.

### What’s included
- Master agent (driver + sequencer) and slave agent (responder + memory/register model)
- Passive monitor with functional coverage and optional transaction recording
- Interface-bound protocol assertions (SVA) with runtime enable/disable switches
- Example UVM back-to-back testbench and simulator scripts for Questa/VCS/Xcelium

### Protocol mode switch (AHB-Lite vs AHB Full)
Mode is selected at runtime:
- `+AHB_MODE=AHB_LITE` (default)
- `+AHB_MODE=AHB_FULL`

AHB-Lite mode restricts responses to OKAY/ERROR and assumes a single master (no arbitration). AHB Full mode enables optional signals and (optionally) extended responses; the reference implementation currently focuses on OKAY/ERROR for both modes.

### Directory structure
- `kvips/ahb/sv/if/` – `ahb_if.sv` (AHB interface + clocking + assertions include)
- `kvips/ahb/sv/assertions/` – `ahb_if_sva.svh` (protocol checks, runtime switches)
- `kvips/ahb/sv/pkg/` – `ahb_types_pkg.sv`, `ahb_uvm_pkg.sv`
- `kvips/ahb/sv/uvm/` – UVM cfg/txn/sequencer/driver/monitor/scoreboard/sequences/env
- `kvips/ahb/examples/uvm_back2back/` – self-contained demo env + tests

### Quick start (examples)
From `kvips/ahb/examples/`:
- List tests: `make list-tests`
- Run Questa: `make questa TEST=ahb_smoke_test`
- Run VCS: `make vcs TEST=ahb_smoke_test`
- Run Xcelium: `make xcelium TEST=ahb_smoke_test`

If you need LSF to access tools, use `USE_LSF=1` and set `LSF_BSUB` for your site.

### Documentation
See `kvips/ahb/docs/` for:
- Integration guide
- Supported features
- Assertions and runtime switches
- Testplan mapping

### Status / pending
- Implemented: single-bus AHB-Lite style master+slave VIP with bursts, stalls, error injection, monitor coverage, scoreboard, and a back-to-back example.
- Pending: AHB Full multi-master semantics (arbitration), RETRY/SPLIT support, BUSY insertion, stricter burst legality assertions, and richer transaction recording. See `kvips/ahb/docs/supported_features.md`.
