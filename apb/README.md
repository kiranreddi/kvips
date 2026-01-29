## KVIPS APB (APB3/APB4) VIP

This directory provides an AMBA APB VIP supporting both APB3 and APB4 in a single compiled image, selectable at runtime.

### What’s included
- Master agent (driver + sequencer) and slave agent (responder + memory model)
- Passive monitor with functional coverage and optional transaction recording
- Interface-bound protocol assertions (SVA) with runtime enable/disable switches
- Example UVM back-to-back testbench and simulator scripts for Questa/VCS/Xcelium

### Protocol mode switch (APB3 vs APB4)
The interface always includes APB4 signals (`PPROT`, `PSTRB`). Mode is selected at runtime:
- `+APB_PROTOCOL=APB3`
- `+APB_PROTOCOL=APB4` (default)

In APB3 mode, the master forces APB3 semantics (`PSTRB='1`, `PPROT=0`) and APB4-only assertions are disabled.

### Directory structure
- `kvips/apb/sv/if/` – `apb_if.sv` (APB3/APB4 interface + clocking + assertions include)
- `kvips/apb/sv/assertions/` – `apb_if_sva.svh` (protocol checks, runtime switches)
- `kvips/apb/sv/pkg/` – `apb_types_pkg.sv`, `apb_uvm_pkg.sv`
- `kvips/apb/sv/uvm/` – UVM cfg/txn/sequencer/driver/monitor/scoreboard/sequences/env
- `kvips/apb/examples/uvm_back2back/` – self-contained demo env + tests

### Quick start (examples)
From `kvips/apb/examples/`:
- List tests: `make list-tests`
- Run Questa: `make questa TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB4'`
- Run VCS: `make vcs TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB4'`
- Run Xcelium: `make xcelium TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB4'`

If you need LSF to access tools, use `USE_LSF=1` and set `LSF_BSUB` for your site. On this environment:
- `source /tools/lsf/conf/profile.lsf`
- `make questa USE_LSF=1 ...`

### Documentation
See `kvips/apb/docs/` for:
- Integration guide
- Supported features
- Assertions and runtime switches
- Testplan mapping (APB3/APB4)

