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
- `kvips/apb/examples/uvm_dut/` – APB4 master driving a signal-level RTL RAM
  DUT with commercial-simulator regression scripts

### Quick start (examples)
From `kvips/apb/examples/`:
- List tests: `make list-tests`
- Run Questa: `make questa TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB4'`
- Run VCS: `make vcs TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB4'`
- Run Xcelium: `make xcelium TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB4'`

### APB4 RTL-DUT verification

The DUT flow is separate from the back-to-back demo and exercises a real
byte-addressed APB4 RAM responder, including `PSTRB`, `PPROT`, wait states,
boundary behavior, and unmapped `PSLVERR` responses.  The three commercial
regressions are evidence-gated on monitor handshakes, scoreboard mismatches,
and simulator/UVM errors:

```bash
make -C kvips/apb/examples regress-rtl-questa USE_LSF=1
make -C kvips/apb/examples regress-rtl-vcs USE_LSF=1
make -C kvips/apb/examples regress-rtl-xcelium USE_LSF=1
```

Use `RTL_TEST=apb_dut_smoke_test` with `rtl-questa`, `rtl-vcs`, or `rtl-xcelium`
for a single DUT test.  The **APB DUT CI** workflow runs the DUT Verilator
list (separate from **APB BK2BK CI**); Verilator remains CI-only on the
development workstation.

If you need LSF to access tools, use `USE_LSF=1` and set `LSF_BSUB` for your site. On this environment:
- `source /tools/lsf/conf/profile.lsf`
- `make questa USE_LSF=1 ...`

### Documentation
See `kvips/apb/docs/` for:
- Integration guide
- Supported features
- Assertions and runtime switches
- Testplan mapping (APB3/APB4)
- APB4 RTL-DUT verification milestone (`docs/dut_verification.md`)
