## KVIPS AHB (AHB-Lite/AHB Full) VIP

This directory provides an AMBA AHB VIP supporting both AHB-Lite and AHB Full in a single compiled image, selectable at runtime.

### What’s included
- Master agent (driver + sequencer) and slave agent (responder + memory/register model)
- Passive monitor with functional coverage and optional transaction recording
- Interface-bound protocol assertions (SVA) with runtime enable/disable switches
- Example UVM back-to-back and RTL-DUT testbenches with simulator scripts for Questa/VCS/Xcelium

### Protocol mode switch (AHB-Lite vs AHB Full)
Mode is selected at runtime:
- `+AHB_MODE=AHB_LITE` (default)
- `+AHB_MODE=AHB_FULL`

AHB-Lite mode restricts responses to OKAY/ERROR and assumes a single master (no arbitration). AHB Full mode enables the superset response encoding, including directed RETRY/SPLIT responses, while the reference example remains a single-master/single-slave bus model.

### Directory structure
- `kvips/ahb/sv/if/` – `ahb_if.sv` (AHB interface + clocking + assertions include)
- `kvips/ahb/sv/assertions/` – `ahb_if_sva.svh` (protocol checks, runtime switches)
- `kvips/ahb/sv/pkg/` – `ahb_types_pkg.sv`, `ahb_uvm_pkg.sv`
- `kvips/ahb/sv/uvm/` – UVM cfg/txn/sequencer/driver/monitor/scoreboard/sequences/env
- `kvips/ahb/examples/uvm_back2back/` – self-contained demo env + tests
- `kvips/ahb/examples/uvm_dut/` – KVIPS master driving a synthesizable AHB RAM DUT

### Quick start (examples)
From `kvips/ahb/examples/`:
- List tests: `make list-tests`
- Run Questa: `make questa TEST=ahb_smoke_test`
- Run VCS: `make vcs TEST=ahb_smoke_test`
- Run Xcelium: `make xcelium TEST=ahb_smoke_test`
- Run the complete Questa regression: `make regress-questa`
- Run the complete VCS regression: `make regress-vcs`
- Run the complete Xcelium regression: `make regress-xcelium`

### RTL-DUT verification

The `uvm_dut` example is an executable signal-level integration milestone. It
drives a reset-initialized, byte-lane-aware RAM responder and checks real AHB
handshakes through the monitor, logger, and scoreboard. Six tests cover smoke,
incrementing and wrapping bursts, fixed wait states, back-to-back stress, and
the `AHB_FULL` mode. Commercial regressions are evidence-gated on nonzero
read/write traffic, zero responder errors, zero scoreboard mismatches, and
wait-state evidence where expected:

```bash
make regress-rtl-questa USE_LSF=1
make regress-rtl-vcs USE_LSF=1
make regress-rtl-xcelium USE_LSF=1
make rtl-questa RTL_TEST=ahb_dut_full_mode_test PLUSARGS='+AHB_MODE=AHB_FULL'
```

The Verilator DUT regression runs in CI for portable compile/smoke coverage;
it does not replace the commercial simulator evidence. See
[`docs/dut_verification.md`](docs/dut_verification.md) for the topology,
acceptance criteria, and known integration boundaries.

If you need LSF to access tools, use `USE_LSF=1` and set `LSF_BSUB` for your site.

### Documentation
See `kvips/ahb/docs/` for:
- Integration guide
- RTL-DUT verification guide
- Supported features
- Assertions and runtime switches
- Testplan mapping

### Status / pending
- Implemented: single-bus AHB-Lite/Full master+slave VIP with legal burst generation, BUSY insertion, wait states, error injection, directed RETRY/SPLIT response encoding, HNONSEC transport and policy callbacks, configurable endian mapping, strict legality checks, monitor coverage, beat-accurate scoreboard checking, reset recovery, back-to-back examples, and a six-test RTL-DUT RAM integration gate.
- Pending: multi-master arbitration/HMASTER scheduling, HSPLIT routing and multi-slave interconnect decode, negative-DUT SVA harnesses, and full transaction-recording integration. See `kvips/ahb/docs/supported_features.md` and `kvips/ahb/docs/amba_spec_coverage.md`.
