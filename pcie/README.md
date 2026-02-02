# KVIPS PCIe VIP (UVM + SVA) — Work In Progress

This is an early-stage PCIe VIP scaffold intended to grow into a full-featured VIP over time.

Today it provides:
- SystemVerilog **PIPE** and **Serial** interface definitions (`pcie_pipe_if`, `pcie_serial_if`)
- A buildable UVM skeleton: `pcie_cfg`, `pcie_transaction`, `pcie_sequencer`, `pcie_driver`, `pcie_monitor`, `pcie_scoreboard`, `pcie_agent`
- A runnable back-to-back (B2B) example that is validated to **compile/elaborate/run** on Questa/VCS/Xcelium
- Placeholder SVA modules for PHY/DLL/TL (not yet integrated/bound into the example TB)

It does **not** yet implement a complete PCIe stack (LTSSM/DLL/TL behavior, real TLP/DLLP exchange, credit model, replay, etc.). The default example tests are “bring-up” style and currently do not generate end-to-end PCIe traffic.

Designed for IEEE 1800 SystemVerilog + Accellera UVM.

## Protocol coverage status
- PCIe generation/width enums exist up to Gen6/x32 in `pcie_types_pkg`, but functional “Gen1–Gen6 compliance” is **not implemented/validated** yet.

## Supported simulators (validated versions)
- Siemens Questa: `2025_3_2`
- Synopsys VCS: `2025.06_1`
- Cadence Xcelium: `25.03.007`

## Quick start (back-to-back demo)
See `kvips/pcie/examples/uvm_back2back/README.md`.

Common single-test usage (from repo root):
- Questa: `kvips/pcie/examples/uvm_back2back/sim/run_questa.sh +UVM_TESTNAME=pcie_b2b_smoke_test`
- VCS: `kvips/pcie/examples/uvm_back2back/sim/run_vcs.sh +UVM_TESTNAME=pcie_b2b_smoke_test`
- Xcelium: `kvips/pcie/examples/uvm_back2back/sim/run_xcelium.sh +UVM_TESTNAME=pcie_b2b_smoke_test`

## Repository layout
- `kvips/pcie/sv/if/` : Interface definitions (PIPE, Serial)
- `kvips/pcie/sv/pkg/` : `pcie_types_pkg`, `pcie_uvm_pkg`
- `kvips/pcie/sv/uvm/` : Agent, drivers, monitor, scoreboard, sequences
- `kvips/pcie/sv/assertions/` : Protocol assertions (all layers)
- `kvips/pcie/examples/` : Runnable demos (Questa/VCS/Xcelium scripts)
- `kvips/pcie/docs/` : User guide, testplan, assertions, supported features

## Current limitations (important)
- The example does not bring up a real link (LTSSM is disabled by default via `pcie_cfg.enable_ltssm=0`).
- The example “memory test” currently only constructs a `pcie_transaction` object; it does not yet drive a TLP through a modeled link.
- Assertions exist as standalone SVA modules but are not bound/instantiated in the example TB yet.

## Debug knobs
Plusargs (demo-friendly):
- `+VIP_TRACE` : Verbose driver/monitor prints (UVM_INFO)
- `+VIP_TR` : UVM transaction recording hooks from monitor
- `+VIP_STATS` : Enable monitor stats summary
- `+PCIE_GEN=<1-6>` : Set target link speed
- `+PCIE_LANES=<1-32>` : Set link width

Assertions:
- Disable all: `+KVIPS_PCIE_ASSERT_OFF`
- Disable PHY layer: `+KVIPS_PCIE_ASSERT_PHY_OFF`
- Disable DLL layer: `+KVIPS_PCIE_ASSERT_DLL_OFF`
- Disable TL layer: `+KVIPS_PCIE_ASSERT_TL_OFF`

Scoreboard:
- Disable: `+KVIPS_PCIE_SB_OFF`

## Documentation
- `kvips/pcie/docs/user_guide.md`
- `kvips/pcie/docs/integration_guide.md`
- `kvips/pcie/docs/supported_features.md`
- `kvips/pcie/docs/testplan.md`
- `kvips/pcie/docs/assertions.md`

## LSF Access for /tools/ path
```bash
# Source LSF environment
source /tools/lsf/conf/profile.lsf

# Use bsub for simulator access
bsub -Ip -app gnrc -P boxsteru4 -Lp boxsteru4 -q interactive <command>
```
