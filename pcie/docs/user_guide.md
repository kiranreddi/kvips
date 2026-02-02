# KVIPS PCIe VIP User Guide (Current Status)

This PCIe VIP is a **work in progress**. The current deliverable is a **buildable** (Questa/VCS/Xcelium) SV/UVM scaffold plus a runnable bring-up example.

If you are looking for the long-term plan/intent, see `kvips/pcie/docs/COMPREHENSIVE_PCIE_VIP_PLAN.md`.

## 1. What Is Implemented Today

**Implemented (builds and runs the example):**
- SV interfaces: `kvips/pcie/sv/if/pcie_pipe_if.sv`, `kvips/pcie/sv/if/pcie_serial_if.sv`
- UVM classes: `pcie_cfg`, `pcie_transaction`, `pcie_sequencer`, `pcie_driver`, `pcie_monitor`, `pcie_scoreboard`, `pcie_agent`
- Example TB: `kvips/pcie/examples/uvm_back2back`

**Not implemented yet (planned):**
- Full PCIe link training / LTSSM behavior (disabled by default)
- End-to-end PIPE/Serial link “wire model” (RC Tx → EP Rx and EP Tx → RC Rx)
- A real transaction sequence library that drives TLPs and checks completions
- Binding/instantiation of the SVA modules into the example TB
- Protocol-accurate PHY/DLL/TL modeling and compliance coverage

## 2. Directory Layout

```
kvips/pcie/
├── README.md
├── AGENTS.md
├── docs/
│   ├── COMPREHENSIVE_PCIE_VIP_PLAN.md
│   ├── integration_guide.md
│   ├── supported_features.md
│   ├── testplan.md
│   └── assertions.md
├── sv/
│   ├── if/
│   ├── pkg/
│   ├── uvm/
│   └── assertions/
└── examples/
    └── uvm_back2back/
```

## 3. UVM Components

The PCIe VIP currently ships an **agent-level** scaffold (there is no `pcie_env` wrapper yet).

- `pcie_cfg` (`kvips/pcie/sv/uvm/pcie_cfg.svh`)
  - Contains basic knobs for agent/interface mode and default “safe” values.
  - `enable_ltssm` exists; the example uses the default (`0`) to avoid background LTSSM threads.
- `pcie_agent` (`kvips/pcie/sv/uvm/pcie_agent.svh`)
  - Builds a driver/monitor/scoreboard around the configured interface mode.
- `pcie_driver` (`kvips/pcie/sv/uvm/pcie_driver.svh`)
  - Contains a draft implementation of “transaction driving”, but it currently waits for `link_up`.
  - With `enable_ltssm=0` (example default), no link-up occurs and no traffic is driven.

Agent mode enum (see `pcie_types_pkg`):
- `PCIE_RC`
- `PCIE_EP`
- `PCIE_MONITOR`

## 4. Running the Back-to-Back Example

From repo root:

- Questa: `kvips/pcie/examples/uvm_back2back/sim/run_questa.sh +UVM_TESTNAME=pcie_b2b_smoke_test`
- VCS: `kvips/pcie/examples/uvm_back2back/sim/run_vcs.sh +UVM_TESTNAME=pcie_b2b_smoke_test`
- Xcelium: `kvips/pcie/examples/uvm_back2back/sim/run_xcelium.sh +UVM_TESTNAME=pcie_b2b_smoke_test`

**Example limitations (important):**
- The example instantiates **one** PIPE interface. To avoid multiple drivers, it configures:
  - RC agent as active
  - EP agent as **monitor-only**
- The `pcie_b2b_mem_test` currently constructs a `pcie_transaction` but does not yet start a sequence to drive it.

## 5. Integration Notes

For integration patterns (how to wire vifs via `uvm_config_db`, recommended top-level wiring, and simulator notes), see `kvips/pcie/docs/integration_guide.md`.

## 6. Roadmap

The “product-grade” feature list, test plan, and planned architecture are tracked here:
- `kvips/pcie/docs/supported_features.md`
- `kvips/pcie/docs/testplan.md`
