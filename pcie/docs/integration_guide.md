# PCIe VIP Integration Guide (Current Implementation)

This guide documents the integration patterns that exist **today** for `kvips/pcie`. It intentionally avoids describing unimplemented PCIe protocol features as if they are available.

## 1. What You Can Integrate Today

- A PIPE or Serial **interface definition** in your TB.
- A UVM **agent-level** scaffold (`pcie_agent`) that can be configured for:
  - `PCIE_RC`, `PCIE_EP`, or `PCIE_MONITOR`
  - `PCIE_PIPE_MODE` or `PCIE_SERIAL_MODE`
- A runnable example that demonstrates config_db wiring and cross-simulator scripts:
  - `kvips/pcie/examples/uvm_back2back`

## 2. Directory Structure (Actual)

```
kvips/pcie/
├── sv/
│   ├── if/
│   │   ├── pcie_pipe_if.sv
│   │   └── pcie_serial_if.sv
│   ├── pkg/
│   │   ├── pcie_types_pkg.sv
│   │   └── pcie_uvm_pkg.sv
│   ├── uvm/
│   │   ├── pcie_cfg.svh
│   │   ├── pcie_transaction.svh
│   │   ├── pcie_sequencer.svh
│   │   ├── pcie_driver.svh
│   │   ├── pcie_monitor.svh
│   │   ├── pcie_scoreboard.svh
│   │   └── pcie_agent.svh
│   └── assertions/
│       ├── pcie_phy_assertions.sv
│       ├── pcie_dll_assertions.sv
│       └── pcie_tl_assertions.sv
└── examples/
    └── uvm_back2back/
        ├── tb/
        │   ├── top.sv
        │   └── tb_pkg.sv
        └── sim/
            ├── filelist.f
            ├── run_questa.sh
            ├── run_vcs.sh
            └── run_xcelium.sh
```

## 3. Minimal PIPE Integration (Recommended Starting Point)

In your TB top (pattern used by the example `kvips/pcie/examples/uvm_back2back/tb/top.sv`):

- Instantiate `pcie_pipe_if`.
- Push vifs into the UVM config DB:
  - whole interface for tests (`key: vif`)
  - `.mac` modport for the driver (`key: vif_pipe`)
  - `.monitor` modport for the monitor (`key: vif_pipe`)

The example demonstrates all of this wiring.

## 4. Simulator Notes (This Site)

On this environment, Questa/VCS/Xcelium binaries are typically accessible via `module load …`.
If tools are not accessible directly, use LSF interactive jobs:

```bash
source /tools/lsf/conf/profile.lsf
bsub -Ip -app gnrc -P boxsteru4 -Lp boxsteru4 -q interactive bash
```

Then run the example scripts from inside that session.

## 5. Known Gaps / Next Work

- There is no “link model” connecting RC and EP endpoints yet (a back-to-back topology requires at least two endpoints and a wire model).
- Assertions are not currently bound/instantiated by the example.
- The example tests are bring-up only; they do not yet drive real PCIe traffic.
