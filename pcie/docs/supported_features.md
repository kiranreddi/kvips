# PCIe VIP Supported Features (Truth Table)

This VIP is **work in progress**. This document reflects what is actually present in `kvips/pcie` today.

Legend:
- ✅ Implemented (runnable/validated in the example)
- 🟡 Partial (present as scaffolding only)
- ❌ Planned / not implemented

## 1. Build/Tool Support

| Item | Status | Notes |
|------|--------|------|
| Questa `2025_3_2` compile/elab/run (B2B example) | ✅ | `pcie_b2b_smoke_test`, `pcie_b2b_mem_test` |
| VCS `2025.06_1` compile/elab/run (B2B example) | ✅ | Same |
| Xcelium `25.03.007` compile/elab/run (B2B example) | ✅ | Same |

## 2. Interfaces

| Item | Status | Notes |
|------|--------|------|
| PIPE interface `pcie_pipe_if` | ✅ | SV interface + modports + clocking blocks |
| Serial interface `pcie_serial_if` | 🟡 | SV interface exists; no full serial PHY model |

## 3. UVM Architecture

| Item | Status | Notes |
|------|--------|------|
| `pcie_cfg` | ✅ | Includes `enable_ltssm` default `0` |
| `pcie_transaction` | ✅ | Transaction container for draft TLP/DLLP/OS concepts |
| `pcie_sequencer` | 🟡 | Sequencer scaffold; no production sequence library yet |
| `pcie_driver` | 🟡 | Contains draft drive code; waits for `link_up` which is not achieved in the default example |
| `pcie_monitor` | 🟡 | Draft monitor/scaffold; limited/no meaningful traffic in default example |
| `pcie_scoreboard` | 🟡 | Skeleton checker; limited by lack of real traffic |
| `pcie_agent` | ✅ | Builds driver/monitor/scoreboard; used by the example |
| `pcie_env` wrapper | ❌ | Not present yet |

## 4. Protocol Features (Roadmap)

| Layer/Feature | Status | Notes |
|--------------|--------|------|
| LTSSM / link training | ❌ | Not functional; disabled by default |
| Ordered sets generation/detection | ❌ | Planned |
| Flow control credit model | ❌ | Planned |
| ACK/NAK + replay buffer | ❌ | Planned |
| Real TLP transmit/receive | ❌ | Planned (no end-to-end topology yet) |
| Completion tracking / timeouts | ❌ | Planned |
| Gen1–Gen6 compliance | ❌ | Enums/types exist; behavior not implemented |

## 5. Assertions (SVA)

| Item | Status | Notes |
|------|--------|------|
| PHY/DLL/TL assertion modules exist | 🟡 | Standalone modules under `kvips/pcie/sv/assertions` |
| Assertions integrated into example TB | ❌ | Not bound/instantiated yet |

## 6. Examples

| Example | Status | Notes |
|--------|--------|------|
| `examples/uvm_back2back` | ✅ | Bring-up; EP agent configured as monitor-only to avoid multi-driving a single interface instance |
