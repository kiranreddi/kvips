# KVIPS PCIe VIP User Guide

## 1. Introduction

The KVIPS PCIe VIP is a complete UVM-based verification IP for PCI Express Gen1 through Gen6. It supports both Root Complex (RC) and Endpoint (EP) modes, with PIPE and Serial interface options.

### 1.1 Key Features

- **Multi-Generation**: Gen1 (2.5GT/s) to Gen6 (64GT/s)
- **Multi-Width**: x1 to x32 lane configurations
- **Dual Interface**: PIPE (PHY-MAC boundary) and Serial (full PHY)
- **UVM Architecture**: Standard UVM 1.2 compliant
- **Protocol Assertions**: Comprehensive SVA coverage
- **Coverage Models**: Functional and protocol coverage

### 1.2 Documentation Overview

| Document | Description |
|----------|-------------|
| `README.md` | Quick start guide |
| `user_guide.md` | This document |
| `integration_guide.md` | DUT integration instructions |
| `supported_features.md` | Complete feature list |
| `testplan.md` | Test plan and test descriptions |
| `assertions.md` | SVA assertion details |

## 2. Getting Started

### 2.1 Environment Setup

```bash
# Set KVIPS root directory
export KVIPS_ROOT=/path/to/kvips
```

### 2.2 File Organization

```
kvips/pcie/
├── sv/
│   ├── if/           # Interface definitions
│   ├── pkg/          # Type and UVM packages
│   ├── uvm/          # UVM components
│   ├── assertions/   # SVA files
│   ├── phy/          # PHY layer models
│   ├── dll/          # Data Link Layer
│   └── tl/           # Transaction Layer
├── examples/         # Runnable examples
└── docs/             # Documentation
```

### 2.3 Running First Example

```bash
cd kvips/pcie/examples/uvm_back2back/sim
./run_questa.sh +UVM_TESTNAME=pcie_b2b_smoke_test
```

## 3. VIP Architecture

### 3.1 UVM Component Hierarchy

```
pcie_env
├── rc_agent (Root Complex)
│   ├── driver
│   ├── monitor
│   ├── sequencer
│   └── coverage
├── ep_agent (Endpoint)
│   ├── driver
│   ├── monitor
│   ├── sequencer
│   └── coverage
└── scoreboard
```

### 3.2 Agent Modes

| Mode | Description | Use Case |
|------|-------------|----------|
| `PCIE_RC` | Root Complex | Verify EP DUTs |
| `PCIE_EP` | Endpoint | Verify RC DUTs |
| `PCIE_MONITOR` | Monitor only | Protocol analysis |

### 3.3 Interface Modes

| Interface | Description | Use Case |
|-----------|-------------|----------|
| PIPE | PHY-MAC boundary | Most integrations |
| Serial | Full PHY | SERDES testing |

## 4. Configuration

### 4.1 Agent Configuration (pcie_cfg)

```systemverilog
pcie_cfg cfg = pcie_cfg::type_id::create("cfg");
cfg.agent_mode   = PCIE_RC;
cfg.if_mode      = PCIE_PIPE_MODE;
cfg.target_gen   = PCIE_GEN4;
cfg.target_width = PCIE_X4;
```

### 4.2 Plusarg Configuration

| Plusarg | Description | Default |
|---------|-------------|---------|
| `+PCIE_GEN=<n>` | Target generation (1-6) | 4 |
| `+PCIE_LANES=<n>` | Lane count (1-32) | 4 |
| `+VIP_TRACE` | Enable verbose logging | Off |
| `+VIP_TR` | Enable transaction recording | Off |
| `+VIP_STATS` | Enable statistics | Off |

## 5. Transactions

The VIP uses `pcie_transaction` to represent TLP/DLLP/ordered-set traffic at a UVM sequence-item level.

## 6. Sequences

Sequence library is intended to cover:
- Link bring-up
- Memory/config/io TLPs
- Error injection / stress

---

## Agent note (2026-02-02T05:17:58-08:00)

- This doc is kept as a “product intent” guide. Current implementation status is tracked in `kvips/pcie/docs/supported_features.md`.
- In the runnable example (`kvips/pcie/examples/uvm_back2back`), EP is configured monitor-only to avoid multi-driving a single PIPE interface instance.
- Verified `pcie_b2b_smoke_test` and `pcie_b2b_mem_test` compile/elab/run under:
  - Questa `2025_3_2`
  - VCS `2025.06_1`
  - Xcelium `25.03.007`
