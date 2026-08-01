# KVIPS — K's Verification IP Suite

<div align="center">

![KVIPS Logo](https://img.shields.io/badge/KVIPS-Verification_IP_Suite-blue?style=for-the-badge)

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![GitHub Pages](https://img.shields.io/badge/docs-github_pages-blue)](https://kiranreddi.github.io/kvips/)
[![SystemVerilog](https://img.shields.io/badge/SystemVerilog-IEEE_1800-orange)](https://standards.ieee.org/)
[![UVM](https://img.shields.io/badge/UVM-1.1d%20%7C%201.2-green)](https://www.accellera.org/)
[![AXI4 BK2BK CI](https://github.com/kiranreddi/kvips/actions/workflows/axi4-bk2bk-verilator.yml/badge.svg?branch=main)](https://github.com/kiranreddi/kvips/actions/workflows/axi4-bk2bk-verilator.yml)
[![AXI4 DUT CI](https://github.com/kiranreddi/kvips/actions/workflows/axi4-dut-verilator.yml/badge.svg?branch=main)](https://github.com/kiranreddi/kvips/actions/workflows/axi4-dut-verilator.yml)
[![APB BK2BK CI](https://github.com/kiranreddi/kvips/actions/workflows/apb-bk2bk-verilator.yml/badge.svg?branch=main)](https://github.com/kiranreddi/kvips/actions/workflows/apb-bk2bk-verilator.yml)
[![APB DUT CI](https://github.com/kiranreddi/kvips/actions/workflows/apb-dut-verilator.yml/badge.svg?branch=main)](https://github.com/kiranreddi/kvips/actions/workflows/apb-dut-verilator.yml)
[![AHB BK2BK CI](https://github.com/kiranreddi/kvips/actions/workflows/ahb-bk2bk-verilator.yml/badge.svg?branch=main)](https://github.com/kiranreddi/kvips/actions/workflows/ahb-bk2bk-verilator.yml)
[![AHB DUT CI](https://github.com/kiranreddi/kvips/actions/workflows/ahb-dut-verilator.yml/badge.svg?branch=main)](https://github.com/kiranreddi/kvips/actions/workflows/ahb-dut-verilator.yml)
[![APB Cocotb CI](https://github.com/kiranreddi/kvips/actions/workflows/apb-cocotb-verilator.yml/badge.svg?branch=main)](https://github.com/kiranreddi/kvips/actions/workflows/apb-cocotb-verilator.yml)
[![AXI4 Cocotb CI](https://github.com/kiranreddi/kvips/actions/workflows/axi4-cocotb-verilator.yml/badge.svg?branch=main)](https://github.com/kiranreddi/kvips/actions/workflows/axi4-cocotb-verilator.yml)
[![AHB Cocotb CI](https://github.com/kiranreddi/kvips/actions/workflows/ahb-cocotb-verilator.yml/badge.svg?branch=main)](https://github.com/kiranreddi/kvips/actions/workflows/ahb-cocotb-verilator.yml)
[![Verilator Lint](https://github.com/kiranreddi/kvips/actions/workflows/verilator-lint.yml/badge.svg?branch=main)](https://github.com/kiranreddi/kvips/actions/workflows/verilator-lint.yml)
[![Pages](https://github.com/kiranreddi/kvips/actions/workflows/pages.yml/badge.svg?branch=main)](https://github.com/kiranreddi/kvips/actions/workflows/pages.yml)

**Professional, vendor-neutral verification IP suite for AMBA protocols and high-speed interfaces**

[📚 Documentation](https://kiranreddi.github.io/kvips/) | [🚀 Getting Started](https://kiranreddi.github.io/kvips/docs/getting-started/) | [📖 Code Review](https://kiranreddi.github.io/kvips/docs/code-review/) | [💬 Discussions](https://github.com/kiranreddi/kvips/discussions)

</div>

---

## 🎯 Overview

KVIPS is an open-source SystemVerilog UVM verification IP suite for AMBA protocols. Each VIP provides:

- **Protocol checkers** — SVA assertions and scoreboard-backed example environments
- **Configurable agents** — Parameterized interfaces, sequences, and runtime plusargs
- **Diagnostics** — Transaction logging, coverage hooks, and example regressions
- **Verilator CI** — Separate BK2BK and DUT workflows for AXI4, APB, and AHB
- **Commercial simulator validation** — AXI4, APB4, and AHB RTL-DUT flows include evidence-gated Questa, VCS, and Xcelium regressions
- **Documentation** — Guides and integration examples under [GitHub Pages](https://kiranreddi.github.io/kvips/)

---

## 📦 Available Verification IPs

| Protocol | Status | Version | Description | Documentation |
|----------|--------|---------|-------------|---------------|
| **AXI4 Full** | DUT-validated | v0.1 | AXI4 master/slave agents, assertions, scoreboard, and an executable RTL-DUT flow; commercial evidence gate plus back-to-back Verilator CI | [📖 AXI4 VIP Guide](https://kiranreddi.github.io/kvips/vips/axi4/) |
| **APB** | DUT-validated | v0.1 | APB3/APB4 agents and an executable APB4 RTL-DUT flow; commercial evidence gate plus back-to-back/DUT Verilator CI | [📖 APB VIP Guide](https://kiranreddi.github.io/kvips/docs/apb-vip/) |
| **AHB** | DUT-validated | v0.1 | AHB-Lite/Full agents, bursts, wait states, assertions, and a six-test synthesizable RAM DUT gate; multi-master fabric remains pending | [📖 AHB VIP Guide](https://kiranreddi.github.io/kvips/docs/ahb-vip/) |
| **PCIe** | 📋 Planned | - | PCIe Gen3/Gen4/Gen5 with TLP generation | - |
| **USB 3.x** | 📋 Planned | - | USB 3.0/3.1/3.2 protocol layers | - |

> 🗺️ Full roadmap available in [VIP Catalog](https://kiranreddi.github.io/kvips/vips/)

---

## 🌟 Key Features

<table>
<tr>
<td width="50%">

### 🏗️ **Architecture**
- Modular, reusable UVM components
- Parameterized interfaces and agents
- Layered sequence library
- Protocol-accurate timing
- Configurable address/data widths

</td>
<td width="50%">

### 🔍 **Verification**
- Protocol assertions (SVA)
- Functional coverage models
- Transaction-level scoreboard
- Error injection sequences
- Constrained random stimulus

</td>
</tr>
<tr>
<td>

### 🛠️ **Tooling**
- Verilator 5.048 (CI regressions + portable lint)
- GitHub Actions (lint, regressions, Pages)
- Commercial Questa, VCS, and Xcelium scripts with evidence-gated AXI4/APB4/AHB DUT regressions

</td>
<td>

### 📚 **Documentation**
- Comprehensive user guides
- Integration examples
- API reference
- Best practices
- Code review reports

</td>
</tr>
</table>

---

## 🚀 Quick Start

### Prerequisites

- SystemVerilog simulator (Questa/VCS/Xcelium)
- UVM library (1.1d or 1.2)
- Basic UVM knowledge

### Installation

```bash
# Clone the repository
git clone https://github.com/kiranreddi/kvips.git
cd kvips

# Run commands from the repository root; each protocol has its own examples directory
```

### Run Your First Test (Questa)

```bash
cd axi4/examples

# Run a single test (compiles + runs)
make questa TEST=axi4_b2b_test SEED=1

# Dump waves (VCD)
make questa TEST=axi4_b2b_test SEED=1 PLUSARGS='+KVIPS_WAVES'

# Dump waves (FSDB, requires Verdi/Novas PLI)
make questa-waves TEST=axi4_b2b_test SEED=1
```

### Run Your First Test (VCS)

```bash
cd axi4/examples

make vcs TEST=axi4_b2b_test SEED=1
make vcs TEST=axi4_b2b_test SEED=1 PLUSARGS='+KVIPS_WAVES'
```

### Run Your First Test (Xcelium)

```bash
cd axi4/examples
make xcelium TEST=axi4_b2b_test SEED=1
make xcelium TEST=axi4_b2b_test SEED=1 PLUSARGS='+KVIPS_WAVES'
```

### Run Your First Test (Verilator)

```bash
cd axi4/examples/uvm_back2back/sim

# Single test
./run_verilator.sh +UVM_TESTNAME=axi4_b2b_test

# Full regression (from the repository root)
make -C axi4/examples regress-verilator
```

> 📝 Note: SVA assertions are skipped under Verilator.

### Run the RTL-DUT examples

The DUT examples connect a KVIPS master to a signal-level synthesizable RAM,
then require monitor handshakes, checker health, and scoreboard agreement.
They are separate from the back-to-back demos:

```bash
# AXI4 Full DUT (11 tests in the default list)
make -C axi4/examples regress-rtl-questa USE_LSF=1
make -C axi4/examples regress-rtl-vcs USE_LSF=1
make -C axi4/examples regress-rtl-xcelium USE_LSF=1

# APB4 DUT (8 tests in the default list)
make -C apb/examples regress-rtl-questa USE_LSF=1
make -C apb/examples regress-rtl-vcs USE_LSF=1
make -C apb/examples regress-rtl-xcelium USE_LSF=1

# AHB DUT (6 tests in the default list)
make -C ahb/examples regress-rtl-questa USE_LSF=1
make -C ahb/examples regress-rtl-vcs USE_LSF=1
make -C ahb/examples regress-rtl-xcelium USE_LSF=1
```

See the [AXI4 DUT milestone](https://github.com/kiranreddi/kvips/blob/main/axi4/docs/dut_verification.md)
and [APB4 DUT milestone](https://github.com/kiranreddi/kvips/blob/main/apb/docs/dut_verification.md)
and [AHB DUT milestone](https://github.com/kiranreddi/kvips/blob/main/ahb/docs/dut_verification.md)
for test lists, evidence rules, and the CI-only Verilator distinction.

---

## 📂 Repository Structure

```
kvips/
├── axi4/                      # AXI4 Full VIP
│   ├── sv/                    # SystemVerilog source
│   │   ├── pkg/              # UVM package
│   │   ├── uvm/              # Agent components
│   │   ├── if/               # Interface definitions
│   │   └── assertions/       # SVA protocol checks
│   ├── examples/             # Testbenches and tests
│   │   ├── uvm_back2back/    # VIP-to-VIP executable demo
│   │   └── uvm_dut/          # AXI4 master to RTL-DUT integration
│   └── docs/                 # VIP-specific documentation
├── apb/                       # APB3/APB4 VIP (stable)
│   ├── sv/
│   ├── docs/
│   └── examples/               # back-to-back and APB4 RTL-DUT flows
├── ahb/                       # AHB-Lite/AHB Full VIP (DUT validated)
│   ├── sv/
│   ├── docs/
│   └── examples/
├── docs/                      # GitHub Pages documentation
│   ├── getting-started.md
│   ├── axi4-vip.md           # Source guide (Pages copy is under pages/docs/)
│   ├── best-practices.md
│   ├── code-review.md
│   └── faq.md
├── assets/                    # CSS/JS for GitHub Pages
├── .github/workflows/         # GitHub Actions CI/CD
├── .pre-commit-config.yaml   # Verilator pre-commit hooks
└── README.md                  # This file
```

---

## 🏗️ AXI4 VIP Architecture

```
┌───────────────────────────────────────────────────────────┐
│                    UVM Test Environment                   │
├───────────────────────────────────────────────────────────┤
│                                                           │
│  ┌─────────────────────┐        ┌─────────────────────┐   │
│  │   AXI4 Master Agent │        │   AXI4 Slave Agent  │   │
│  │  ┌────────────────┐ │        │  ┌────────────────┐ │   │
│  │  │ Sequencer      │ │        │  │ Sequencer      │ │   │
│  │  └───────┬────────┘ │        │  └───────┬────────┘ │   │
│  │          │          │        │          │          │   │
│  │  ┌───────▼────────┐ │        │  ┌───────▼────────┐ │   │
│  │  │ Driver         │◄┼────────┼─►│ Driver         │ │   │
│  │  └───────┬────────┘ │        │  └───────┬────────┘ │   │
│  │          │          │        │          │          │   │
│  │  ┌───────▼────────┐ │        │  ┌───────▼────────┐ │   │
│  │  │ Monitor        │◄┼────────┼─►│ Monitor        │ │   │
│  │  └───────┬────────┘ │        │  └───────┬────────┘ │   │
│  │          │          │        │          │          │   │
│  │  ┌───────▼────────┐ │        │  ┌───────▼────────┐ │   │
│  │  │ Coverage       │ │        │  │ Coverage       │ │   │
│  │  └────────────────┘ │        │  └────────────────┘ │   │
│  └─────────────────────┘        └─────────────────────┘   │
│             │                             │               │
│             └─────────────┬───────────────┘               │
│                           │                               │
│                   ┌───────▼────────┐                      │
│                   │  Scoreboard    │                      │
│                   └────────────────┘                      │
└───────────────────────────────────────────────────────────┘
                           │
                           ▼
                    ┌─────────────┐
                    │  AXI4 DUT   │
                    └─────────────┘
```

---

## 🎯 Integration Example

```systemverilog
// 1. Import the VIP package
import uvm_pkg::*;
import axi4_uvm_pkg::*;

// 2. Instantiate the AXI4 interface
axi4_if #(
  .ADDR_WIDTH(32),
  .DATA_WIDTH(64),
  .ID_WIDTH(4)
) axi_if (clk, rst_n);

// 3. Configure the agent
axi4_agent_cfg m_cfg = axi4_agent_cfg::type_id::create("m_cfg");
m_cfg.is_active = UVM_ACTIVE;
m_cfg.agent_type = AXI4_MASTER;
m_cfg.enable_pipelined = 1;
m_cfg.max_outstanding = 8;

// 4. Connect to the DUT
assign dut.axi_awvalid = axi_if.awvalid;
assign dut.axi_awaddr  = axi_if.awaddr;
// ... (connect all signals)

// 5. Run sequences
axi4_write_seq #(64) seq = axi4_write_seq::type_id::create("seq");
seq.start(env.axi_master.sequencer);
```

> For complete integration guide, see [Getting Started](https://kiranreddi.github.io/kvips/docs/getting-started/)

---

## ✅ Quality & Testing

### Code Quality Metrics

| Metric | Score | Status |
|--------|-------|--------|
| **Architecture** | ⭐⭐⭐⭐⭐ 5/5 | Modular, parameterized design |
| **Code Style** | ⭐⭐⭐⭐⭐ 5/5 | Consistent, documented |
| **UVM Compliance** | ⭐⭐⭐⭐⭐ 5/5 | Factory, config DB, TLM |
| **Protocol Compliance** | ⭐⭐⭐⭐☆ 4/5 | Implemented AXI4/APB scope with assertions; see protocol gap documents |
| **Coverage** | ⭐⭐⭐⭐☆ 4/5 | Transaction + assertions |
| **Documentation** | ⭐⭐⭐⭐⭐ 5/5 | Comprehensive guides |

> Self-assessment and gap notes: [Code Review Document](https://kiranreddi.github.io/kvips/docs/code-review/)

### Simulator Compatibility

| Simulator | Version (examples) | CI status | Notes |
|-----------|-------------------|-----------|-------|
| Verilator | 5.048 | Regressions + lint in GitHub Actions | Primary open-source validation path |
| Siemens Questa | 2025.3_2 | AXI4/APB4/AHB DUT evidence gate | Run `make -C <proto>/examples questa` or `regress-rtl-questa` |
| Synopsys VCS | 2025.06_1 | AXI4/APB4/AHB DUT evidence gate | Run `make -C <proto>/examples vcs` or `regress-rtl-vcs` |
| Cadence Xcelium | 25.03.007 | AXI4/APB4/AHB DUT evidence gate | Run `make -C <proto>/examples xcelium` or `regress-rtl-xcelium` |

### CI/CD Pipeline

All automation runs on **GitHub Actions**:

- **Verilator Lint** — Blocking portable lint for AXI4, APB, and AHB interface subsets (`make lint`)
- **BK2BK CI** — `AXI4/APB/AHB BK2BK CI` workflows (`uvm_back2back` Verilator lists)
- **DUT CI** — `AXI4/APB/AHB DUT CI` workflows (`uvm_dut` Verilator lists)
- **GitHub Pages** — Jekyll build and Actions deploy on site-path changes to `main` (Pages source must be **GitHub Actions**)
- **Local** — `make test-smoke`, `make test-verilator`, `make docs-build`, `make clean-all`

---

## 🔬 Verilator Pre-Commit Integration

KVIPS uses Verilator's pre-commit hook for automated linting:

```yaml
# .pre-commit-config.yaml
repos:
  - repo: https://github.com/verilator/verilator
    rev: v5.026
    hooks:
      - id: verilator
```

**Install pre-commit hooks:**

```bash
# Install pre-commit (if not already installed)
pip install pre-commit

# Install the hooks
pre-commit install

# Run manually (optional)
pre-commit run --all-files
```

This ensures all SystemVerilog code is linted before committing, catching syntax errors early.

---

## 📚 Documentation

| Resource | Description | Link |
|----------|-------------|------|
| **GitHub Pages** | Full documentation site with guides and examples | [🔗 View Site](https://kiranreddi.github.io/kvips/) |
| **Getting Started** | Installation, compilation, first test | [🔗 Guide](https://kiranreddi.github.io/kvips/docs/getting-started/) |
| **AXI4 VIP Guide** | Complete API reference, sequences, assertions, and RTL-DUT milestone | [🔗 Guide](https://kiranreddi.github.io/kvips/vips/axi4/) |
| **Best Practices** | Testbench architecture, debugging, optimization | [🔗 Guide](https://kiranreddi.github.io/kvips/docs/best-practices/) |
| **Code Review** | Quality assessment with recommendations | [🔗 Report](https://kiranreddi.github.io/kvips/docs/code-review/) |
| **FAQ** | Common questions and troubleshooting | [🔗 FAQ](https://kiranreddi.github.io/kvips/docs/faq/) |

---

## 🤝 Contributing

We welcome contributions! Whether it's:

- 🐛 Bug reports and fixes
- ✨ New VIP protocols
- 📝 Documentation improvements
- 💡 Feature suggestions

**Steps to contribute:**

1. Fork the repository
2. Create a feature branch (`git checkout -b feature/new-vip`)
3. Make your changes and commit (`git commit -am 'Add APB VIP'`)
4. Push to your branch (`git push origin feature/new-vip`)
5. Open a Pull Request

> Detailed contribution guidelines are coming soon. For now, use GitHub Issues/Discussions for changes and proposals.

---

## 🐛 Issue Tracking & Support

- **🐛 Bug Reports:** [GitHub Issues](https://github.com/kiranreddi/kvips/issues)
- **💬 Questions:** [GitHub Discussions](https://github.com/kiranreddi/kvips/discussions)
- **📧 Email:** Create a discussion thread for private inquiries

---

## 📜 License

KVIPS is released under the **MIT License**, allowing free use in both commercial and non-commercial projects.

```
MIT License

Copyright (c) 2026 Kiran Tathekalva

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.
```

See [LICENSE](LICENSE) file for full details.

---

## 🙏 Acknowledgments

KVIPS is built on the shoulders of giants:

- **Accellera UVM** — Universal Verification Methodology
- **IEEE 1800** — SystemVerilog standard
- **AMBA Specifications** — ARM protocol standards
- **Open-source community** — Countless verification engineers who share knowledge

---

## 📊 Project Statistics

![GitHub stars](https://img.shields.io/github/stars/kiranreddi/kvips?style=social)
![GitHub forks](https://img.shields.io/github/forks/kiranreddi/kvips?style=social)
![GitHub issues](https://img.shields.io/github/issues/kiranreddi/kvips)
![GitHub pull requests](https://img.shields.io/github/issues-pr/kiranreddi/kvips)
![Lines of code](https://img.shields.io/tokei/lines/github/kiranreddi/kvips)

---

## 🚦 Roadmap

### Phase 1: Core Bus Protocols (2026 Q1-Q2)
- [x] AXI4 Full (v0.1) — **DUT VALIDATED**
- [x] APB3/APB4 (v0.1) — **DUT VALIDATED**
- [x] AHB-Lite/AHB Full (v0.1) — **DUT VALIDATED** (single-master RAM integration; fabric semantics pending)

### Phase 2: High-Speed Interfaces (2026 Q3-Q4)
- [ ] PCIe Gen3/Gen4 — Q3 2026
- [ ] USB 3.x — Q4 2026
- [ ] Ethernet MAC — Q4 2026

### Phase 3: Peripheral Interfaces (2027)
- [ ] I2C Master/Slave
- [ ] SPI Master/Slave
- [ ] UART with flow control

> Follow [Project Board](https://github.com/kiranreddi/kvips/projects) for live updates

---

## 🌐 Links

- **🏠 Homepage:** [https://kiranreddi.github.io/kvips/](https://kiranreddi.github.io/kvips/)
- **📂 Repository:** [https://github.com/kiranreddi/kvips](https://github.com/kiranreddi/kvips)
- **💬 Discussions:** [https://github.com/kiranreddi/kvips/discussions](https://github.com/kiranreddi/kvips/discussions)
- **🐛 Issues:** [https://github.com/kiranreddi/kvips/issues](https://github.com/kiranreddi/kvips/issues)

---

<div align="center">

**Made with ❤️ by verification engineers, for verification engineers**

⭐ **Star this repo** if you find it useful! ⭐

</div>
