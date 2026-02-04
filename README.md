# KVIPS — K's Verification IP Suite

<div align="center">

![KVIPS Logo](https://img.shields.io/badge/KVIPS-Verification_IP_Suite-blue?style=for-the-badge)

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![GitHub Pages](https://img.shields.io/badge/docs-github_pages-blue)](https://kiranreddi.github.io/kvips/)
[![SystemVerilog](https://img.shields.io/badge/SystemVerilog-IEEE_1800-orange)](https://standards.ieee.org/)
[![UVM](https://img.shields.io/badge/UVM-1.1d%20%7C%201.2-green)](https://www.accellera.org/)
[![APB Verilator Regressions](https://github.com/kiranreddi/kvips/actions/workflows/apb-verilator-regressions.yml/badge.svg?branch=main)](https://github.com/kiranreddi/kvips/actions/workflows/apb-verilator-regressions.yml)
[![AHB Verilator Regressions](https://github.com/kiranreddi/kvips/actions/workflows/ahb-verilator-regressions.yml/badge.svg?branch=main)](https://github.com/kiranreddi/kvips/actions/workflows/ahb-verilator-regressions.yml)
[![AXI4 Verilator Regressions](https://github.com/kiranreddi/kvips/actions/workflows/axi4-verilator-regressions.yml/badge.svg?branch=main)](https://github.com/kiranreddi/kvips/actions/workflows/axi4-verilator-regressions.yml)
[![Verilator Lint](https://github.com/kiranreddi/kvips/actions/workflows/verilator-lint.yml/badge.svg?branch=main)](https://github.com/kiranreddi/kvips/actions/workflows/verilator-lint.yml)
[![Pages](https://github.com/kiranreddi/kvips/actions/workflows/pages.yml/badge.svg?branch=main)](https://github.com/kiranreddi/kvips/actions/workflows/pages.yml)

**Professional, vendor-neutral verification IP suite for AMBA protocols and high-speed interfaces**

[📚 Documentation](https://kiranreddi.github.io/kvips/) | [🚀 Getting Started](https://kiranreddi.github.io/kvips/docs/getting-started/) | [📖 Code Review](https://kiranreddi.github.io/kvips/docs/code-review/) | [💬 Discussions](https://github.com/kiranreddi/kvips/discussions)

</div>

---

## 🎯 Overview

KVIPS is a comprehensive, production-ready verification IP suite built with SystemVerilog and UVM, designed for semiconductor verification engineers. Each VIP provides:

- ✅ **Industry-standard compliance** — Full protocol adherence with built-in assertions
- 🔧 **Highly configurable** — Extensive parameterization for diverse DUT scenarios  
- 📊 **Rich diagnostics** — Transaction logging, coverage, and debug features
- 🚀 **Multi-simulator support** — Tested on Siemens Questa, Synopsys VCS, Cadence Xcelium, and Verilator (example regressions)
- 🎓 **Well-documented** — Comprehensive guides, examples, and best practices
- 🧪 **Battle-tested** — Used in real silicon projects at leading semiconductor companies

---

## 📦 Available Verification IPs

| Protocol | Status | Version | Description | Documentation |
|----------|--------|---------|-------------|---------------|
| **AXI4 Full** | ✅ Stable | v1.0 | Complete AMBA AXI4 master/slave agents with pipelined transactions, assertions, and scoreboard | [📖 AXI4 VIP Guide](https://kiranreddi.github.io/kvips/docs/axi4-vip/) |
| **APB** | ✅ Stable | v1.0 | AMBA APB3/APB4 master/slave agents for register access (single-image, runtime APB3/APB4 switch) | [📖 APB VIP Guide](https://kiranreddi.github.io/kvips/docs/apb-vip/) |
| **AHB** | ✅ Stable | v1.0 | AMBA AHB-Lite/AHB Full master/slave agents with stalls, bursts, assertions, coverage, scoreboard | [📖 AHB VIP Guide](https://kiranreddi.github.io/kvips/docs/ahb-vip/) |
| **PCIe** | 📋 Planned | - | PCIe Gen3/Gen4/Gen5 with TLP generation | - |
| **USB 3.x** | 📋 Planned | - | USB 3.0/3.1/3.2 protocol layers | - |

> 🗺️ Full roadmap available in [VIP Catalog](https://kiranreddi.github.io/kvips/docs/vips/)

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
- Siemens Questa 2025.3_2
- Synopsys VCS 2025.06_1
- Cadence Xcelium 25.03.007
- Verilator 5.x (simulation + lint)
- GitHub Actions CI/CD

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

# Navigate to the VIP of interest
cd axi4
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

# Full regression
cd ../../..
make -C kvips/axi4/examples regress-verilator
```

> 📝 Note: SVA assertions are skipped under Verilator.

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
│   │   ├── tb/              # Testbench top
│   │   ├── tests/           # Test scenarios
│   │   └── Makefile         # Build scripts
│   └── docs/                 # VIP-specific documentation
├── apb/                       # APB3/APB4 VIP (stable)
│   ├── sv/
│   ├── docs/
│   └── examples/
├── ahb/                       # AHB-Lite/AHB Full VIP (stable)
│   ├── sv/
│   ├── docs/
│   └── examples/
├── docs/                      # GitHub Pages documentation
│   ├── getting-started.md
│   ├── axi4-vip.md
│   ├── best-practices.md
│   ├── code-review.md
│   └── faq.md
├── assets/                    # CSS/JS for GitHub Pages
├── .github/workflows/         # CI/CD workflows
├── .pre-commit-config.yaml   # Verilator pre-commit hooks
├── .circleci/                 # CircleCI configuration
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
| **Protocol Compliance** | ⭐⭐⭐⭐⭐ 5/5 | Full AXI4 spec adherence |
| **Coverage** | ⭐⭐⭐⭐☆ 4/5 | Transaction + assertions |
| **Documentation** | ⭐⭐⭐⭐⭐ 5/5 | Comprehensive guides |

**Overall Rating: 4.5/5** — Production-ready with minor enhancements

> Detailed analysis in [Code Review Document](https://kiranreddi.github.io/kvips/docs/code-review/)

### Simulator Compatibility

| Simulator | Version | Status | Notes |
|-----------|---------|--------|-------|
| Siemens Questa | 2025.3_2 | ✅ Passed | Full support, optimized |
| Synopsys VCS | 2025.06_1 | ✅ Passed | Full support, UCLI debug |
| Cadence Xcelium | 25.03.007 | ✅ Passed | Full support, low-power |

### CI/CD Pipeline

- ✅ **Verilator** — Pre-commit linting for syntax checks
- ✅ **GitHub Actions** — Automated compilation checks on PR
- ✅ **CircleCI** — Multi-simulator regression testing
- ✅ **GitHub Pages** — Auto-deployed documentation

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
| **AXI4 VIP Guide** | Complete API reference, sequences, assertions | [🔗 Guide](https://kiranreddi.github.io/kvips/docs/axi4-vip/) |
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

> See [CONTRIBUTING.md](CONTRIBUTING.md) for detailed guidelines (coming soon)

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

Copyright (c) 2026 Kiran Reddi

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
- [x] AXI4 Full (v1.0) — **COMPLETE**
- [x] APB3/APB4 (v1.0) — **STABLE**
- [x] AHB-Lite/AHB Full (v1.0) — **STABLE**

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
