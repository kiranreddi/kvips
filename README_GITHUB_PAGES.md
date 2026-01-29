# KVIPS - Premium Verification IP Library

**Note:** This is the source repository. For documentation and guides, visit our [GitHub Pages site](https://kiranreddi.github.io/kvips/).

## 🚀 Quick Links

- 📖 **[Documentation](https://kiranreddi.github.io/kvips/docs/)**
- 🚀 **[Getting Started](https://kiranreddi.github.io/kvips/docs/getting-started/)**
- 📦 **[VIP Catalog](https://kiranreddi.github.io/kvips/vips/)**
- 🔍 **[Code Review](https://kiranreddi.github.io/kvips/docs/code-review/)**

## What is KVIPS?

KVIPS is a vendor-neutral, production-ready SystemVerilog UVM verification IP library designed for semiconductor verification engineers. It provides professional-grade protocol VIPs that have been validated on leading EDA tools.

### Key Features

✅ **UVM-Compliant** - Built on Accellera UVM 1.1d/1.2 standards  
✅ **Multi-Simulator** - Validated on Questa, VCS, and Xcelium  
✅ **Production-Ready** - Comprehensive assertions and scoreboards  
✅ **Well-Documented** - Extensive guides, examples, and API docs  
✅ **Highly Configurable** - Flexible configuration for various use cases  
✅ **Vendor-Neutral** - No simulator-specific extensions

## Available VIPs

| VIP | Status | Description |
|-----|--------|-------------|
| **AXI4 Full** | ✅ Stable v1.0 | AMBA AXI4 master/slave with assertions |
| APB | 🚧 Planned | Advanced Peripheral Bus |
| AHB | 🚧 Planned | Advanced High-performance Bus |

## Quick Start

```bash
# Clone repository
git clone https://github.com/kiranreddi/kvips.git
cd kvips

# Run AXI4 example (Questa)
cd axi4/examples/uvm_back2back/sim
./run_questa.sh +UVM_TESTNAME=axi4_b2b_test

# Run with waveforms
./run_questa.sh +UVM_TESTNAME=axi4_b2b_test +KVIPS_WAVES
```

## Supported Tools

| Tool | Validated Version | Status |
|------|------------------|--------|
| Siemens Questa | 2025.3_2 | ✅ Fully Supported |
| Synopsys VCS | 2025.06_1 | ✅ Fully Supported |
| Cadence Xcelium | 25.03.007 | ✅ Fully Supported |

## Documentation

Complete documentation is available on our **[GitHub Pages site](https://kiranreddi.github.io/kvips/)**.

Key documents:
- [Getting Started Guide](https://kiranreddi.github.io/kvips/docs/getting-started/)
- [AXI4 VIP Documentation](https://kiranreddi.github.io/kvips/docs/axi4-vip/)
- [Integration Guide](https://kiranreddi.github.io/kvips/docs/axi4/integration/)
- [Code Review & Quality Assessment](https://kiranreddi.github.io/kvips/docs/code-review/)

## Repository Structure

```
kvips/
├── common/              # Shared utilities and macros
├── axi4/                # AXI4 Full VIP
│   ├── sv/             # SystemVerilog source
│   ├── docs/           # VIP-specific docs
│   └── examples/       # Working examples
├── docs/               # GitHub Pages documentation
├── assets/             # CSS, JS, images for docs
└── _layouts/           # Jekyll templates
```

## Contributing

We welcome contributions! Please see our [Contributing Guide](CONTRIBUTING.md) for details.

## License

KVIPS is released under the **MIT License**. See [LICENSE](LICENSE) for details.

## Support

- 🐛 [Issue Tracker](https://github.com/kiranreddi/kvips/issues)
- 💬 [Discussions](https://github.com/kiranreddi/kvips/discussions)
- 📧 Email: your-email@example.com

## Citation

If you use KVIPS in your research or project, please cite:

```bibtex
@misc{kvips2026,
  title={KVIPS: Premium SystemVerilog UVM Verification IP Library},
  author={KVIPS Contributors},
  year={2026},
  publisher={GitHub},
  url={https://github.com/kiranreddi/kvips}
}
```

---

<p align="center">
  <strong>Built with ❤️ for the verification community</strong>
</p>
