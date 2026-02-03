---
layout: default
title: AHB Verification IP
permalink: /docs/ahb-vip/
---

# AHB (AHB-Lite/AHB Full) Protocol Verification IP

<div class="hero" style="padding: 2rem; margin: -2rem -2rem 2rem -2rem;">
<div style="max-width: 800px; margin: 0 auto;">
<h1 style="color: white; margin-bottom: 1rem;">AHB VIP</h1>
<p style="font-size: 1.25rem; color: rgba(255,255,255,0.95);">
Professional-grade AMBA AHB verification component supporting both AHB-Lite and AHB Full with master/slave agents, protocol checkers, and built-in scoreboard
</p>
<div style="display: flex; gap: 0.5rem; flex-wrap: wrap; margin-top: 1.5rem;">
<span class="badge badge-success">Stable v1.0</span>
<span class="badge badge-info">UVM 1.1d/1.2</span>
<span class="badge badge-primary">IEEE 1800</span>
<span class="badge badge-success">Single Image AHB-Lite/AHB Full</span>
</div>
</div>
</div>

---

## 📋 Overview

The KVIPS AHB VIP provides a comprehensive verification environment for AMBA AHB-Lite and AHB Full protocols in a **single compiled image** with runtime mode selection. It includes:

<div class="grid grid-2" style="margin: 2rem 0;">
<div class="card">
<h3>🎯 Master Agent</h3>
<ul>
<li>Single and burst transfers (INCR4/8/16, WRAP4/8/16)</li>
<li>Configurable address/control pipelining</li>
<li>Variable HSIZE (byte/half/word/dword)</li>
<li>Configurable inter-transaction delays</li>
<li>Runtime mode switch: AHB-Lite vs AHB Full</li>
</ul>
</div>

<div class="card">
<h3>🔄 Slave Agent</h3>
<ul>
<li>Flexible memory model with byte-addressable storage</li>
<li>Configurable wait states (HREADY control)</li>
<li>Error injection (OKAY/ERROR responses)</li>
<li>Address range-based error injection</li>
<li>Stall modeling for realistic timing</li>
</ul>
</div>

<div class="card">
<h3>✅ Protocol Checkers</h3>
<ul>
<li>Hold-stability assertions while stalled</li>
<li>Known/X checks on control signals</li>
<li>AHB-Lite response legality (no RETRY/SPLIT)</li>
<li>Burst legality and boundary checks</li>
<li>Runtime assertion enable/disable switches</li>
</ul>
</div>

<div class="card">
<h3>📊 Verification Features</h3>
<ul>
<li>Monitor-based expected memory scoreboard</li>
<li>Transaction reconstruction and logging</li>
<li>Functional coverage (size, burst, stalls, responses)</li>
<li>Performance statistics and counters</li>
<li>End-of-test summary reporting</li>
</ul>
</div>
</div>

---

## 🔌 Protocol Mode Selection

The AHB VIP supports both AHB-Lite and AHB Full in a **single compiled image**. Select the mode at runtime:

```bash
# AHB-Lite mode (default) - single master, OKAY/ERROR responses only
+AHB_MODE=AHB_LITE

# AHB Full mode - extended features (arbiter support planned)
+AHB_MODE=AHB_FULL
```

<div class="alert alert-info">
<strong>📝 Note:</strong> AHB-Lite mode restricts responses to OKAY/ERROR and assumes single-master operation. AHB Full mode enables optional signals; multi-master arbitration and RETRY/SPLIT support are planned for future releases.
</div>

---

## 🚀 Quick Start

### Run Example Tests

Navigate to the AHB examples directory and run tests:

```bash
cd ahb/examples/

# List available tests
make list-tests

# Run smoke test on Questa
make questa TEST=ahb_smoke_test

# Run with AHB Full mode
make questa TEST=ahb_smoke_test PLUSARGS='+AHB_MODE=AHB_FULL'

# Run wait state test on VCS
make vcs TEST=ahb_wait_state_test

# Run stress test on Xcelium
make xcelium TEST=ahb_random_stress_test

# Run on Verilator
make verilator TEST=ahb_smoke_test

# Full Verilator regression
make regress-verilator

# Run with LSF (if tools require job scheduler)
make questa USE_LSF=1 TEST=ahb_smoke_test
```

> 📝 Note: SVA assertions are skipped under Verilator.

### Available Test Cases

| Test Name | Description |
|-----------|-------------|
| `ahb_smoke_test` | Basic SINGLE transfers (read/write) |
| `ahb_wait_state_test` | Tests slave wait state insertion |
| `ahb_back_to_back_test` | Burst transfers with minimal gaps |
| `ahb_random_stress_test` | Random bursts, sizes, and stalls |
| `ahb_error_test` | Error response injection testing |

---

## 📐 Architecture

### Component Hierarchy

```
ahb_env
├── ahb_agent (master)
│   ├── ahb_sequencer
│   ├── ahb_master_driver
│   └── ahb_monitor
├── ahb_agent (slave)
│   ├── ahb_sequencer
│   ├── ahb_slave_driver
│   └── ahb_monitor
├── ahb_scoreboard
└── ahb_txn_logger (optional)
```

### Directory Structure

```
kvips/ahb/
├── sv/
│   ├── if/
│   │   └── ahb_if.sv              # AHB interface + clocking blocks
│   ├── assertions/
│   │   └── ahb_if_sva.svh         # Protocol assertions (SVA)
│   ├── pkg/
│   │   ├── ahb_types_pkg.sv       # Type definitions, enums
│   │   └── ahb_uvm_pkg.sv         # UVM package
│   └── uvm/
│       ├── ahb_cfg.sv             # Configuration object
│       ├── ahb_txn.sv             # Transaction item
│       ├── ahb_sequencer.sv       # Sequencer
│       ├── ahb_master_driver.sv   # Master driver
│       ├── ahb_slave_driver.sv    # Slave driver
│       ├── ahb_monitor.sv         # Passive monitor
│       ├── ahb_scoreboard.sv      # Data integrity checker
│       ├── ahb_agent.sv           # Agent wrapper
│       ├── ahb_env.sv             # Environment
│       └── sequences/
│           ├── ahb_base_seq.sv
│           ├── ahb_single_seq.sv
│           └── ahb_burst_seq.sv
├── docs/
│   ├── user_guide.md              # Detailed usage guide
│   ├── integration_guide.md       # Integration instructions
│   ├── supported_features.md      # Feature list & roadmap
│   ├── assertions.md              # Assertion documentation
│   ├── testplan.md                # Test coverage plan
│   └── directory_structure.md     # File organization
├── examples/
│   └── uvm_back2back/             # Self-contained demo testbench
└── README.md                       # Quick reference
```

---

## ⚙️ Configuration

### Key Configuration Knobs

```systemverilog
class ahb_cfg extends uvm_object;
  
  // Protocol Mode
  ahb_mode_t mode = AHB_MODE_LITE;  // AHB_MODE_LITE or AHB_MODE_FULL
  
  // Slave Configuration - Wait States
  bit        allow_wait_states = 1;
  int unsigned min_wait = 0;        // Minimum wait cycles
  int unsigned max_wait = 5;        // Maximum wait cycles
  
  // Slave Configuration - Error Injection
  bit        err_enable = 0;        // Enable error injection
  bit [31:0] err_addr_lo = 0;       // Error range start
  bit [31:0] err_addr_hi = 0;       // Error range end
  int unsigned err_pct = 10;        // Error probability %
  
  // Master Configuration - Burst Policy
  bit        allow_bursts = 1;      // Enable burst transfers
  bit        allow_wrap = 1;        // Enable WRAP bursts
  int unsigned max_incr_len = 16;   // Max INCR burst length
  
  // Debug & Coverage
  bit        trace_enable = 0;      // Transaction tracing
  bit        coverage_enable = 1;   // Coverage sampling
  
  // Assertion Control
  bit        assertions_enable = 1; // Enable SVA checks
  
  // Address Configuration
  bit [31:0] addr_min = 32'h0000_0000;
  bit [31:0] addr_max = 32'hFFFF_FFFF;
  
endclass
```

### Runtime Configuration via Plusargs

```bash
# Protocol mode selection
+AHB_MODE=AHB_LITE       # Default: AHB-Lite mode
+AHB_MODE=AHB_FULL       # AHB Full mode

# Debug options
+VIP_TRACE               # Enable transaction tracing
+UVM_VERBOSITY=UVM_HIGH  # Verbose UVM messaging

# Scoreboard options
+KVIPS_AHB_SB_WARN_UNINIT  # Warn on reads from uninitialized memory
```

---

## 📊 Supported Features

### ✅ Currently Supported (v0.1)

#### Protocol Support
- ✅ Single-bus, single-master operation (AHB-Lite style)
- ✅ Runtime mode selection: AHB-Lite vs AHB Full
- ✅ Basic responses: OKAY and ERROR
- ✅ Address/control pipelining with HREADY stall handling

#### Transfer Types
- ✅ SINGLE transfers
- ✅ INCR4/8/16 burst transfers
- ✅ WRAP4/8/16 burst transfers with wrap addressing
- ✅ Variable HSIZE (byte/half-word/word/double-word)

#### VIP Components
- ✅ Master agent: drives transfers with correct address/control vs data phasing
- ✅ Slave agent: responds with HREADYOUT/HRESP/HRDATA, captures writes
- ✅ Passive monitor: reconstructs completed transfers
- ✅ Scoreboard: monitor-based expected memory model
- ✅ Transaction logger: per-transfer logging + end-of-test summary

#### Timing & Stalls
- ✅ Configurable wait-state insertion (slave)
- ✅ Hold-stability during stalls
- ✅ Inter-transaction gap control (master)

#### Debug & Verification
- ✅ Interface-bound SVA assertions
  - Hold-stability while stalled
  - Known/X checks on control signals
  - AHB-Lite response legality
- ✅ Functional coverage
  - Read/write operations
  - Transfer sizes
  - Burst types and lengths
  - Wait state bins
  - Response types
  - Cross-coverage matrices

### 📋 Planned Features (Future Releases)

#### AHB Full Enhancements
- 📋 Multi-master arbitration support
- 📋 HMASTER behavior tracking
- 📋 SPLIT/RETRY response handling
- 📋 HSPLITx signal support

#### Protocol Enhancements
- 📋 BUSY insertion and legality checking
- 📋 Stricter wrap boundary alignment enforcement
- 📋 Endianness configuration (currently little-endian)
- 📋 Multiple slave regions with interconnect-like decode

#### Advanced Features
- 📋 Full UVM transaction recording (UVM TR) integration
- 📋 Performance monitoring and bottleneck analysis
- 📋 Advanced constrained random coverage
- 📋 Formal verification property exports

---

## 🔍 Debug Workflow

### Recommended Bring-Up Sequence

1. **Start with basic transfers:**
   ```bash
   make questa TEST=ahb_smoke_test
   ```
   Verifies basic SINGLE read/write operations

2. **Enable wait states:**
   ```bash
   make questa TEST=ahb_wait_state_test
   ```
   Tests slave stall insertion and hold-stability

3. **Enable burst stress:**
   ```bash
   make questa TEST=ahb_back_to_back_test
   make questa TEST=ahb_random_stress_test
   ```
   Tests various burst types and random traffic

4. **Enable error injection:**
   ```bash
   make questa TEST=ahb_error_test
   ```
   Tests error response handling

### Debug Options

```bash
# Verbose UVM messaging
+UVM_VERBOSITY=UVM_HIGH

# Enable transaction tracing
+VIP_TRACE

# Warn on uninitialized memory reads
+KVIPS_AHB_SB_WARN_UNINIT

# Waveform dumping
+KVIPS_WAVES
```

---

## 📚 Detailed Documentation

For comprehensive information, refer to the following documents in `kvips/ahb/docs/`:

- **[User Guide](../../ahb/docs/user_guide.md)** - Detailed configuration and usage
- **[Integration Guide](../../ahb/docs/integration_guide.md)** - Step-by-step integration
- **[Supported Features](../../ahb/docs/supported_features.md)** - Complete feature list
- **[Assertions](../../ahb/docs/assertions.md)** - SVA checker documentation
- **[Testplan](../../ahb/docs/testplan.md)** - Test coverage mapping
- **[Directory Structure](../../ahb/docs/directory_structure.md)** - File organization

---

## 💡 Integration Example

### Minimal Testbench Integration

```systemverilog
// 1. Instantiate AHB interface
ahb_if ahb_if_inst (
    .HCLK(clk),
    .HRESETn(rst_n)
);

// 2. In your UVM environment
class my_env extends uvm_env;
    ahb_env ahb_env_inst;
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create AHB configuration
        ahb_cfg cfg = ahb_cfg::type_id::create("cfg");
        cfg.mode = AHB_MODE_LITE;
        cfg.allow_wait_states = 1;
        cfg.max_wait = 5;
        cfg.trace_enable = 1;
        
        // Set virtual interface
        if (!uvm_config_db#(virtual ahb_if)::get(this, "", "vif", cfg.vif))
            `uvm_fatal("ENV", "Failed to get AHB interface")
        
        // Create environment
        uvm_config_db#(ahb_cfg)::set(this, "ahb_env_inst", "cfg", cfg);
        ahb_env_inst = ahb_env::type_id::create("ahb_env_inst", this);
    endfunction
endclass

// 3. Start sequences
class my_test extends uvm_test;
    task run_phase(uvm_phase phase);
        ahb_single_seq seq;
        phase.raise_objection(this);
        
        seq = ahb_single_seq::type_id::create("seq");
        seq.addr = 32'h1000;
        seq.data = 32'hDEADBEEF;
        seq.is_write = 1;
        seq.start(env.ahb_env_inst.master_agent.sequencer);
        
        phase.drop_objection(this);
    endtask
endclass
```

---

## 🎓 Example Tests

Located in `kvips/ahb/examples/uvm_back2back/`:

```
examples/
├── tb/
│   ├── top.sv                  # Top-level testbench
│   └── test_pkg.sv             # Test package
├── tests/
│   ├── ahb_base_test.sv
│   ├── ahb_smoke_test.sv
│   ├── ahb_wait_state_test.sv
│   ├── ahb_back_to_back_test.sv
│   └── ahb_random_stress_test.sv
└── sim/
    ├── Makefile
    ├── run_questa.sh
    ├── run_vcs.sh
    └── run_xcelium.sh
```

---

## 🔧 Validated Tool Versions

<div style="display: flex; gap: 0.5rem; flex-wrap: wrap; margin: 1rem 0;">
<span class="badge badge-info">Siemens Questa 2025.3_2</span>
<span class="badge badge-info">Synopsys VCS 2025.06_1</span>
<span class="badge badge-info">Cadence Xcelium 25.03.007</span>
</div>

---

## 📞 Support & Resources

<div class="grid grid-2" style="margin: 2rem 0;">
<div class="card">
<h4>📖 Documentation</h4>
<ul>
<li><a href="{{ '/docs/getting-started' | relative_url }}">Getting Started</a></li>
<li><a href="{{ '/docs/best-practices' | relative_url }}">Best Practices</a></li>
<li><a href="{{ '/docs/faq' | relative_url }}">FAQ</a></li>
</ul>
</div>

<div class="card">
<h4>💬 Community</h4>
<ul>
<li><a href="https://github.com/kiranreddi/kvips/discussions">Discussions</a></li>
<li><a href="https://github.com/kiranreddi/kvips/issues">Report Issues</a></li>
<li><a href="{{ '/docs/vips' | relative_url }}">VIP Catalog</a></li>
</ul>
</div>
</div>

---

<div style="text-align: center; margin: 3rem 0; padding: 2rem; background: var(--bg-secondary); border-radius: var(--radius-xl);">
<h3>Ready to Verify AHB Designs?</h3>
<p style="font-size: 1.125rem; color: var(--text-secondary); margin: 1rem 0;">
Get started with KVIPS AHB VIP and accelerate your verification!
</p>
<a href="{{ '/docs/getting-started' | relative_url }}" class="btn btn-primary">Get Started</a>
<a href="https://github.com/kiranreddi/kvips" class="btn btn-secondary">View on GitHub</a>
</div>
