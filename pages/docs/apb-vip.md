---
layout: default
title: APB Verification IP
permalink: /docs/apb-vip/
---

# APB (APB3/APB4) Protocol Verification IP

<div class="hero" style="padding: 2rem; margin: -2rem -2rem 2rem -2rem;">
<div style="max-width: 800px; margin: 0 auto;">
<h1 style="color: white; margin-bottom: 1rem;">APB VIP</h1>
<p style="font-size: 1.25rem; color: rgba(255,255,255,0.95);">
Professional-grade AMBA APB3/APB4 verification component for low-bandwidth peripheral and register access verification
</p>
<div style="display: flex; gap: 0.5rem; flex-wrap: wrap; margin-top: 1.5rem;">
<span class="badge badge-warning">Beta v0.1</span>
<span class="badge badge-info">UVM 1.1d/1.2</span>
<span class="badge badge-primary">IEEE 1800</span>
<span class="badge badge-success">Single Image APB3/APB4</span>
</div>
</div>
</div>

---

## 📋 Overview

The KVIPS APB VIP is a vendor-neutral SystemVerilog/UVM verification component supporting both APB3 and APB4 protocols in a **single compiled image** with runtime protocol selection. Ideal for verifying register access interfaces and low-bandwidth peripheral connections.

<div class="grid grid-2" style="margin: 2rem 0;">
<div class="card">
<h3>🎯 Master Agent</h3>
<ul>
<li>Setup/access phase sequencing</li>
<li>Configurable PSEL drop/continuous modes</li>
<li>APB3/APB4 protocol compliance</li>
<li>Configurable address/data widths</li>
<li>PPROT generation (APB4)</li>
<li>PSTRB byte-lane control (APB4)</li>
</ul>
</div>

<div class="card">
<h3>🔄 Slave Agent</h3>
<ul>
<li>Word-addressed memory model</li>
<li>Configurable wait states (PREADY control)</li>
<li>Error injection (PSLVERR responses)</li>
<li>Address range-based error injection</li>
<li>PSTRB-aware byte-lane writes (APB4)</li>
<li>Multiple PSEL support</li>
</ul>
</div>

<div class="card">
<h3>✅ Protocol Checkers</h3>
<ul>
<li>Setup/access phase timing validation</li>
<li>Signal stability assertions</li>
<li>APB3-specific checks</li>
<li>APB4-specific checks (PPROT, PSTRB)</li>
<li>Runtime assertion enable/disable switches</li>
<li>PSEL/PENABLE sequencing checks</li>
</ul>
</div>

<div class="card">
<h3>📊 Verification Features</h3>
<ul>
<li>Expected memory scoreboard</li>
<li>Transaction reconstruction on completion</li>
<li>Functional coverage collection</li>
<li>Optional transaction recording (UVM TR)</li>
<li>Configurable trace levels</li>
<li>Read data integrity checking</li>
</ul>
</div>
</div>

---

## 🔌 Protocol Selection

The APB VIP supports both APB3 and APB4 in a **single compiled image**. The interface always includes APB4 signals (`PPROT`, `PSTRB`), but the mode determines their behavior:

```bash
# APB3 mode - legacy compatibility
+APB_PROTOCOL=APB3
# Master forces PSTRB='1, PPROT=0
# APB4-only assertions are disabled

# APB4 mode (default) - full APB4 features
+APB_PROTOCOL=APB4
# PPROT and PSTRB are actively driven
# All APB4 assertions are enabled
```

<div class="alert alert-info">
<strong>📝 Note:</strong> In APB3 mode, the master forces APB3-compliant semantics (PSTRB=all 1's, PPROT=0) and APB4-specific assertions are automatically disabled.
</div>

---

## 🚀 Quick Start

### Run Example Tests

Navigate to the APB examples directory and run tests:

```bash
cd /newsswork/tsmc12/boxsteru4/ktatheka/kvips/apb/examples/

# List available tests
make list-tests

# Run smoke test on Questa with APB4
make questa TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB4'

# Run with APB3 mode
make questa TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB3'

# Run on VCS
make vcs TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB4'

# Run on Xcelium
make xcelium TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB4'

# Run with LSF (if tools require job scheduler)
source /tools/lsf/conf/profile.lsf
make questa USE_LSF=1 TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB4'
```

### Available Test Cases

| Test Name | Description | Protocol |
|-----------|-------------|----------|
| `apb_b2b_smoke_test` | Basic back-to-back read/write transfers | APB3/APB4 |
| `apb_wait_state_test` | Tests slave wait state insertion (PREADY=0) | APB3/APB4 |
| `apb_error_test` | Error response injection (PSLVERR) testing | APB3/APB4 |
| `apb_strobe_test` | Byte-lane strobing tests | APB4 only |
| `apb_prot_test` | PPROT signal generation tests | APB4 only |
| `apb_random_stress_test` | Random mixed transactions | APB3/APB4 |

---

## 📐 Architecture

### Component Hierarchy

```
apb_env
├── apb_agent (master)
│   ├── apb_sequencer
│   ├── apb_master_driver
│   └── apb_monitor
├── apb_agent (slave)
│   ├── apb_sequencer
│   ├── apb_slave_driver
│   └── apb_monitor
├── apb_scoreboard
└── apb_txn_logger (optional)
```

### Directory Structure

```
kvips/apb/
├── sv/
│   ├── if/
│   │   └── apb_if.sv              # APB interface + clocking blocks
│   ├── assertions/
│   │   └── apb_if_sva.svh         # Protocol assertions (SVA)
│   ├── pkg/
│   │   ├── apb_types_pkg.sv       # Type definitions, enums
│   │   └── apb_uvm_pkg.sv         # UVM package
│   └── uvm/
│       ├── apb_cfg.sv             # Configuration object
│       ├── apb_txn.sv             # Transaction item
│       ├── apb_sequencer.sv       # Sequencer
│       ├── apb_master_driver.sv   # Master driver
│       ├── apb_slave_driver.sv    # Slave driver/responder
│       ├── apb_monitor.sv         # Passive monitor
│       ├── apb_scoreboard.sv      # Data integrity checker
│       ├── apb_agent.sv           # Agent wrapper
│       ├── apb_env.sv             # Environment
│       └── sequences/
│           ├── apb_base_seq.sv
│           ├── apb_single_seq.sv
│           └── apb_burst_seq.sv
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
class apb_cfg extends uvm_object;
  
  // Protocol Selection
  apb_protocol_t protocol = APB4;  // APB3 or APB4
  
  // Address/Data Configuration
  int unsigned addr_width = 32;
  int unsigned data_width = 32;
  int unsigned nsel = 1;           // Number of PSEL signals
  
  // Master Configuration
  bit drop_psel_between = 1;       // Drop PSEL between transactions
  int unsigned sel_index = 0;      // Which PSEL to drive (0..nsel-1)
  
  // Slave Configuration - Wait States
  bit        allow_wait_states = 1;
  int unsigned min_wait_cycles = 0;  // Minimum PREADY=0 cycles
  int unsigned max_wait_cycles = 5;  // Maximum PREADY=0 cycles
  
  // Slave Configuration - Error Injection
  bit        err_enable = 0;         // Enable PSLVERR injection
  bit [31:0] err_addr_lo = 0;        // Error range start
  bit [31:0] err_addr_hi = 0;        // Error range end
  int unsigned err_pct = 10;         // Error probability %
  
  // APB4-Specific Configuration
  bit        randomize_pprot = 1;    // Random PPROT generation
  bit        randomize_pstrb = 0;    // Random PSTRB (0=full strobes)
  
  // Debug & Coverage
  bit        trace_enable = 0;       // Transaction tracing
  bit        coverage_enable = 1;    // Coverage sampling
  
  // Assertion Control
  bit        assertions_enable = 1;  // Enable SVA checks
  
  // Memory Configuration
  bit [31:0] mem_base = 32'h0000_0000;
  bit [31:0] mem_size = 32'h0001_0000;
  
endclass
```

### Runtime Configuration via Plusargs

```bash
# Protocol mode selection
+APB_PROTOCOL=APB3       # APB3 mode
+APB_PROTOCOL=APB4       # APB4 mode (default)

# Debug options
+VIP_TRACE               # Enable transaction tracing
+UVM_VERBOSITY=UVM_HIGH  # Verbose UVM messaging

# Scoreboard options
+KVIPS_APB_SB_WARN_UNINIT  # Warn on reads from uninitialized memory
```

---

## 📊 Supported Features

### ✅ APB3 Features (Current)

- ✅ Master driver with setup/access phase sequencing
- ✅ Optional drop/continuous PSEL style
- ✅ Slave responder with word-addressed memory model
- ✅ Configurable wait-state insertion (PREADY control)
- ✅ Error injection (PSLVERR) by address range
- ✅ Monitor with transaction reconstruction
- ✅ Scoreboard with expected memory model
- ✅ Read data integrity checking

### ✅ APB4 Features (APB3 + Enhancements)

- ✅ PPROT signal generation and checking
  - Optional randomization
  - Protocol-aware constraints
- ✅ PSTRB byte-lane strobing
  - Byte-lane masked writes in memory model
  - Optional randomization or full strobes
- ✅ APB4-specific assertions
  - Automatically enabled in APB4 mode
  - Gated off in APB3 mode

### ✅ Multi-Select Support

- ✅ Vector PSEL[NSEL-1:0] interface support
- ✅ Configurable NSEL parameter
- ✅ Master selects specific sel_index

### 📋 Limitations & Future Enhancements

#### Current Limitations
- 📋 Slave memory model is simplified (not a full register model)
- 📋 No negative/bad-driver test modes yet
- 📋 Limited constrained random coverage scenarios

#### Planned Enhancements
- 📋 Register abstraction layer (RAL) integration
- 📋 Advanced error injection modes
- 📋 Protocol violation tests
- 📋 Formal verification property exports
- 📋 Performance monitoring
- 📋 Multi-master arbitration scenarios

---

## 🔍 APB3 vs APB4 Comparison

<table>
<thead>
<tr>
<th>Feature</th>
<th>APB3</th>
<th>APB4</th>
</tr>
</thead>
<tbody>
<tr>
<td><strong>PSEL/PENABLE</strong></td>
<td>✅</td>
<td>✅</td>
</tr>
<tr>
<td><strong>PADDR/PWDATA/PRDATA</strong></td>
<td>✅</td>
<td>✅</td>
</tr>
<tr>
<td><strong>PWRITE</strong></td>
<td>✅</td>
<td>✅</td>
</tr>
<tr>
<td><strong>PREADY</strong></td>
<td>✅</td>
<td>✅</td>
</tr>
<tr>
<td><strong>PSLVERR</strong></td>
<td>✅</td>
<td>✅</td>
</tr>
<tr>
<td><strong>PPROT[2:0]</strong></td>
<td>❌</td>
<td>✅ Protection control</td>
</tr>
<tr>
<td><strong>PSTRB[n-1:0]</strong></td>
<td>❌</td>
<td>✅ Byte lane strobes</td>
</tr>
<tr>
<td><strong>Write Granularity</strong></td>
<td>Full word only</td>
<td>Byte-lane selective</td>
</tr>
<tr>
<td><strong>Protection Types</strong></td>
<td>None</td>
<td>Normal/Privileged/Secure</td>
</tr>
</tbody>
</table>

---

## 🔍 Debug Workflow

### Recommended Bring-Up Sequence

1. **Start with basic APB4 transfers:**
   ```bash
   make questa TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB4'
   ```
   Verifies basic read/write operations with APB4

2. **Test APB3 backward compatibility:**
   ```bash
   make questa TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB3'
   ```
   Ensures APB3 mode works correctly

3. **Enable wait states:**
   ```bash
   make questa TEST=apb_wait_state_test PLUSARGS='+APB_PROTOCOL=APB4'
   ```
   Tests slave PREADY stalling

4. **Test byte strobes (APB4 only):**
   ```bash
   make questa TEST=apb_strobe_test PLUSARGS='+APB_PROTOCOL=APB4'
   ```
   Verifies PSTRB byte-lane writes

5. **Enable error injection:**
   ```bash
   make questa TEST=apb_error_test PLUSARGS='+APB_PROTOCOL=APB4'
   ```
   Tests PSLVERR error responses

6. **Random stress testing:**
   ```bash
   make questa TEST=apb_random_stress_test PLUSARGS='+APB_PROTOCOL=APB4'
   ```
   Runs mixed random transactions

### Debug Options

```bash
# Verbose UVM messaging
+UVM_VERBOSITY=UVM_HIGH

# Enable transaction tracing
+VIP_TRACE

# Warn on uninitialized memory reads
+KVIPS_APB_SB_WARN_UNINIT

# Waveform dumping
+KVIPS_WAVES

# Protocol mode selection
+APB_PROTOCOL=APB3  # or APB4
```

---

## 📚 Detailed Documentation

For comprehensive information, refer to the following documents in `kvips/apb/docs/`:

- **[User Guide](../../apb/docs/user_guide.md)** - Detailed configuration and usage
- **[Integration Guide](../../apb/docs/integration_guide.md)** - Step-by-step integration
- **[Supported Features](../../apb/docs/supported_features.md)** - Complete feature list
- **[Assertions](../../apb/docs/assertions.md)** - SVA checker documentation
- **[Testplan](../../apb/docs/testplan.md)** - Test coverage mapping
- **[Directory Structure](../../apb/docs/directory_structure.md)** - File organization

---

## 💡 Integration Example

### Minimal Testbench Integration

```systemverilog
// 1. Instantiate APB interface
apb_if #(
    .ADDR_W(32),
    .DATA_W(32),
    .NSEL(1)
) apb_if_inst (
    .PCLK(clk),
    .PRESETn(rst_n)
);

// 2. In your UVM environment
class my_env extends uvm_env;
    apb_env apb_env_inst;
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create APB configuration
        apb_cfg cfg = apb_cfg::type_id::create("cfg");
        cfg.protocol = APB4;
        cfg.allow_wait_states = 1;
        cfg.max_wait_cycles = 3;
        cfg.trace_enable = 1;
        
        // Set virtual interface
        if (!uvm_config_db#(virtual apb_if)::get(this, "", "vif", cfg.vif))
            `uvm_fatal("ENV", "Failed to get APB interface")
        
        // Create environment
        uvm_config_db#(apb_cfg)::set(this, "apb_env_inst", "cfg", cfg);
        apb_env_inst = apb_env::type_id::create("apb_env_inst", this);
    endfunction
endclass

// 3. Start sequences
class my_test extends uvm_test;
    task run_phase(uvm_phase phase);
        apb_single_seq seq;
        phase.raise_objection(this);
        
        // Write to register
        seq = apb_single_seq::type_id::create("seq");
        seq.addr = 32'h1000;
        seq.data = 32'hCAFEBABE;
        seq.is_write = 1;
        seq.strb = 4'hF;  // All bytes (APB4)
        seq.start(env.apb_env_inst.master_agent.sequencer);
        
        // Read back
        seq = apb_single_seq::type_id::create("seq");
        seq.addr = 32'h1000;
        seq.is_write = 0;
        seq.start(env.apb_env_inst.master_agent.sequencer);
        
        phase.drop_objection(this);
    endtask
endclass
```

---

## 🎓 Example Tests

Located in `kvips/apb/examples/uvm_back2back/`:

```
examples/
├── tb/
│   ├── top.sv                  # Top-level testbench
│   └── test_pkg.sv             # Test package
├── tests/
│   ├── apb_base_test.sv
│   ├── apb_b2b_smoke_test.sv
│   ├── apb_wait_state_test.sv
│   ├── apb_error_test.sv
│   ├── apb_strobe_test.sv      # APB4 only
│   └── apb_random_stress_test.sv
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
<li><a href="{{ '/pages/docs/getting-started' | relative_url }}">Getting Started</a></li>
<li><a href="{{ '/pages/docs/best-practices' | relative_url }}">Best Practices</a></li>
<li><a href="{{ '/pages/docs/faq' | relative_url }}">FAQ</a></li>
</ul>
</div>

<div class="card">
<h4>💬 Community</h4>
<ul>
<li><a href="https://github.com/kiranreddi/kvips/discussions">Discussions</a></li>
<li><a href="https://github.com/kiranreddi/kvips/issues">Report Issues</a></li>
<li><a href="{{ '/pages/docs/vips' | relative_url }}">VIP Catalog</a></li>
</ul>
</div>
</div>

---

<div style="text-align: center; margin: 3rem 0; padding: 2rem; background: var(--bg-secondary); border-radius: var(--radius-xl);">
<h3>Ready to Verify APB Interfaces?</h3>
<p style="font-size: 1.125rem; color: var(--text-secondary); margin: 1rem 0;">
Get started with KVIPS APB VIP and accelerate your register verification!
</p>
<a href="{{ '/pages/docs/getting-started' | relative_url }}" class="btn btn-primary">Get Started</a>
<a href="https://github.com/kiranreddi/kvips" class="btn btn-secondary">View on GitHub</a>
</div>

