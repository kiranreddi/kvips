---
layout: default
title: Getting Started with KVIPS
permalink: /docs/getting-started/
---

# Getting Started with KVIPS

Welcome to KVIPS - your comprehensive SystemVerilog UVM verification IP library! This guide will help you get up and running quickly.

## 📋 Prerequisites

Before you begin, ensure you have:

<div class="alert alert-info">
<strong>Required Tools:</strong> At least one of the following EDA simulators installed and licensed:
<ul>
<li>Siemens Questa 2024.1 or later (validated: 2025.3_2)</li>
<li>Synopsys VCS 2024.12 or later (validated: 2025.06_1)</li>
<li>Cadence Xcelium 24.09 or later (validated: 25.03.007)</li>
</ul>
</div>

### System Requirements

- **OS**: Linux (RHEL 7/8, CentOS 7/8, Ubuntu 18.04+)
- **Shell**: bash or csh/tcsh
- **Memory**: Minimum 8GB RAM (16GB+ recommended for large testbenches)
- **Disk**: ~1GB for repository and simulation artifacts

### Knowledge Prerequisites

- SystemVerilog (IEEE 1800-2017)
- UVM Methodology (Accellera UVM 1.1d or 1.2)
- Basic understanding of the protocol you're working with

---

## 🚀 Quick Start (5 Minutes)

### Step 1: Clone the Repository

```bash
# Clone KVIPS repository
git clone https://github.com/kiranreddi/kvips.git
cd kvips

# Verify structure
ls -la
# You should see: axi4/, common/, README.md, etc.
```

### Step 2: Run Your First Example

Choose your simulator and run the AXI4 back-to-back example:

#### Option A: Siemens Questa

```bash
cd axi4/examples/uvm_back2back/sim

# Single test
./run_questa.sh +UVM_TESTNAME=axi4_b2b_test

# With waveforms (VCD)
./run_questa.sh +UVM_TESTNAME=axi4_b2b_test +KVIPS_WAVES

# With waveforms (FSDB, requires Verdi/Novas PLI)
./run_questa_fsdb.sh +UVM_TESTNAME=axi4_b2b_test

# Full regression
module load lsf
cd ../../..
make -C kvips/axi4/examples regress-questa USE_LSF=1
```

#### Option B: Synopsys VCS

```bash
cd axi4/examples/uvm_back2back/sim

# Single test
./run_vcs.sh +UVM_TESTNAME=axi4_b2b_test

# With waveforms (VCD)
./run_vcs.sh +UVM_TESTNAME=axi4_b2b_test +KVIPS_WAVES
```

#### Option C: Cadence Xcelium

```bash
cd axi4/examples/uvm_back2back/sim

# Single test
./run_xcelium.sh +UVM_TESTNAME=axi4_b2b_test

# With waveforms (VCD)
./run_xcelium.sh +UVM_TESTNAME=axi4_b2b_test +KVIPS_WAVES
```

### Step 3: Verify Success

Look for these indicators in the simulation output:

```
UVM_INFO @ 1000ns: axi4_b2b_test [TEST] Test passed!
** Report counts by severity
UVM_INFO    :  250
UVM_WARNING :    0
UVM_ERROR   :    0
UVM_FATAL   :    0
```

<div class="alert alert-success">
<strong>✅ Success!</strong> You've successfully run your first KVIPS simulation. Continue reading to learn how to integrate VIPs into your own testbench.
</div>

### Optional: Try the APB example

KVIPS APB VIP supports APB3 and APB4 in a **single compiled image** with a runtime switch:

```bash
make -C kvips/apb/examples list-tests
make -C kvips/apb/examples questa TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB4'
make -C kvips/apb/examples questa TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB3'
```

---

## 📦 Repository Structure

Understanding the KVIPS organization:

```
kvips/
├── common/                    # Shared utilities and macros
│   └── sv/
│       ├── kvips_macros.svh  # Common macro definitions
│       └── kvips_wave_dump.svh # Waveform control
├── axi4/                      # AXI4 Full VIP
│   ├── sv/                    # SystemVerilog source
│   │   ├── if/               # Interface definitions
│   │   ├── pkg/              # UVM packages
│   │   ├── uvm/              # UVM components
│   │   └── assertions/       # SVA checkers
│   ├── docs/                  # VIP-specific documentation
│   │   ├── user_guide.md
│   │   ├── integration_guide.md
│   │   ├── supported_features.md
│   │   └── assertions.md
│   └── examples/              # Working examples
│       └── uvm_back2back/
│           ├── tb/           # Testbench code
│           └── sim/          # Simulation scripts
├── apb/                       # APB3/APB4 VIP (beta)
│   ├── sv/
│   ├── docs/
│   └── examples/
└── README.md                  # Repository overview
```

---

## 🔧 Basic Integration

Follow these steps to integrate a KVIPS VIP into your existing testbench:

### 1. Add to Compilation

Add KVIPS to your filelist or compile script:

```tcl
# Questa example (compile.do)
# Common utilities
+incdir+${KVIPS_ROOT}/common/sv

# AXI4 VIP
+incdir+${KVIPS_ROOT}/axi4/sv/if
+incdir+${KVIPS_ROOT}/axi4/sv/uvm
vlog -sv ${KVIPS_ROOT}/axi4/sv/pkg/axi4_types_pkg.sv
vlog -sv ${KVIPS_ROOT}/axi4/sv/pkg/axi4_uvm_pkg.sv
vlog -sv ${KVIPS_ROOT}/axi4/sv/if/axi4_if.sv
```

Or using a `.f` file:

```
+incdir+${KVIPS_ROOT}/common/sv
+incdir+${KVIPS_ROOT}/axi4/sv/if
+incdir+${KVIPS_ROOT}/axi4/sv/uvm

${KVIPS_ROOT}/axi4/sv/pkg/axi4_types_pkg.sv
${KVIPS_ROOT}/axi4/sv/pkg/axi4_uvm_pkg.sv
${KVIPS_ROOT}/axi4/sv/if/axi4_if.sv
```

### 2. Instantiate Interface

In your top-level testbench module:

```systemverilog
module tb_top;
  // Clock and reset
  logic clk = 0;
  logic rst_n = 0;
  
  always #5 clk = ~clk; // 100MHz clock
  
  initial begin
    rst_n = 0;
    #100;
    rst_n = 1;
  end
  
  // Instantiate AXI4 interface
  axi4_if #(
    .ADDR_W(32),
    .DATA_W(64),
    .ID_W(4),
    .USER_W(1)
  ) axi_if (
    .aclk(clk),
    .areset_n(rst_n)
  );
  
  // Connect to your DUT
  your_dut dut (
    .axi_awid    (axi_if.awid),
    .axi_awaddr  (axi_if.awaddr),
    .axi_awvalid (axi_if.awvalid),
    .axi_awready (axi_if.awready),
    // ... other AXI signals
  );
  
  // Pass interface to UVM
  initial begin
    uvm_config_db#(virtual axi4_if#(32,64,4,1))::set(
      null, "uvm_test_top.env.axi_agent*", "vif", axi_if
    );
    run_test();
  end
endmodule
```

### 3. Configure Agent

In your UVM test or base test:

```systemverilog
class my_base_test extends uvm_test;
  `uvm_component_utils(my_base_test)
  
  axi4_env#(32, 64, 4, 1) axi_env;
  axi4_env_cfg#(32, 64, 4, 1) env_cfg;
  
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
  
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    // Create environment configuration
    env_cfg = axi4_env_cfg#(32, 64, 4, 1)::type_id::create("env_cfg");
    
    // Configure master agent
    begin
      axi4_agent_cfg#(32, 64, 4, 1) mst_cfg;
      mst_cfg = axi4_agent_cfg#(32, 64, 4, 1)::type_id::create("mst_cfg");
      mst_cfg.is_master = 1;
      mst_cfg.is_active = UVM_ACTIVE;
      mst_cfg.trace_enable = 0;
      env_cfg.agent_cfgs.push_back(mst_cfg);
    end
    
    // Set configuration
    uvm_config_db#(axi4_env_cfg#(32, 64, 4, 1))::set(
      this, "axi_env*", "cfg", env_cfg
    );
    
    // Create environment
    axi_env = axi4_env#(32, 64, 4, 1)::type_id::create("axi_env", this);
  endfunction
  
  task run_phase(uvm_phase phase);
    // Environment is ready - start your sequences!
    phase.raise_objection(this);
    #1000ns;
    phase.drop_objection(this);
  endtask
endclass
```

### 4. Write Sequences

Create sequences to drive transactions:

```systemverilog
class my_test_seq extends uvm_sequence#(axi4_item#(32, 64, 4, 1));
  `uvm_object_utils(my_test_seq)
  
  function new(string name = "my_test_seq");
    super.new(name);
  endfunction
  
  task body();
    axi4_item#(32, 64, 4, 1) item;
    
    // Write transaction
    `uvm_do_with(item, {
      is_write == 1;
      addr == 32'h1000;
      len == 0;  // Single beat
      size == 3; // 8 bytes
      data[0] == 64'hDEAD_BEEF_CAFE_BABE;
    })
    
    // Read transaction
    `uvm_do_with(item, {
      is_write == 0;
      addr == 32'h1000;
      len == 0;
      size == 3;
    })
  endtask
endclass
```

---

## ⚙️ Configuration Options

### Common Plusargs

| Plusarg | Description | Example |
|---------|-------------|---------|
| `+UVM_TESTNAME=<test>` | Specify UVM test to run | `+UVM_TESTNAME=axi4_b2b_test` |
| `+UVM_VERBOSITY=<level>` | Set UVM verbosity | `+UVM_VERBOSITY=UVM_HIGH` |
| `+VIP_TRACE` | Enable VIP transaction tracing | `+VIP_TRACE` |
| `+VIP_STATS` | Enable performance statistics | `+VIP_STATS` |
| `+VIP_TR` | Enable UVM transaction recording | `+VIP_TR` |
| `+KVIPS_WAVES` | Dump waveforms | `+KVIPS_WAVES` |

### AXI4-Specific Plusargs

| Plusarg | Description |
|---------|-------------|
| `+KVIPS_AXI4_ASSERT_OFF` | Disable all AXI4 assertions |
| `+KVIPS_AXI4_ASSERT_KNOWN` | Enable X/Z value checks |
| `+KVIPS_AXI4_SB_OFF` | Disable scoreboard |
| `+VIP_PIPE` | Enable pipelined master mode |
| `+VIP_MAX_OUTS=<n>` | Set max outstanding transactions |

---

## 🎯 Next Steps

Now that you have KVIPS running, explore these resources:

<div class="grid grid-2">
<div class="card">
<h3>📖 VIP Documentation</h3>
<ul>
<li><a href="/vips/axi4/">AXI4 User Guide</a></li>
<li><a href="/docs/axi4/api/">API Reference</a></li>
<li><a href="/docs/axi4/integration/">Integration Guide</a></li>
</ul>
</div>

<div class="card">
<h3>🔧 Advanced Topics</h3>
<ul>
<li><a href="/docs/best-practices/">Best Practices</a></li>
<li><a href="/docs/debugging/">Debugging Tips</a></li>
<li><a href="/docs/performance/">Performance Tuning</a></li>
</ul>
</div>
</div>

---

## 🆘 Troubleshooting

### Common Issues

<details>
<summary><strong>Compilation errors with include paths</strong></summary>

**Solution:** Ensure `+incdir+` paths are set correctly:
```bash
+incdir+${KVIPS_ROOT}/common/sv
+incdir+${KVIPS_ROOT}/axi4/sv/if
+incdir+${KVIPS_ROOT}/axi4/sv/uvm
```
</details>

<details>
<summary><strong>Virtual interface is null</strong></summary>

**Solution:** Check that you're setting the interface in config DB before creating agents:
```systemverilog
uvm_config_db#(virtual axi4_if#(...))::set(null, "*.axi_agent*", "vif", axi_if);
```
</details>

<details>
<summary><strong>Simulation hangs</strong></summary>

**Solution:** Check for:
- Missing handshakes (VALID/READY not driven)
- Clock/reset issues
- Insufficient timeout values
</details>

### Getting Help

- 📚 [FAQ](/docs/faq/)
- 🐛 [Issue Tracker](https://github.com/kiranreddi/kvips/issues)
- 💬 [Discussions](https://github.com/kiranreddi/kvips/discussions)

---

## 📝 License

KVIPS is released under the MIT License. See [LICENSE](https://github.com/kiranreddi/kvips/blob/main/LICENSE) for details.

<div class="alert alert-success" style="margin-top: 2rem;">
<strong>🎉 You're all set!</strong> Start building robust verification environments with KVIPS. If you have questions or feedback, please open an issue on GitHub.
</div>
