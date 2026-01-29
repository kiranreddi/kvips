---
layout: default
title: AXI4 Verification IP
permalink: /vips/axi4/
---

# AXI4 Full Protocol Verification IP

<div class="hero" style="padding: 2rem; margin: -2rem -2rem 2rem -2rem;">
<div style="max-width: 800px; margin: 0 auto;">
<h1 style="color: white; margin-bottom: 1rem;">AXI4 Full VIP</h1>
<p style="font-size: 1.25rem; color: rgba(255,255,255,0.95);">
Professional-grade AMBA AXI4 verification component with master/slave agents, protocol checkers, and built-in scoreboard
</p>
<div style="display: flex; gap: 0.5rem; flex-wrap: wrap; margin-top: 1.5rem;">
<span class="badge badge-success">Stable v1.0</span>
<span class="badge badge-info">UVM 1.1d/1.2</span>
<span class="badge badge-primary">IEEE 1800</span>
</div>
</div>
</div>

---

## 📋 Overview

The KVIPS AXI4 VIP provides a complete, production-ready verification environment for AMBA AXI4 (full) protocol. It includes:

<div class="grid grid-2" style="margin: 2rem 0;">
<div class="card">
<h3>🎯 Master Agent</h3>
<ul>
<li>Configurable address/data/ID/user widths</li>
<li>All burst types: INCR, FIXED, WRAP</li>
<li>Exclusive access support</li>
<li>Pipelined outstanding transactions</li>
<li>Configurable delays and backpressure</li>
</ul>
</div>

<div class="card">
<h3>🔄 Slave Agent</h3>
<ul>
<li>Flexible memory model</li>
<li>Error injection (SLVERR/DECERR)</li>
<li>Configurable response latencies</li>
<li>Exclusive reservation tracking</li>
<li>Address range mapping</li>
</ul>
</div>

<div class="card">
<h3>✅ Protocol Checkers</h3>
<ul>
<li>Handshake protocol validation</li>
<li>Burst legality checks</li>
<li>4KB boundary enforcement</li>
<li>Signal stability assertions</li>
<li>Exclusive access rules</li>
</ul>
</div>

<div class="card">
<h3>📊 Verification Features</h3>
<ul>
<li>Write-derived read scoreboard</li>
<li>Transaction recording (UVM TR)</li>
<li>Performance statistics</li>
<li>Configurable trace levels</li>
<li>Coverage collection hooks</li>
</ul>
</div>
</div>

---

## 🚀 Quick Start

### Minimal Example

```systemverilog
// 1. Instantiate interface
axi4_if #(.ADDR_W(32), .DATA_W(64), .ID_W(4)) axi_if(.aclk(clk), .areset_n(rst_n));

// 2. Configure and create environment
class my_test extends uvm_test;
  axi4_env#(32, 64, 4, 1) env;
  
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    // Create config
    axi4_env_cfg#(32, 64, 4, 1) cfg = axi4_env_cfg#(32, 64, 4, 1)::type_id::create("cfg");
    
    // Add master agent
    begin
      axi4_agent_cfg#(32, 64, 4, 1) mst_cfg = 
        axi4_agent_cfg#(32, 64, 4, 1)::type_id::create("mst_cfg");
      mst_cfg.is_master = 1;
      mst_cfg.is_active = UVM_ACTIVE;
      cfg.agent_cfgs.push_back(mst_cfg);
    end
    
    // Add slave agent with memory
    begin
      axi4_agent_cfg#(32, 64, 4, 1) slv_cfg = 
        axi4_agent_cfg#(32, 64, 4, 1)::type_id::create("slv_cfg");
      slv_cfg.is_master = 0;
      slv_cfg.is_active = UVM_ACTIVE;
      slv_cfg.slave_mem_enable = 1;
      cfg.agent_cfgs.push_back(slv_cfg);
    end
    
    uvm_config_db#(axi4_env_cfg#(32, 64, 4, 1))::set(this, "env", "cfg", cfg);
    env = axi4_env#(32, 64, 4, 1)::type_id::create("env", this);
  endfunction
endclass

// 3. Start sequences
axi4_basic_write_seq#(32, 64, 4, 1) seq = new("seq");
seq.start(env.get_master_sequencer(0));
```

### Run Example Simulation

```bash
# Questa
cd kvips/axi4/examples/uvm_back2back/sim
./run_questa.sh +UVM_TESTNAME=axi4_b2b_test

# VCS
./run_vcs.sh +UVM_TESTNAME=axi4_b2b_test

# Xcelium
./run_xcelium.sh +UVM_TESTNAME=axi4_b2b_test
```

---

## 📐 Architecture

### Component Hierarchy

```
axi4_env
├── axi4_agent (master)
│   ├── axi4_sequencer
│   ├── axi4_master_driver
│   └── axi4_monitor
├── axi4_agent (slave)
│   ├── axi4_sequencer
│   ├── axi4_slave_driver
│   └── axi4_monitor
├── axi4_scoreboard
└── axi4_txn_logger (optional)
```

### Data Flow

```
Sequence
   ↓
Sequencer → Driver → Interface → DUT/Slave
                         ↓
                     Monitor → Analysis Port → Scoreboard
                                            → Txn Logger
                                            → Coverage Collector
```

---

## ⚙️ Configuration

### Agent Configuration (`axi4_agent_cfg`)

```systemverilog
class axi4_agent_cfg #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends uvm_object;

  // Role Configuration
  bit                is_master = 1;        // Master or slave agent
  uvm_active_passive_enum is_active = UVM_ACTIVE;
  virtual axi4_if    vif;                  // Interface handle
  
  // Master Configuration
  bit                master_pipelined = 0; // Enable outstanding transactions
  int unsigned       max_outstanding_writes = 4;
  int unsigned       max_outstanding_reads = 4;
  int unsigned       master_aw_delay_min = 0;
  int unsigned       master_aw_delay_max = 5;
  int unsigned       master_ar_delay_min = 0;
  int unsigned       master_ar_delay_max = 5;
  int unsigned       master_w_beat_gap_min = 0;
  int unsigned       master_w_beat_gap_max = 3;
  bit                master_rready_random = 1;
  int unsigned       inter_txn_gap_min = 0;
  int unsigned       inter_txn_gap_max = 10;
  
  // Slave Configuration
  bit                slave_mem_enable = 0; // Enable internal memory model
  int unsigned       slave_read_latency_min = 1;
  int unsigned       slave_read_latency_max = 10;
  int unsigned       slave_write_latency_min = 1;
  int unsigned       slave_write_latency_max = 10;
  bit                slave_err_enable = 0; // Enable error injection
  logic [ADDR_W-1:0] slave_err_start = '0;
  logic [ADDR_W-1:0] slave_err_end = '0;
  axi4_resp_e        slave_err_resp = AXI4_RESP_SLVERR;
  bit                slave_err_on_write = 1;
  bit                slave_err_on_read = 1;
  bit                slave_exclusive_enable = 1; // Support exclusive access
  int unsigned       slave_exclusive_max_bytes = 128;
  
  // Debug/Observability
  bit                trace_enable = 0;     // Verbose transaction prints
  bit                stats_enable = 0;     // Collect performance stats
  bit                monitor_enable = 1;   // Enable monitor (disable for shared vif)
  
endclass
```

### Common Configuration Patterns

#### High-Performance Mode
```systemverilog
mst_cfg.master_pipelined = 1;
mst_cfg.max_outstanding_writes = 16;
mst_cfg.max_outstanding_reads = 16;
mst_cfg.master_aw_delay_min = 0;
mst_cfg.master_aw_delay_max = 0;
mst_cfg.master_w_beat_gap_min = 0;
mst_cfg.master_w_beat_gap_max = 0;
mst_cfg.inter_txn_gap_min = 0;
mst_cfg.inter_txn_gap_max = 0;
```

#### Stress Test Mode
```systemverilog
mst_cfg.master_aw_delay_min = 0;
mst_cfg.master_aw_delay_max = 20;
mst_cfg.master_w_beat_gap_min = 0;
mst_cfg.master_w_beat_gap_max = 10;
slv_cfg.slave_read_latency_min = 5;
slv_cfg.slave_read_latency_max = 50;
```

#### Debug Mode
```systemverilog
mst_cfg.trace_enable = 1;
mst_cfg.stats_enable = 1;
// Plus: +UVM_VERBOSITY=UVM_HIGH +VIP_TRACE +VIP_STATS
```

---

## 🎮 Sequence Library

### Basic Sequences

```systemverilog
// Single write
axi4_basic_write_seq #(32, 64, 4, 1) wr_seq;
wr_seq = new("wr_seq");
wr_seq.addr = 32'h1000;
wr_seq.data = 64'hDEADBEEF_CAFEBABE;
wr_seq.start(sequencer);

// Single read
axi4_basic_read_seq #(32, 64, 4, 1) rd_seq;
rd_seq = new("rd_seq");
rd_seq.addr = 32'h1000;
rd_seq.start(sequencer);

// Burst write (16 beats)
axi4_burst_write_seq #(32, 64, 4, 1) burst_seq;
burst_seq = new("burst_seq");
burst_seq.addr = 32'h2000;
burst_seq.len = 15;  // 16 beats
burst_seq.burst_type = AXI4_BURST_INCR;
burst_seq.start(sequencer);
```

### Advanced Sequences

```systemverilog
// Concurrent read/write
fork
  begin
    axi4_random_write_seq #(32, 64, 4, 1) wr_seq;
    wr_seq = new("wr_seq");
    wr_seq.num_txns = 100;
    wr_seq.start(sequencer);
  end
  begin
    axi4_random_read_seq #(32, 64, 4, 1) rd_seq;
    rd_seq = new("rd_seq");
    rd_seq.num_txns = 100;
    rd_seq.start(sequencer);
  end
join

// Exclusive access sequence
axi4_exclusive_seq #(32, 64, 4, 1) excl_seq;
excl_seq = new("excl_seq");
excl_seq.addr = 32'h4000;
excl_seq.start(sequencer);
// Internally: exclusive read -> exclusive write -> verify EXOKAY

// Error injection test
slv_cfg.slave_err_enable = 1;
slv_cfg.slave_err_start = 32'hF000;
slv_cfg.slave_err_end = 32'hFFFF;
slv_cfg.slave_err_resp = AXI4_RESP_SLVERR;
// Now reads/writes to 0xF000-0xFFFF will return SLVERR
```

### Custom Sequence Example

```systemverilog
class my_custom_seq extends uvm_sequence #(axi4_item#(32, 64, 4, 1));
  `uvm_object_utils(my_custom_seq)
  
  rand int num_bursts;
  constraint c_num { num_bursts inside {[10:50]}; }
  
  task body();
    for (int i = 0; i < num_bursts; i++) begin
      `uvm_do_with(req, {
        is_write == (i % 2 == 0);  // Alternate write/read
        addr[31:12] == i[19:0];    // Different 4KB pages
        len inside {[0:15]};        // Random burst length
        size == 3;                  // 8 bytes per beat
        burst == AXI4_BURST_INCR;
      })
    end
  endtask
endclass
```

---

## ✅ Assertions & Protocol Checking

### Built-in Assertions

The VIP includes comprehensive SVA checkers:

#### Handshake Protocol
```systemverilog
// AWVALID must remain high until AWREADY
property p_aw_valid_stable;
  @(posedge aclk) disable iff (!areset_n)
  (awvalid && !awready) |=> awvalid;
endproperty

// AWADDR must remain stable when AWVALID is high
property p_aw_stable;
  @(posedge aclk) disable iff (!areset_n)
  (awvalid && !awready) |=> $stable(awaddr);
endproperty
```

#### Burst Legality
```systemverilog
// INCR bursts: len 0-255
// FIXED/WRAP bursts: len 0-15
// WRAP bursts: len must be 1,3,7,15 (2,4,8,16 beats)
property p_burst_len_legal;
  @(posedge aclk) disable iff (!areset_n)
  (awvalid && awready) |-> 
    (awburst == 2'b01) ? (awlen <= 8'd255) : (awlen <= 8'd15);
endproperty
```

#### 4KB Boundary
```systemverilog
// Burst must not cross 4KB boundary
property p_no_4kb_cross;
  @(posedge aclk) disable iff (!areset_n)
  (awvalid && awready) |-> 
    ((awaddr[11:0] + (1 << awsize) * (awlen + 1)) <= 12'h1000);
endproperty
```

#### Exclusive Access
```systemverilog
// Exclusive write must have prior exclusive read with same ID
property p_exclusive_write_after_read;
  logic [ID_W-1:0] excl_id;
  @(posedge aclk) disable iff (!areset_n)
  (arvalid && arready && arlock, excl_id = arid) |->
    ##[1:$] (awvalid && awready && awlock && (awid == excl_id));
endproperty
```

### Runtime Control

```bash
# Disable all assertions
+KVIPS_AXI4_ASSERT_OFF

# Enable X/Z checking
+KVIPS_AXI4_ASSERT_KNOWN

# Disable specific assertion groups
+KVIPS_AXI4_ASSERT_BURST_OFF      # Disable burst legality checks
+KVIPS_AXI4_ASSERT_EXCL_OFF       # Disable exclusive access checks
```

---

## 📊 Scoreboard & Data Checking

### Write-Derived Read Checking

The built-in scoreboard implements memory-model checking:

1. **On Write:** Store data to internal memory
   ```systemverilog
   foreach (wr_txn.data[i]) begin
     for (int b = 0; b < STRB_W; b++) begin
       if (wr_txn.strb[i][b]) begin
         memory[addr + i*STRB_W + b] = wr_txn.data[i][b*8 +: 8];
       end
     end
   end
   ```

2. **On Read:** Compare against stored data
   ```systemverilog
   foreach (rd_txn.data[i]) begin
     for (int b = 0; b < STRB_W; b++) begin
       exp_byte = memory[addr + i*STRB_W + b];
       obs_byte = rd_txn.data[i][b*8 +: 8];
       if (exp_byte !== obs_byte) begin
         `uvm_error("AXI4_SB", $sformatf(
           "Data mismatch @ 0x%0h: exp=0x%0h obs=0x%0h",
           addr + i*STRB_W + b, exp_byte, obs_byte))
       end
     end
   end
   ```

### Configuration

```systemverilog
// Disable scoreboard
// Plusarg: +KVIPS_AXI4_SB_OFF

// Warn on reads of unwritten addresses
// Plusarg: +KVIPS_AXI4_SB_WARN_UNINIT
```

---

## 📈 Performance Statistics

Enable with `cfg.stats_enable = 1` or `+VIP_STATS`:

```
=== AXI4 Monitor Statistics ===
Observation period: 1000 ns

Write Statistics:
  Total write bursts:     50
  Total write beats:      800
  Write cycles:           1200
  Average latency:        5.2 cycles
  Peak bandwidth:         85%
  Max outstanding:        8

Read Statistics:
  Total read bursts:      50
  Total read beats:       800
  Read cycles:            1500
  Average latency:        7.8 cycles
  Peak bandwidth:         70%
  Max outstanding:        6

Stalls:
  AW stalls:              120 cycles (10%)
  W stalls:               200 cycles (16.7%)
  B backpressure:         50 cycles (4.2%)
  AR stalls:              150 cycles (10%)
  R backpressure:         300 cycles (20%)
```

---

## 🎓 Integration Examples

### Integrate with Existing Testbench

See [Integration Guide](/docs/axi4/integration/) for detailed steps.

### Multiple Agents

```systemverilog
class multi_master_test extends axi4_base_test;
  axi4_env#(32, 64, 4, 1) env;
  
  function void build_phase(uvm_phase phase);
    axi4_env_cfg#(32, 64, 4, 1) cfg = new("cfg");
    
    // Master 0
    begin
      axi4_agent_cfg#(32, 64, 4, 1) mst0_cfg = new("mst0_cfg");
      mst0_cfg.is_master = 1;
      // Set vif for master 0
      cfg.agent_cfgs.push_back(mst0_cfg);
    end
    
    // Master 1
    begin
      axi4_agent_cfg#(32, 64, 4, 1) mst1_cfg = new("mst1_cfg");
      mst1_cfg.is_master = 1;
      // Set vif for master 1
      cfg.agent_cfgs.push_back(mst1_cfg);
    end
    
    // Shared slave
    begin
      axi4_agent_cfg#(32, 64, 4, 1) slv_cfg = new("slv_cfg");
      slv_cfg.is_master = 0;
      slv_cfg.slave_mem_enable = 1;
      cfg.agent_cfgs.push_back(slv_cfg);
    end
    
    // ...
  endfunction
  
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    
    // Run sequences on both masters concurrently
    fork
      begin
        my_seq seq = new("seq0");
        seq.start(env.get_master_sequencer(0));
      end
      begin
        my_seq seq = new("seq1");
        seq.start(env.get_master_sequencer(1));
      end
    join
    
    phase.drop_objection(this);
  endtask
endclass
```

---

## 📚 Additional Resources

<div class="grid grid-2" style="margin: 2rem 0;">
<div class="card">
<h3>📖 Documentation</h3>
<ul>
<li><a href="/docs/axi4/user-guide/">User Guide</a></li>
<li><a href="/docs/axi4/api/">API Reference</a></li>
<li><a href="/docs/axi4/integration/">Integration Guide</a></li>
<li><a href="/docs/axi4/testplan/">Test Plan</a></li>
<li><a href="/docs/axi4/assertions/">Assertions</a></li>
</ul>
</div>

<div class="card">
<h3>🔧 Examples & Tools</h3>
<ul>
<li><a href="https://github.com/kiranreddi/kvips/tree/main/axi4/examples">Example Testbenches</a></li>
<li><a href="/docs/axi4/debug/">Debugging Guide</a></li>
<li><a href="/docs/axi4/performance/">Performance Tuning</a></li>
<li><a href="/docs/axi4/faq/">FAQ</a></li>
</ul>
</div>
</div>

---

## 🐛 Known Limitations

<div class="alert alert-warning">
<ul style="margin: 0;">
<li><strong>QoS:</strong> QoS fields are present but ordering is not enforced</li>
<li><strong>Cache:</strong> ARCACHE/AWCACHE checked but not modeled</li>
<li><strong>Regions:</strong> AWREGION/ARREGION supported but not actively used</li>
<li><strong>Low-power:</strong> CSYSREQ/CSYSACK not included</li>
</ul>
</div>

---

## 📜 License & Support

- **License:** MIT (see [LICENSE](https://github.com/kiranreddi/kvips/blob/main/LICENSE))
- **Issues:** [GitHub Issue Tracker](https://github.com/kiranreddi/kvips/issues)
- **Discussions:** [GitHub Discussions](https://github.com/kiranreddi/kvips/discussions)

<div style="text-align: center; margin-top: 3rem; padding: 2rem; background: linear-gradient(135deg, var(--primary-color) 0%, var(--secondary-color) 100%); border-radius: var(--radius-2xl); color: white;">
<h3 style="color: white; margin-bottom: 1rem;">Ready to use AXI4 VIP?</h3>
<p style="font-size: 1.125rem; margin-bottom: 1.5rem; color: rgba(255,255,255,0.95);">
Download KVIPS and start verifying your AXI4 designs today!
</p>
<a href="/docs/getting-started/" class="btn btn-secondary">Get Started</a>
</div>
