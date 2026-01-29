---
layout: default
title: Best Practices
permalink: /docs/best-practices/
---

# Best Practices for KVIPS VIPs

This guide presents recommended practices for using KVIPS verification IPs effectively.

---

## 🏗️ Testbench Architecture

### Recommended Structure

```systemverilog
class my_env extends uvm_env;
  // VIP environments
  axi4_env#(32, 64, 4, 1) axi_master_env;
  axi4_env#(32, 64, 4, 1) axi_slave_env;
  
  // DUT-specific components
  my_scoreboard scoreboard;
  my_coverage_collector coverage;
  
  // Configuration
  my_env_cfg cfg;
  
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    // Create VIP envs with proper config
    if (!uvm_config_db#(my_env_cfg)::get(this, "", "cfg", cfg))
      `uvm_fatal(get_type_name(), "Missing cfg")
    
    // Configure and create VIPs
    axi_master_env = axi4_env#(32, 64, 4, 1)::type_id::create("axi_master_env", this);
    axi_slave_env = axi4_env#(32, 64, 4, 1)::type_id::create("axi_slave_env", this);
    
    // Create DUT-specific components
    scoreboard = my_scoreboard::type_id::create("scoreboard", this);
    coverage = my_coverage_collector::type_id::create("coverage", this);
  endfunction
  
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    
    // Connect VIP analysis ports to your components
    axi_master_env.analysis_port.connect(scoreboard.axi_export);
    axi_master_env.analysis_port.connect(coverage.axi_export);
  endfunction
endclass
```

### Configuration Best Practices

**✅ DO:**
- Create configuration objects early in build_phase
- Use config_db to pass configurations hierarchically
- Document all configuration knobs
- Provide sensible defaults

**❌ DON'T:**
- Hardcode addresses or timing values
- Skip validation of configuration parameters
- Modify configuration after component creation

---

## 🎮 Sequence Development

### Layered Sequences

```systemverilog
// Layer 1: Protocol-level (provided by VIP)
class axi4_basic_write_seq extends uvm_sequence;
  // Low-level AXI4 transaction
endclass

// Layer 2: Application-level
class write_register_seq extends uvm_sequence;
  rand logic [31:0] reg_addr;
  rand logic [31:0] reg_data;
  
  task body();
    axi4_basic_write_seq axi_seq;
    axi_seq = new("axi_seq");
    axi_seq.addr = reg_addr;
    axi_seq.data[0] = {32'h0, reg_data};
    axi_seq.start(p_sequencer);
  endtask
endclass

// Layer 3: Test-level
class configure_dut_seq extends uvm_sequence;
  task body();
    write_register_seq wr_seq;
    
    // Write configuration registers
    `uvm_do_with(wr_seq, {
      reg_addr == 32'h0; 
      reg_data == 32'h1;  // Enable
    })
    
    `uvm_do_with(wr_seq, {
      reg_addr == 32'h4;
      reg_data == 32'hFF;  // Set threshold
    })
  endtask
endclass
```

### Sequence Reusability

```systemverilog
// Good: Parameterized, reusable sequence
class generic_burst_seq #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W = 4,
  int USER_W = 1
) extends uvm_sequence #(axi4_item#(ADDR_W, DATA_W, ID_W, USER_W));
  
  rand logic [ADDR_W-1:0] base_addr;
  rand int unsigned num_bursts;
  rand axi4_burst_e burst_type;
  
  constraint c_reasonable {
    num_bursts inside {[1:100]};
    burst_type inside {AXI4_BURST_INCR, AXI4_BURST_WRAP};
  }
  
  task body();
    for (int i = 0; i < num_bursts; i++) begin
      `uvm_do_with(req, {
        addr == base_addr + i * 64;
        burst == burst_type;
        len inside {[0:15]};
      })
    end
  endtask
endclass
```

---

## 🔍 Debugging Strategies

### Enabling Debug Features

```systemverilog
// In your test or env
function void build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  // Enable VIP tracing
  if ($test$plusargs("VIP_DEBUG")) begin
    cfg.axi_master_cfg.trace_enable = 1;
    cfg.axi_slave_cfg.trace_enable = 1;
    cfg.axi_master_cfg.stats_enable = 1;
  end
  
  // Adjust UVM verbosity for specific components
  uvm_config_db#(int)::set(this, "axi_master_env.agent.driver", 
    "recording_detail", UVM_FULL);
endfunction
```

### Systematic Debug Approach

1. **Reproduce the issue**
   ```bash
   # Run with fixed seed
   vsim +UVM_TESTNAME=my_test +ntb_random_seed=12345
   ```

2. **Enable targeted verbosity**
   ```bash
   # Specific component
   +uvm_set_verbosity=*driver*,UVM_DEBUG,time,100ns
   
   # All VIP components
   +VIP_TRACE +UVM_VERBOSITY=UVM_HIGH
   ```

3. **Use waveforms selectively**
   ```systemverilog
   initial begin
     if ($test$plusargs("DUMP_WAVES")) begin
       $dumpfile("debug.vcd");
       $dumpvars(0, tb_top.axi_if);  // Only AXI interface
     end
   end
   ```

4. **Add temporal assertions**
   ```systemverilog
   // Temporary debug assertion
   property p_debug_addr_range;
     @(posedge clk) (awvalid && awready) |-> (awaddr inside {[32'h1000:32'h2000]});
   endproperty
   assert property (p_debug_addr_range) else
     `uvm_error("DEBUG", $sformatf("Unexpected address: 0x%0h", awaddr))
   ```

---

## ✅ Assertions & Checkers

### Complementary DUT Assertions

Add DUT-specific assertions that complement VIP assertions:

```systemverilog
// VIP checks protocol
// You check DUT-specific behavior

module my_dut (
  axi4_if.slave axi_s,
  // ...
);

  // Check DUT-specific requirement
  property p_dut_response_time;
    logic [3:0] local_id;
    @(posedge axi_s.aclk) disable iff (!axi_s.areset_n)
    (axi_s.arvalid && axi_s.arready, local_id = axi_s.arid) |->
      ##[1:20] (axi_s.rvalid && (axi_s.rid == local_id));
  endproperty
  
  assert property (p_dut_response_time) else
    $error("DUT response timeout");
    
  // Check DUT state machine
  property p_dut_state_transition;
    @(posedge clk) (state == IDLE && start) |=> (state == ACTIVE);
  endproperty
  
  assert property (p_dut_state_transition) else
    $error("Invalid state transition");
    
endmodule
```

---

## 📊 Coverage Strategy

### Protocol Coverage

```systemverilog
class axi4_coverage_collector extends uvm_subscriber #(axi4_item);
  
  covergroup cg_axi4_protocol;
    cp_burst_type: coverpoint item.burst {
      bins incr = {AXI4_BURST_INCR};
      bins fixed = {AXI4_BURST_FIXED};
      bins wrap = {AXI4_BURST_WRAP};
    }
    
    cp_burst_size: coverpoint item.size {
      bins byte_xfer = {0};
      bins halfword = {1};
      bins word = {2};
      bins dword = {3};
    }
    
    cp_burst_len: coverpoint item.len {
      bins single = {0};
      bins short_burst = {[1:3]};
      bins medium_burst = {[4:15]};
      bins long_burst = {[16:255]};
    }
    
    // Cross coverage
    cx_burst_type_size: cross cp_burst_type, cp_burst_size;
    cx_burst_type_len: cross cp_burst_type, cp_burst_len;
    
    // Interesting corners
    cp_4kb_boundary: coverpoint item.addr[11:0] {
      bins near_boundary = {[12'hF00:12'hFFF]};
    }
    
    cp_narrow_transfer: coverpoint (item.size < $clog2(DATA_W/8)) {
      bins narrow = {1};
      bins full_width = {0};
    }
  endgroup
  
  function new(string name, uvm_component parent);
    super.new(name, parent);
    cg_axi4_protocol = new();
  endfunction
  
  function void write(axi4_item t);
    item = t;
    cg_axi4_protocol.sample();
  endfunction
endclass
```

### DUT-Specific Coverage

```systemverilog
covergroup cg_dut_scenarios @(posedge clk);
  // Cover interesting DUT states
  cp_dut_state: coverpoint dut.state {
    bins reset = {RESET};
    bins idle = {IDLE};
    bins active = {ACTIVE};
    bins error = {ERROR};
    bins states[] = {RESET, IDLE, ACTIVE, ERROR};
  }
  
  // Cover state transitions
  cp_state_trans: coverpoint dut.state {
    bins reset_to_idle = (RESET => IDLE);
    bins idle_to_active = (IDLE => ACTIVE);
    bins active_to_idle = (ACTIVE => IDLE);
    bins any_to_error = (RESET, IDLE, ACTIVE => ERROR);
  }
  
  // Cover backpressure scenarios
  cp_backpressure: coverpoint dut.fifo_full {
    bins not_full = {0};
    bins full = {1};
  }
  
  // Cover interesting combinations
  cx_state_backpressure: cross cp_dut_state, cp_backpressure;
endgroup
```

---

## ⚡ Performance Optimization

### Simulation Speed

```systemverilog
// Optimize for simulation speed

// 1. Use `uvm_field_*` macros judiciously
class my_txn extends uvm_sequence_item;
  rand logic [31:0] addr;
  rand logic [63:0] data;
  
  // DON'T use field macros for large arrays if not needed
  // `uvm_field_array_int(big_array, UVM_DEFAULT)
  
  // DO implement do_copy, do_compare manually for critical paths
  function void do_copy(uvm_object rhs);
    my_txn rhs_;
    if (!$cast(rhs_, rhs)) return;
    addr = rhs_.addr;
    data = rhs_.data;
  endfunction
endclass

// 2. Disable unnecessary checks
initial begin
  // In regression mode
  if ($test$plusargs("REGRESSION")) begin
    // Disable expensive assertions
    $assertoff(0, tb_top.expensive_assertion);
    
    // Reduce UVM verbosity
    uvm_top.set_report_verbosity_level_hier(UVM_LOW);
  end
end

// 3. Use pipelined mode for throughput
cfg.master_pipelined = 1;
cfg.max_outstanding_writes = 16;
cfg.max_outstanding_reads = 16;

// 4. Minimize inter-transaction gaps
cfg.inter_txn_gap_min = 0;
cfg.inter_txn_gap_max = 0;
```

### Memory Management

```systemverilog
// For large memory spaces
class sparse_memory;
  // Use associative array instead of unpacked array
  bit [7:0] mem [logic [31:0]];  // Only allocates used addresses
  
  // DON'T do this for large spaces:
  // bit [7:0] mem [0:32'hFFFF_FFFF];  // Would allocate 4GB!
  
  function void write_byte(logic [31:0] addr, logic [7:0] data);
    mem[addr] = data;
  endfunction
  
  function logic [7:0] read_byte(logic [31:0] addr);
    if (!mem.exists(addr)) begin
      `uvm_warning("MEM", $sformatf("Reading uninitialized address 0x%0h", addr))
      return 8'h00;
    end
    return mem[addr];
  endfunction
endclass
```

---

## 🔒 Regression Testing

### Test Organization

```bash
# tests_questa.list
axi4_basic_test              +ntb_random_seed=1
axi4_burst_test              +ntb_random_seed=2
axi4_outstanding_test        +ntb_random_seed=3
axi4_exclusive_test          +ntb_random_seed=4
axi4_error_inject_test       +ntb_random_seed=5
axi4_stress_test             +ntb_random_seed=6 +iterations=1000

# Add corner cases
axi4_basic_test              +ntb_random_seed=100  # Different seed
axi4_wrap_burst_test         +ntb_random_seed=7
axi4_4kb_boundary_test       +ntb_random_seed=8
axi4_narrow_transfer_test    +ntb_random_seed=9
axi4_max_burst_test          +ntb_random_seed=10
```

### Regression Script

```bash
#!/bin/bash
# regress.sh

TEST_LIST="tests_questa.list"
LOG_DIR="regression_logs"
mkdir -p $LOG_DIR

PASS=0
FAIL=0

while IFS= read -r line; do
  # Skip comments and empty lines
  [[ $line =~ ^#.*$ ]] && continue
  [[ -z "$line" ]] && continue
  
  # Parse test and plusargs
  TEST_NAME=$(echo $line | awk '{print $1}')
  PLUSARGS=$(echo $line | cut -d' ' -f2-)
  
  echo "Running: $TEST_NAME $PLUSARGS"
  
  # Run test
  ./run_questa.sh +UVM_TESTNAME=$TEST_NAME $PLUSARGS > $LOG_DIR/$TEST_NAME.log 2>&1
  
  # Check result
  if grep -q "UVM_ERROR\s*:\s*0" $LOG_DIR/$TEST_NAME.log && \
     grep -q "UVM_FATAL\s*:\s*0" $LOG_DIR/$TEST_NAME.log; then
    echo "  PASS"
    ((PASS++))
  else
    echo "  FAIL"
    ((FAIL++))
  fi
done < "$TEST_LIST"

echo ""
echo "================="
echo "Regression Summary"
echo "================="
echo "PASS: $PASS"
echo "FAIL: $FAIL"
echo "Total: $((PASS + FAIL))"

[[ $FAIL -eq 0 ]] && exit 0 || exit 1
```

---

## 📝 Documentation

### Self-Documenting Code

```systemverilog
/// Configure AXI4 master for high-throughput operation
///
/// This function configures the master agent for maximum bandwidth
/// by enabling pipelined mode and setting generous outstanding limits.
///
/// @param cfg - Agent configuration object to modify
/// @param max_outs - Maximum outstanding transactions (default: 16)
function automatic void configure_high_throughput(
  ref axi4_agent_cfg cfg,
  input int unsigned max_outs = 16
);
  cfg.master_pipelined = 1;
  cfg.max_outstanding_writes = max_outs;
  cfg.max_outstanding_reads = max_outs;
  cfg.master_aw_delay_min = 0;
  cfg.master_aw_delay_max = 0;
  cfg.master_ar_delay_min = 0;
  cfg.master_ar_delay_max = 0;
  cfg.inter_txn_gap_min = 0;
  cfg.inter_txn_gap_max = 0;
endfunction
```

---

## Summary Checklist

✅ **Architecture**
- [ ] VIP environments properly instantiated
- [ ] Configuration objects created early
- [ ] Analysis ports connected correctly
- [ ] Hierarchical configuration used

✅ **Sequences**
- [ ] Layered sequence approach
- [ ] Reusable sequences
- [ ] Constrained random where appropriate
- [ ] Deterministic scenarios covered

✅ **Debug**
- [ ] Trace knobs documented
- [ ] Systematic debug approach
- [ ] Selective waveform dumping
- [ ] Temporal assertions for debug

✅ **Coverage**
- [ ] Protocol coverage defined
- [ ] DUT-specific coverage added
- [ ] Cross-coverage for interactions
- [ ] Corner cases covered

✅ **Performance**
- [ ] Simulation speed optimized
- [ ] Memory usage considered
- [ ] Pipelined mode for throughput
- [ ] Regression runs clean

---

<div style="text-align: center; margin-top: 3rem;">
<p><strong>Have questions or suggestions?</strong></p>
<p><a href="https://github.com/kiranreddi/kvips/discussions">Join the Discussion</a></p>
</div>
