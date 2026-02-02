# PCIe VIP Plan (Roadmap Draft)

This document is a forward-looking plan. It describes intended capabilities; it is **not** a guarantee of what is currently implemented.

For the current “what actually exists” status, see `kvips/pcie/docs/supported_features.md` and `kvips/pcie/docs/user_guide.md`.

## Table of Contents
1. [Overview](#1-overview)
2. [Quick Start](#2-quick-start)
3. [Configuration](#3-configuration)
4. [Agent Modes](#4-agent-modes)
5. [Interface Modes](#5-interface-modes)
6. [Running Simulations](#6-running-simulations)
7. [Sequences](#7-sequences)
8. [Scoreboard](#8-scoreboard)
9. [Coverage](#9-coverage)
10. [Debug Features](#10-debug-features)
11. [Error Injection](#11-error-injection)
12. [Performance Tuning](#12-performance-tuning)

---

## 1. Overview

This document describes the **target end-state** for a vendor-neutral PCIe VIP (Gen1–Gen6). It is a roadmap; implementation is incremental.

For current status, see:
- `kvips/pcie/docs/supported_features.md`
- `kvips/pcie/docs/user_guide.md`

- **Root Complex (RC)** and **Endpoint (EP)** agents
- **PIPE interface** and **Serial interface** modes
- Full LTSSM implementation
- All TLP types support
- Protocol assertions at PHY/DLL/TL layers
- UVM-compliant architecture
- Functional coverage models

### Supported Features
- PCIe Base Specification 5.0 (Gen5) and 6.0 (Gen6)
- Link widths x1, x2, x4, x8, x12, x16, x32
- 8b/10b encoding (Gen1/2)
- 128b/130b encoding (Gen3/4/5)
- FLIT mode (Gen6)
- Full link training and equalization
- Power management (ASPM L0s, L1, L1 Substates)
- All TLP types (Memory, IO, Config, Message, Completion)
- MSI/MSI-X interrupts
- Advanced Error Reporting (AER)
- Virtual Channels (VC0-VC7)

---

## 2. Quick Start (Current Example)

### 2.1 Prerequisites
- SystemVerilog simulator (Questa/VCS/Xcelium)
- UVM 1.1d or 1.2 library
- KVIPS repository cloned

### 2.2 Run Back-to-Back Demo

```bash
# Navigate to examples directory
cd kvips/pcie/examples/uvm_back2back/sim

# Run with Questa
./run_questa.sh +UVM_TESTNAME=pcie_b2b_smoke_test

# Run with VCS
./run_vcs.sh +UVM_TESTNAME=pcie_b2b_smoke_test

# Run with Xcelium
./run_xcelium.sh +UVM_TESTNAME=pcie_b2b_smoke_test
```

### 2.3 Run with Specific Configuration (Roadmap)

```bash
# The following are examples of the *intended* UX once plusarg plumbing exists:
# ./run_questa.sh +UVM_TESTNAME=pcie_b2b_mem_test +PCIE_GEN=4 +PCIE_LANES=8

# Enable transaction tracing
# ./run_questa.sh +UVM_TESTNAME=pcie_b2b_smoke_test +VIP_TRACE

# Disable assertions
# ./run_questa.sh +UVM_TESTNAME=pcie_b2b_smoke_test +KVIPS_PCIE_ASSERT_OFF
```

---

## 3. Configuration

### 3.1 Configuration Object (Current)

The current implementation uses `pcie_cfg`:

```systemverilog
pcie_cfg cfg = pcie_cfg::type_id::create("cfg");

// Set agent mode
cfg.agent_mode = PCIE_RC;  // or PCIE_EP / PCIE_MONITOR

// Select interface mode
cfg.if_mode = PCIE_PIPE_MODE; // or PCIE_SERIAL_MODE

// Link parameters (draft; example uses PIPE defaults)
cfg.target_gen = PCIE_GEN4;
cfg.target_width = PCIE_X4;

// Note: PCIe “device identification” and most protocol behaviors are roadmap items.
cfg.msi_enable = 1;
cfg.aer_enable = 1;

// Configure via UVM config_db
uvm_config_db#(pcie_agent_cfg)::set(this, "env.agent*", "cfg", cfg);
```

### 3.2 Key Configuration Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `agent_mode` | enum | `PCIE_RC` | RC, EP, or MONITOR |
| `if_mode` | enum | `PCIE_PIPE_MODE` | PIPE or SERIAL interface |
| `target_gen` | enum | `PCIE_GEN4` | Target link speed |
| `target_width` | enum | `PCIE_X4` | Target link width |
| `max_payload_size` | int | 2 | Max payload (0=128B, 5=4KB) |
| `supports_extended_tag` | bit | 1 | Draft config field (roadmap behavior) |
| `supports_10bit_tag` | bit | 1 | Draft config field (roadmap behavior) |
| `inject_ecrc_error` | bit | 0 | Error injection knob (roadmap behavior) |

### 3.3 Runtime Plusargs

Plusarg parsing is a **roadmap** item; the current example does not implement these switches yet.

| Plusarg | Description |
|---------|-------------|
| `+PCIE_GEN=<1-6>` | Set target generation |
| `+PCIE_LANES=<1-32>` | Set number of lanes |
| `+PCIE_WIDTH=<1,2,4,8,16,32>` | Set link width |
| `+PCIE_MAX_PAYLOAD=<128-4096>` | Max payload size |
| `+VIP_TRACE` | Enable verbose tracing |
| `+VIP_TR` | Enable transaction recording |
| `+VIP_STATS` | Enable statistics |
| `+VIP_COV` | Enable coverage |

---

## 4. Agent Modes

### 4.1 Root Complex (RC) Mode

The RC agent acts as the host initiating transactions:
- Performs bus enumeration
- Initiates memory/IO/config read/write
- Generates completions for EP requests
- Manages flow control credits

```systemverilog
cfg.agent_mode = PCIE_RC;
cfg.bus_num = 8'h00;
cfg.device_num = 5'h00;
cfg.function_num = 3'h0;
```

### 4.2 Endpoint (EP) Mode

The EP agent acts as a device responding to RC:
- Responds to configuration accesses
- Handles memory/IO transactions to BARs
- Generates MSI/MSI-X interrupts
- Can initiate DMA (bus master) transactions

```systemverilog
cfg.agent_mode = PCIE_EP;
cfg.bar_enable = 6'b000011;
cfg.bar_size[0] = 32'h0001_0000;  // 64KB BAR0
cfg.bar_size[1] = 32'h0010_0000;  // 1MB BAR1
```

### 4.3 Monitor Mode

Passive monitoring without driving:

```systemverilog
cfg.agent_mode = PCIE_MONITOR;
cfg.is_active = UVM_PASSIVE;
```

---

## 5. Interface Modes

### 5.1 PIPE Interface Mode

Connects at the MAC-PHY boundary using Intel PIPE specification:

```systemverilog
cfg.if_mode = PCIE_PIPE_MODE;

// In testbench top:
pcie_pipe_if #(.NUM_LANES(16), .MAX_DATA_WIDTH(32)) pipe_if (
    .pclk(pclk),
    .reset_n(reset_n)
);

uvm_config_db#(virtual pcie_pipe_if)::set(null, "*", "pipe_vif", pipe_if);
```

**PIPE Interface Signals:**
- TxData/RxData: Parallel data bus
- TxDataK/RxDataK: K-character indication
- Rate: Link speed
- PowerDown: Power state
- PhyStatus: PHY completion status
- TxElecIdle/RxElecIdle: Electrical idle
- Equalization signals (Gen3+)
- Lane Margining signals (Gen4+)

### 5.2 Serial Interface Mode

Full SerDes with differential signaling:

```systemverilog
cfg.if_mode = PCIE_SERIAL_MODE;

// In testbench top:
pcie_serial_if #(.NUM_LANES(16)) serial_if (
    .refclk_p(refclk_p),
    .refclk_n(refclk_n),
    .reset_n(reset_n)
);

uvm_config_db#(virtual pcie_serial_if)::set(null, "*", "serial_vif", serial_if);
```

**Serial Interface Signals:**
- tx_p/tx_n: Differential transmit
- rx_p/rx_n: Differential receive
- tx_p1/tx_n1, rx_p1/rx_n1: PAM4 (Gen6)
- clkreq_n: Clock request
- perst_n: Fundamental reset
- wake_n: Wake signal

---

## 6. Running Simulations

### 6.1 Directory Structure for Runs

```
kvips/pcie/examples/uvm_back2back/
├── tb/
│   ├── top.sv              # Top module
│   ├── tb_pkg.sv           # TB package
├── sim/
│   ├── run_questa.sh       # Questa script
│   ├── run_vcs.sh          # VCS script
│   ├── run_xcelium.sh      # Xcelium script
│   ├── filelist.f          # Source files list
```

### 6.2 Single Test Run

```bash
# Smoke test (current)
./run_questa.sh +UVM_TESTNAME=pcie_b2b_smoke_test

# With seed
./run_questa.sh +UVM_TESTNAME=pcie_b2b_mem_test +ntb_random_seed=12345

# With verbosity
./run_questa.sh +UVM_TESTNAME=pcie_b2b_smoke_test +UVM_VERBOSITY=UVM_HIGH
```

### 6.3 Regression Run (Roadmap)

```bash
# A dedicated PCIe regression wrapper and `tests.list` are not implemented yet.
```

### 6.4 Waveform Dumping (Current)

```bash
# Use the KVIPS wave-dump include in the example TB:
# - `kvips/pcie/examples/uvm_back2back/tb/top.sv`
# - `kvips/common/sv/kvips_wave_dump.svh`
```

---

## 7. Sequences

### 7.1 Available Sequences (Roadmap)

The current implementation does not yet ship a sequence library for real PCIe traffic.
| `pcie_error_inject_seq` | Error injection |

### 7.2 Using Sequences

```systemverilog
class my_test extends pcie_base_test;
    
    task run_phase(uvm_phase phase);
        pcie_mem_write_seq wr_seq;
        pcie_mem_read_seq  rd_seq;
        
        phase.raise_objection(this);
        
        // Memory write
        wr_seq = pcie_mem_write_seq::type_id::create("wr_seq");
        wr_seq.address = 64'h0000_0001_0000_0000;
        wr_seq.length = 16;  // 16 DW = 64 bytes
        wr_seq.start(env.rc_agent.sequencer);
        
        // Memory read
        rd_seq = pcie_mem_read_seq::type_id::create("rd_seq");
        rd_seq.address = 64'h0000_0001_0000_0000;
        rd_seq.length = 16;
        rd_seq.start(env.rc_agent.sequencer);
        
        phase.drop_objection(this);
    endtask
    
endclass
```

### 7.3 Sequence Parameters

```systemverilog
// Memory sequence parameters
pcie_mem_write_seq seq;
seq.address = 64'hABCD_0000;
seq.length = 32;              // DW count
seq.first_dw_be = 4'b1111;
seq.last_dw_be = 4'b1111;
seq.tc = 0;                   // Traffic class
seq.attr = 2'b00;             // Attributes
seq.data = '{32'h1111_1111, 32'h2222_2222, ...};

// Config sequence parameters
pcie_cfg_read_seq cfg_seq;
cfg_seq.bus_num = 8'h01;
cfg_seq.device_num = 5'h00;
cfg_seq.func_num = 3'h0;
cfg_seq.reg_num = 6'h00;      // Vendor ID / Device ID
```

---

## 8. Scoreboard

### 8.1 Scoreboard Features

The `pcie_scoreboard` provides:
- TLP request/completion matching
- Data integrity checking
- Ordering rule verification
- Timeout detection
- Statistics collection

### 8.2 Scoreboard Configuration

```systemverilog
// Enable/disable via config
env_cfg.scoreboard_enable = 1;

// Or via plusarg
+KVIPS_PCIE_SB_OFF      // Disable scoreboard
+KVIPS_PCIE_SB_VERBOSE  // Verbose scoreboard output
```

### 8.3 Scoreboard Hooks

```systemverilog
// Custom scoreboard extension
class my_scoreboard extends pcie_scoreboard;
    
    function void check_tlp(pcie_tlp_item req, pcie_tlp_item cpl);
        super.check_tlp(req, cpl);
        // Add custom checks
    endfunction
    
endclass
```

---

## 9. Coverage

### 9.1 Coverage Groups

| Coverage Group | Description |
|----------------|-------------|
| `cg_tlp_types` | All TLP type coverage |
| `cg_link_speed` | Link speed transitions |
| `cg_link_width` | Link width coverage |
| `cg_ltssm` | LTSSM state coverage |
| `cg_power_mgmt` | Power state coverage |
| `cg_error` | Error scenario coverage |
| `cg_flow_control` | FC credit coverage |

### 9.2 Enabling Coverage

```systemverilog
// Via configuration
cfg.coverage_enable = 1;

// Via plusarg
+VIP_COV
```

### 9.3 Coverage Reports

```bash
# Merge coverage
python3 scripts/coverage_merge.py --input sim/cov_* --output merged_cov

# Generate HTML report
vcover report -html merged_cov -output cov_html
```

---

## 10. Debug Features

### 10.1 Transaction Tracing

Enable detailed transaction logging:

```bash
+VIP_TRACE
```

Output example:
```
[VIP_TRACE] @1000ns RC_TX: MWr64 Addr=0x0000_0001_0000_0000 Len=16 Tag=0x00
[VIP_TRACE] @1050ns EP_RX: MWr64 Addr=0x0000_0001_0000_0000 Len=16 Tag=0x00
[VIP_TRACE] @1100ns RC_TX: MRd64 Addr=0x0000_0001_0000_0000 Len=16 Tag=0x01
[VIP_TRACE] @1150ns EP_TX: CplD ReqID=0000 Tag=0x01 Status=SC ByteCount=64
```

### 10.2 LTSSM State Tracing

```bash
+PCIE_LTSSM_TRACE
```

Output:
```
[LTSSM] @0ns State: DETECT_QUIET
[LTSSM] @100ns State: DETECT_ACTIVE -> Receiver detected
[LTSSM] @150ns State: POLLING_ACTIVE
[LTSSM] @300ns State: POLLING_CONFIGURATION
[LTSSM] @500ns State: CONFIG_LINKWIDTH_START
...
[LTSSM] @1000ns State: L0 -> Link up!
```

### 10.3 Transaction Recording

Enable UVM transaction recording:

```bash
+VIP_TR +UVM_TR_RECORD
```

### 10.4 Statistics

```bash
+VIP_STATS
```

Output:
```
============ PCIe VIP Statistics ============
Total TLPs Transmitted: 1234
Total TLPs Received:    1230
Memory Writes:          500
Memory Reads:           300
Completions:            300
Config Accesses:        134
Average Latency:        150ns
Max Outstanding:        32
Flow Control Stalls:    5
Replay Events:          2
=============================================
```

---

## 11. Error Injection

### 11.1 Supported Error Types

| Error Type | Description |
|------------|-------------|
| `ERR_ECRC` | ECRC error |
| `ERR_LCRC` | LCRC error |
| `ERR_SEQ_NUM` | Sequence number error |
| `ERR_MALFORMED_TLP` | Malformed TLP |
| `ERR_POISONED` | Poisoned TLP |
| `ERR_UNEXPECTED_CPL` | Unexpected completion |
| `ERR_TIMEOUT` | Completion timeout |
| `ERR_FC_PROTOCOL` | Flow control error |
| `ERR_DLLP_CRC` | DLLP CRC error |

### 11.2 Error Injection Usage

```systemverilog
// Via configuration
cfg.error_injection_enable = 1;
cfg.error_type = ERR_ECRC;
cfg.error_injection_rate = 5;  // 5% of TLPs

// Via sequence
pcie_error_inject_seq err_seq;
err_seq.error_type = ERR_LCRC;
err_seq.target_tag = 10'h05;
err_seq.start(env.rc_agent.sequencer);
```

### 11.3 Error Injection Plusargs

```bash
+PCIE_ERR_INJECT=ECRC      # Inject ECRC errors
+PCIE_ERR_RATE=10          # 10% injection rate
```

---

## 12. Performance Tuning

### 12.1 Simulation Speed

```systemverilog
// Reduce verbosity
cfg.trace_enable = 0;

// Disable unused features (current config field)
cfg.enable_coverage = 0;

// Use PIPE interface (faster than serial)
cfg.if_mode = PCIE_PIPE_MODE;
```

### 12.2 Memory Usage

```systemverilog
// Limit replay buffer
cfg.replay_buffer_size = 256;  // Minimum

// Limit outstanding transactions
cfg.max_outstanding = 32;
```

### 12.3 Assertion Performance

```bash
# Disable all assertions
# +KVIPS_PCIE_ASSERT_OFF

# Disable specific layer assertions
# +KVIPS_PCIE_ASSERT_PHY_OFF
# +KVIPS_PCIE_ASSERT_DLL_OFF
# +KVIPS_PCIE_ASSERT_TL_OFF
```

---

## Appendix A: Troubleshooting

### A.1 Common Issues

| Issue | Solution |
|-------|----------|
| Link doesn't train | Check reset sequencing, verify receiver detect |
| Completion timeout | Verify EP BAR configuration matches RC accesses |
| Flow control stall | Increase initial FC credits |
| LCRC errors | Check scrambler seed synchronization |

### A.2 Debug Checklist

1. Enable `+VIP_TRACE` and `+PCIE_LTSSM_TRACE`
2. Verify LTSSM reaches L0
3. Check flow control initialization completed
4. Verify addresses match BAR ranges
5. Check tag availability

---

## Appendix B: Protocol References

- PCI Express Base Specification, Rev. 5.0
- PCI Express Base Specification, Rev. 6.0
- Intel PIPE Specification, Rev. 4.4.1
- PCI Express Card Electromechanical Specification
