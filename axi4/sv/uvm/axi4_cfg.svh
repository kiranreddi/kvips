//------------------------------------------------------------------------------
// AXI4 Configuration
//------------------------------------------------------------------------------

`ifndef KVIPS_AXI4_CFG_SVH
`define KVIPS_AXI4_CFG_SVH

class axi4_agent_cfg #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends uvm_object;

  typedef virtual interface axi4_if #(ADDR_W, DATA_W, ID_W, USER_W) axi4_vif_t;

  axi4_vif_t vif;

  bit is_master = 1'b1;
  bit is_slave  = 1'b0;

  // Monitor enable (analysis + stats). Disable when multiple agents share the
  // same vif to avoid duplicate transaction capture.
  bit monitor_enable = 1'b1;

  bit trace_enable = 1'b0;

  // Transaction recording (UVM transaction viewing)
  bit    tr_record_enable = 1'b0;
  string tr_stream_name   = "kvips_axi4";

  // Master: allow multiple outstanding by accepting items early and returning
  // responses asynchronously via the sequencer response queue.
  bit          master_pipelined = 1'b0;
  int unsigned max_outstanding_reads  = 1;
  int unsigned max_outstanding_writes = 1;

  // Slave: response scheduling knobs
  bit          slave_reorder_b  = 1'b0;
  bit          slave_interleave_r = 1'b0;

  // Slave: exclusive access support (AXI4 AxLOCK)
  bit          slave_exclusive_enable    = 1'b1;
  int unsigned slave_exclusive_max_bytes = 128;

  // Master knobs
  int unsigned inter_txn_gap_min = 0;
  int unsigned inter_txn_gap_max = 0;
  int unsigned master_aw_delay_min = 0;
  int unsigned master_aw_delay_max = 0;
  int unsigned master_w_beat_gap_min = 0;
  int unsigned master_w_beat_gap_max = 0;
  int unsigned master_ar_delay_min = 0;
  int unsigned master_ar_delay_max = 0;
  bit          master_rready_random = 1'b0;
  int unsigned master_rready_low_min = 0;
  int unsigned master_rready_low_max = 5;

  // Slave knobs
  bit          slave_mem_enable = 1'b1;
  int unsigned slave_mem_bytes  = 64*1024;
  // Slave memory address mapping:
  // - The memory model is a byte array [0:slave_mem_bytes-1]
  // - Transactions index into it using (addr - slave_mem_base)
  // - Optionally wrap addresses modulo slave_mem_bytes
  longint unsigned slave_mem_base = 0;
  bit             slave_mem_wrap = 1'b0;

  // Slave: error-response injection (simple address-range based model).
  // If enabled and the transaction overlaps [slave_err_start, slave_err_end],
  // then the slave responds with slave_err_resp and does not update memory.
  bit          slave_err_enable  = 1'b0;
  bit          slave_err_on_read  = 1'b1;
  bit          slave_err_on_write = 1'b1;
  logic [ADDR_W-1:0] slave_err_start = '0;
  logic [ADDR_W-1:0] slave_err_end   = '0;
  axi4_resp_e   slave_err_resp   = AXI4_RESP_DECERR;

  int unsigned ready_min = 0;  // random-ready (per cycle) min delay
  int unsigned ready_max = 0;  // random-ready (per cycle) max delay
  int unsigned resp_min  = 0;  // response latency (cycles)
  int unsigned resp_max  = 0;

  // Timeouts (0 disables)
  int unsigned handshake_timeout_cycles = 100000;

  // Statistics
  bit stats_enable = 1'b0;
  int unsigned stats_window_cycles = 0; // 0 disables windowed reporting

  // Functional coverage (monitor-based)
  bit coverage_enable = 1'b0;

  function new(string name = "axi4_agent_cfg");
    super.new(name);
  endfunction

  function void apply_plusargs();
    int unsigned v;
    if ($value$plusargs("KVIPS_AXI4_COV=%d", v)) coverage_enable = (v != 0);
    if ($value$plusargs("KVIPS_COV=%d", v)) coverage_enable = (v != 0);
    if ($test$plusargs("KVIPS_FCOV")) coverage_enable = 1'b1;
    if ($test$plusargs("KVIPS_AXI4_TRACE")) trace_enable = 1'b1;
    if ($test$plusargs("KVIPS_AXI4_TR_RECORD")) tr_record_enable = 1'b1;
  endfunction

  function void set_role_master();
    is_master = 1'b1;
    is_slave  = 1'b0;
  endfunction

  function void set_role_slave();
    is_master = 1'b0;
    is_slave  = 1'b1;
  endfunction

`ifdef VERILATOR
  /* verilator lint_off WIDTHEXPAND */
  /* verilator lint_off WIDTHTRUNC */
`endif
  `uvm_object_param_utils_begin(axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W))
    `uvm_field_int(is_master, UVM_DEFAULT)
    `uvm_field_int(is_slave,  UVM_DEFAULT)
    `uvm_field_int(monitor_enable, UVM_DEFAULT)
    `uvm_field_int(trace_enable, UVM_DEFAULT)
    `uvm_field_int(tr_record_enable, UVM_DEFAULT)
    `uvm_field_string(tr_stream_name, UVM_DEFAULT)
    `uvm_field_int(master_pipelined, UVM_DEFAULT)
    `uvm_field_int(max_outstanding_reads, UVM_DEFAULT)
    `uvm_field_int(max_outstanding_writes, UVM_DEFAULT)
    `uvm_field_int(slave_reorder_b, UVM_DEFAULT)
    `uvm_field_int(slave_interleave_r, UVM_DEFAULT)
    `uvm_field_int(slave_exclusive_enable, UVM_DEFAULT)
    `uvm_field_int(slave_exclusive_max_bytes, UVM_DEFAULT)
    `uvm_field_int(inter_txn_gap_min, UVM_DEFAULT)
    `uvm_field_int(inter_txn_gap_max, UVM_DEFAULT)
    `uvm_field_int(master_aw_delay_min, UVM_DEFAULT)
    `uvm_field_int(master_aw_delay_max, UVM_DEFAULT)
    `uvm_field_int(master_w_beat_gap_min, UVM_DEFAULT)
    `uvm_field_int(master_w_beat_gap_max, UVM_DEFAULT)
    `uvm_field_int(master_ar_delay_min, UVM_DEFAULT)
    `uvm_field_int(master_ar_delay_max, UVM_DEFAULT)
    `uvm_field_int(master_rready_random, UVM_DEFAULT)
    `uvm_field_int(master_rready_low_min, UVM_DEFAULT)
    `uvm_field_int(master_rready_low_max, UVM_DEFAULT)
    `uvm_field_int(slave_mem_enable, UVM_DEFAULT)
    `uvm_field_int(slave_mem_bytes, UVM_DEFAULT)
    `uvm_field_int(slave_mem_base, UVM_DEFAULT)
    `uvm_field_int(slave_mem_wrap, UVM_DEFAULT)
    `uvm_field_int(slave_err_enable, UVM_DEFAULT)
    `uvm_field_int(slave_err_on_read, UVM_DEFAULT)
    `uvm_field_int(slave_err_on_write, UVM_DEFAULT)
    `uvm_field_int(slave_err_start, UVM_DEFAULT)
    `uvm_field_int(slave_err_end, UVM_DEFAULT)
    `uvm_field_enum(axi4_resp_e, slave_err_resp, UVM_DEFAULT)
    `uvm_field_int(ready_min, UVM_DEFAULT)
    `uvm_field_int(ready_max, UVM_DEFAULT)
    `uvm_field_int(resp_min, UVM_DEFAULT)
    `uvm_field_int(resp_max, UVM_DEFAULT)
    `uvm_field_int(handshake_timeout_cycles, UVM_DEFAULT)
    `uvm_field_int(stats_enable, UVM_DEFAULT)
    `uvm_field_int(stats_window_cycles, UVM_DEFAULT)
    `uvm_field_int(coverage_enable, UVM_DEFAULT)
  `uvm_object_utils_end
`ifdef VERILATOR
  /* verilator lint_on WIDTHTRUNC */
  /* verilator lint_on WIDTHEXPAND */
`endif

endclass

class axi4_env_cfg #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends uvm_object;

  axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W) agent_cfgs[$];

  function new(string name = "axi4_env_cfg");
    super.new(name);
  endfunction

  function void add_agent_cfg(axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W) cfg);
    agent_cfgs.push_back(cfg);
  endfunction

`ifdef VERILATOR
  /* verilator lint_off WIDTHEXPAND */
  /* verilator lint_off WIDTHTRUNC */
`endif
  `uvm_object_param_utils_begin(axi4_env_cfg#(ADDR_W, DATA_W, ID_W, USER_W))
    `uvm_field_queue_object(agent_cfgs, UVM_DEFAULT)
  `uvm_object_utils_end
`ifdef VERILATOR
  /* verilator lint_on WIDTHTRUNC */
  /* verilator lint_on WIDTHEXPAND */
`endif

endclass

`endif // KVIPS_AXI4_CFG_SVH
