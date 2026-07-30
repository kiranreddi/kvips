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

`ifdef VERILATOR
  virtual axi4_if #(ADDR_W, DATA_W, ID_W, USER_W) vif;
`else
  typedef virtual axi4_if #(ADDR_W, DATA_W, ID_W, USER_W) axi4_vif_t;
  axi4_vif_t vif;
`endif

  bit is_master = 1'b1;
  bit is_slave  = 1'b0;

  // Monitor enable (analysis + stats). Disable when multiple agents share the
  // same vif to avoid duplicate transaction capture.
  bit monitor_enable = 1'b1;

  // Independent channel-order checker.  It is normally enabled with the
  // passive monitor and catches orphaned/mis-ordered B/R traffic directly
  // from the interface, rather than relying on monitor reconstruction.
  bit protocol_checker_enable = 1'b1;

  bit trace_enable = 1'b0;

  // Transaction recording (UVM transaction viewing)
  bit    tr_record_enable = 1'b0;
  string tr_stream_name   = "kvips_axi4";

  // Master: allow multiple outstanding by accepting items early and returning
  // responses asynchronously via the sequencer response queue.
  bit          master_pipelined = 1'b0;
  int unsigned max_outstanding_reads  = 1;
  int unsigned max_outstanding_writes = 1;
  // Zero means the per-direction limits above are the only limit.
  int unsigned max_outstanding_total  = 0;
  // When clear, conservatively serialize opposite-direction traffic in the
  // pipelined master. This is useful when an environment requires explicit
  // read/write ordering rather than allowing overlap.
  bit          order_overlapping_rw = 1'b1;
  // Optional dependency-aware alternative to the legacy all-or-nothing
  // opposite-direction serialization policy.
  axi4_rw_order_mode_e rw_order_mode = AXI4_RW_ORDER_ALLOW;
  // In pipelined mode, flush in-flight requests on reset and return them to
  // the sequence response queue with axi4_item.reset_aborted set.  No AXI B/R
  // response is fabricated because reset has no AXI response encoding.
  bit          master_reset_flush = 1'b1;

  // Slave: response scheduling knobs
  bit          slave_reorder_b  = 1'b0;
  bit          slave_interleave_r = 1'b0;
  bit          slave_reorder_r = 1'b0;
  int unsigned slave_b_accum_cycles = 0;
  int unsigned slave_r_accum_cycles = 0;
  // Zero means unlimited, preserving the original slave behavior.
  int unsigned slave_max_outstanding_wr = 0;
  int unsigned slave_max_outstanding_rd = 0;

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
  bit          master_bready_random = 1'b0;
  int unsigned master_bready_low_min = 0;
  int unsigned master_bready_low_max = 5;

  // Slave knobs
  bit          slave_mem_enable = 1'b1;
  int unsigned slave_mem_bytes  = 64*1024;
  // Slave memory address mapping:
  // - The memory model is a byte array [0:slave_mem_bytes-1]
  // - Transactions index into it using (addr - slave_mem_base)
  // - Optionally wrap addresses modulo slave_mem_bytes
  longint unsigned slave_mem_base = 0;
  bit             slave_mem_wrap = 1'b0;
  axi4_uninit_read_policy_e slave_uninit_read_policy = AXI4_UNINIT_ZERO;
  logic [7:0]               slave_uninit_fill = 8'h00;
  bit                       slave_uninit_read_warn = 1'b0;
  bit                       slave_clear_mem_on_reset = 1'b0;

  // Slave: error-response injection (simple address-range based model).
  // If enabled and the transaction overlaps [slave_err_start, slave_err_end],
  // then the slave responds with slave_err_resp and does not update memory.
  bit          slave_err_enable  = 1'b0;
  bit          slave_err_on_read  = 1'b1;
  bit          slave_err_on_write = 1'b1;
  logic [ADDR_W-1:0] slave_err_start = '0;
  logic [ADDR_W-1:0] slave_err_end   = '0;
  axi4_resp_e   slave_err_resp   = AXI4_RESP_DECERR;
  int unsigned  slave_rd_slverr_rate_pct = 0;
  int unsigned  slave_rd_decerr_rate_pct = 0;
  int unsigned  slave_wr_slverr_rate_pct = 0;
  int unsigned  slave_wr_decerr_rate_pct = 0;

  // Optional address decode.  A transfer that touches an unmapped byte returns
  // DECERR.  Regions are inclusive and may be populated with add_slave_region.
  bit                       slave_region_decode_enable = 1'b0;
  logic [ADDR_W-1:0]        slave_region_start[$];
  logic [ADDR_W-1:0]        slave_region_end[$];

  int unsigned ready_min = 0;  // random-ready (per cycle) min delay
  int unsigned ready_max = 0;  // random-ready (per cycle) max delay
  int unsigned resp_min  = 0;  // response latency (cycles)
  int unsigned resp_max  = 0;
  int unsigned slave_aw_ready_min = 0;
  int unsigned slave_aw_ready_max = 0;
  int unsigned slave_w_ready_min  = 0;
  int unsigned slave_w_ready_max  = 0;
  int unsigned slave_ar_ready_min = 0;
  int unsigned slave_ar_ready_max = 0;
  int unsigned slave_b_resp_min   = 0;
  int unsigned slave_b_resp_max   = 0;
  int unsigned slave_r_resp_min   = 0;
  int unsigned slave_r_resp_max   = 0;
  bit          slave_aw_random_ready = 1'b0;
  bit          slave_w_random_ready  = 1'b0;
  bit          slave_ar_random_ready = 1'b0;
  int unsigned slave_r_beat_delays[];

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

  function void add_slave_region(logic [ADDR_W-1:0] start_addr, logic [ADDR_W-1:0] end_addr);
    slave_region_start.push_back(start_addr);
    slave_region_end.push_back(end_addr);
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
    `uvm_field_int(protocol_checker_enable, UVM_DEFAULT)
    `uvm_field_int(trace_enable, UVM_DEFAULT)
    `uvm_field_int(tr_record_enable, UVM_DEFAULT)
    `uvm_field_string(tr_stream_name, UVM_DEFAULT)
    `uvm_field_int(master_pipelined, UVM_DEFAULT)
    `uvm_field_int(max_outstanding_reads, UVM_DEFAULT)
    `uvm_field_int(max_outstanding_writes, UVM_DEFAULT)
    `uvm_field_int(max_outstanding_total, UVM_DEFAULT)
    `uvm_field_int(order_overlapping_rw, UVM_DEFAULT)
    `uvm_field_enum(axi4_rw_order_mode_e, rw_order_mode, UVM_DEFAULT)
    `uvm_field_int(master_reset_flush, UVM_DEFAULT)
    `uvm_field_int(slave_reorder_b, UVM_DEFAULT)
    `uvm_field_int(slave_interleave_r, UVM_DEFAULT)
    `uvm_field_int(slave_reorder_r, UVM_DEFAULT)
    `uvm_field_int(slave_b_accum_cycles, UVM_DEFAULT)
    `uvm_field_int(slave_r_accum_cycles, UVM_DEFAULT)
    `uvm_field_int(slave_max_outstanding_wr, UVM_DEFAULT)
    `uvm_field_int(slave_max_outstanding_rd, UVM_DEFAULT)
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
    `uvm_field_int(master_bready_random, UVM_DEFAULT)
    `uvm_field_int(master_bready_low_min, UVM_DEFAULT)
    `uvm_field_int(master_bready_low_max, UVM_DEFAULT)
    `uvm_field_int(slave_mem_enable, UVM_DEFAULT)
    `uvm_field_int(slave_mem_bytes, UVM_DEFAULT)
    `uvm_field_int(slave_mem_base, UVM_DEFAULT)
    `uvm_field_int(slave_mem_wrap, UVM_DEFAULT)
    `uvm_field_enum(axi4_uninit_read_policy_e, slave_uninit_read_policy, UVM_DEFAULT)
    `uvm_field_int(slave_uninit_fill, UVM_DEFAULT)
    `uvm_field_int(slave_uninit_read_warn, UVM_DEFAULT)
    `uvm_field_int(slave_clear_mem_on_reset, UVM_DEFAULT)
    `uvm_field_int(slave_err_enable, UVM_DEFAULT)
    `uvm_field_int(slave_err_on_read, UVM_DEFAULT)
    `uvm_field_int(slave_err_on_write, UVM_DEFAULT)
    `uvm_field_int(slave_err_start, UVM_DEFAULT)
    `uvm_field_int(slave_err_end, UVM_DEFAULT)
    `uvm_field_enum(axi4_resp_e, slave_err_resp, UVM_DEFAULT)
    `uvm_field_int(slave_rd_slverr_rate_pct, UVM_DEFAULT)
    `uvm_field_int(slave_rd_decerr_rate_pct, UVM_DEFAULT)
    `uvm_field_int(slave_wr_slverr_rate_pct, UVM_DEFAULT)
    `uvm_field_int(slave_wr_decerr_rate_pct, UVM_DEFAULT)
    `uvm_field_int(slave_region_decode_enable, UVM_DEFAULT)
    `uvm_field_int(ready_min, UVM_DEFAULT)
    `uvm_field_int(ready_max, UVM_DEFAULT)
    `uvm_field_int(resp_min, UVM_DEFAULT)
    `uvm_field_int(resp_max, UVM_DEFAULT)
    `uvm_field_int(slave_aw_ready_min, UVM_DEFAULT)
    `uvm_field_int(slave_aw_ready_max, UVM_DEFAULT)
    `uvm_field_int(slave_w_ready_min, UVM_DEFAULT)
    `uvm_field_int(slave_w_ready_max, UVM_DEFAULT)
    `uvm_field_int(slave_ar_ready_min, UVM_DEFAULT)
    `uvm_field_int(slave_ar_ready_max, UVM_DEFAULT)
    `uvm_field_int(slave_b_resp_min, UVM_DEFAULT)
    `uvm_field_int(slave_b_resp_max, UVM_DEFAULT)
    `uvm_field_int(slave_r_resp_min, UVM_DEFAULT)
    `uvm_field_int(slave_r_resp_max, UVM_DEFAULT)
    `uvm_field_int(slave_aw_random_ready, UVM_DEFAULT)
    `uvm_field_int(slave_w_random_ready, UVM_DEFAULT)
    `uvm_field_int(slave_ar_random_ready, UVM_DEFAULT)
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

class axi4_ready_ctrl_item #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends uvm_sequence_item;
  rand axi4_ready_channel_e channel;
  rand int unsigned         low_min;
  rand int unsigned         low_max;
  rand bit                  randomize_ready;
  constraint c_low_order { low_max >= low_min; }
  `uvm_object_param_utils(axi4_ready_ctrl_item#(ADDR_W, DATA_W, ID_W, USER_W))
  function new(string name = "axi4_ready_ctrl_item");
    super.new(name);
    channel = AXI4_READY_AW;
  endfunction
  function void apply_to_txn(axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) txn);
    int unsigned delay;
    delay = randomize_ready ? $urandom_range(low_max, low_min) : low_min;
    case (channel)
      AXI4_READY_AW: txn.aw_delay_cycles = int'(delay);
      AXI4_READY_AR: txn.ar_delay_cycles = int'(delay);
      AXI4_READY_W:  txn.w_beat_gap_cycles = int'(delay);
      default: `uvm_warning("AXI4_PHASE", "B/R ready control applies to configuration, not one transaction")
    endcase
  endfunction
  function void apply_to_cfg(axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W) cfg);
    case (channel)
      AXI4_READY_AW: begin
        cfg.slave_aw_ready_min = low_min; cfg.slave_aw_ready_max = low_max;
        cfg.slave_aw_random_ready = randomize_ready;
      end
      AXI4_READY_W: begin
        cfg.slave_w_ready_min = low_min; cfg.slave_w_ready_max = low_max;
        cfg.slave_w_random_ready = randomize_ready;
      end
      AXI4_READY_AR: begin
        cfg.slave_ar_ready_min = low_min; cfg.slave_ar_ready_max = low_max;
        cfg.slave_ar_random_ready = randomize_ready;
      end
      AXI4_READY_B: begin
        cfg.master_bready_random = randomize_ready;
        cfg.master_bready_low_min = low_min; cfg.master_bready_low_max = low_max;
      end
      AXI4_READY_R: begin
        cfg.master_rready_random = randomize_ready;
        cfg.master_rready_low_min = low_min; cfg.master_rready_low_max = low_max;
      end
    endcase
  endfunction
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
