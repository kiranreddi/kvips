//------------------------------------------------------------------------------
// AHB Configuration
//------------------------------------------------------------------------------
`ifndef KVIPS_AHB_CFG_SVH
`define KVIPS_AHB_CFG_SVH

class ahb_cfg #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2,
  bit HAS_HMASTLOCK = 1'b0
) extends uvm_object;

`ifdef VERILATOR
  typedef virtual interface ahb_if #(
    .ADDR_W(ADDR_W),
    .DATA_W(DATA_W),
    .HAS_HMASTLOCK(HAS_HMASTLOCK),
    .HRESP_W(HRESP_W)
  ) ahb_vif_t;
`else
  typedef virtual ahb_if #(
    .ADDR_W(ADDR_W),
    .DATA_W(DATA_W),
    .HAS_HMASTLOCK(HAS_HMASTLOCK),
    .HRESP_W(HRESP_W)
  ) ahb_vif_t;
`endif

  ahb_vif_t vif;

  // Protocol selection
  ahb_mode_e mode = AHB_MODE_LITE;

  // Address decode / memory model behavior (single-slave default)
  bit                 single_slave_mode = 1'b1;
  logic [ADDR_W-1:0]  base_addr         = '0;
  logic [ADDR_W-1:0]  addr_mask         = '0; // if nonzero, applies (addr & mask) comparison

  // Timing / wait-states (slave)
  bit          allow_wait_states = 1'b0;
  int unsigned min_wait          = 0;
  int unsigned max_wait          = 0;

  // Error injection (slave)
  bit                 err_enable  = 1'b0;
  logic [ADDR_W-1:0]  err_addr_lo = '0;
  logic [ADDR_W-1:0]  err_addr_hi = '0;
  int unsigned        err_pct     = 0; // 0..100

  // Burst enable/policy (master)
  bit          allow_bursts        = 1'b1;
  bit          allow_wrap          = 1'b1;
  int unsigned max_incr_len        = 16; // used for HBURST=INCR
  bit          insert_idles        = 1'b0;
  int unsigned idle_gap_min        = 0;
  int unsigned idle_gap_max        = 0;

  // Expected transfer sizes (coverage + legality knobs). These are primarily
  // used by the monitor/coverage model to avoid "unreachable bins" when the
  // environment intentionally restricts what a master will generate.
  //
  // Defaults enable all sizes up to DATA_W (set in new()).
  bit allow_size_8  = 1'b1;
  bit allow_size_16 = 1'b1;
  bit allow_size_32 = 1'b1;
  bit allow_size_64 = 1'b1;

  // Advanced responses (AHB Full only). KVIPS currently supports OKAY/ERROR in
  // the slave responder; RETRY/SPLIT are modeled as disabled by default.
  bit          allow_retry_split   = 1'b0;

  // Checks/coverage/logging
  bit monitor_enable  = 1'b1;
  bit coverage_enable = 1'b0;
  bit trace_enable    = 1'b0;

  // Timeouts (0 disables)
  int unsigned handshake_timeout_cycles = 100000;

  // Transaction recording (optional)
  bit    tr_record_enable = 1'b0;
  string tr_stream_name   = "kvips_ahb";

  function new(string name = "ahb_cfg");
    super.new(name);
    allow_size_8  = 1'b1;
    allow_size_16 = (DATA_W >= 16);
    allow_size_32 = (DATA_W >= 32);
    allow_size_64 = (DATA_W >= 64);
  endfunction

  function void apply_plusargs();
    string s;
    int unsigned v;
    if ($value$plusargs("AHB_MODE=%s", s)) begin
      if ((s == "AHB_LITE") || (s == "ahb_lite") || (s == "LITE") || (s == "lite")) mode = AHB_MODE_LITE;
      if ((s == "AHB_FULL") || (s == "ahb_full") || (s == "FULL") || (s == "full")) mode = AHB_MODE_FULL;
    end
    if ($value$plusargs("KVIPS_AHB_COV=%d", v)) coverage_enable = (v != 0);
    if ($value$plusargs("KVIPS_COV=%d", v)) coverage_enable = (v != 0);
    if ($test$plusargs("KVIPS_FCOV")) coverage_enable = 1'b1;
    if ($test$plusargs("KVIPS_AHB_TRACE")) trace_enable = 1'b1;
    if ($test$plusargs("KVIPS_AHB_TR_RECORD")) tr_record_enable = 1'b1;
    if ($value$plusargs("KVIPS_AHB_TIMEOUT=%d", v)) handshake_timeout_cycles = v;
  endfunction

  function bit is_full();
    return (mode == AHB_MODE_FULL);
  endfunction

  function bit addr_in_error_range(logic [ADDR_W-1:0] addr);
    if (!err_enable) return 1'b0;
    if ((addr >= err_addr_lo) && (addr <= err_addr_hi)) return 1'b1;
    if (err_pct == 0) return 1'b0;
    return (($urandom_range(0, 99) < err_pct) ? 1'b1 : 1'b0);
  endfunction

  function bit addr_selected(logic [ADDR_W-1:0] addr);
    if (single_slave_mode) return 1'b1;
    if (addr_mask != '0) begin
      return ((addr & addr_mask) == (base_addr & addr_mask));
    end
    return (addr == base_addr);
  endfunction

`ifdef VERILATOR
  /* verilator lint_off WIDTHEXPAND */
  /* verilator lint_off WIDTHTRUNC */
`endif
  `uvm_object_param_utils_begin(ahb_cfg#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK))
    `uvm_field_enum(ahb_mode_e, mode, UVM_DEFAULT)
    `uvm_field_int(single_slave_mode, UVM_DEFAULT)
    `uvm_field_int(base_addr, UVM_DEFAULT)
    `uvm_field_int(addr_mask, UVM_DEFAULT)
    `uvm_field_int(allow_wait_states, UVM_DEFAULT)
    `uvm_field_int(min_wait, UVM_DEFAULT)
    `uvm_field_int(max_wait, UVM_DEFAULT)
    `uvm_field_int(err_enable, UVM_DEFAULT)
    `uvm_field_int(err_addr_lo, UVM_DEFAULT)
    `uvm_field_int(err_addr_hi, UVM_DEFAULT)
    `uvm_field_int(err_pct, UVM_DEFAULT)
    `uvm_field_int(allow_bursts, UVM_DEFAULT)
    `uvm_field_int(allow_wrap, UVM_DEFAULT)
    `uvm_field_int(max_incr_len, UVM_DEFAULT)
    `uvm_field_int(insert_idles, UVM_DEFAULT)
    `uvm_field_int(idle_gap_min, UVM_DEFAULT)
    `uvm_field_int(idle_gap_max, UVM_DEFAULT)
    `uvm_field_int(allow_size_8, UVM_DEFAULT)
    `uvm_field_int(allow_size_16, UVM_DEFAULT)
    `uvm_field_int(allow_size_32, UVM_DEFAULT)
    `uvm_field_int(allow_size_64, UVM_DEFAULT)
    `uvm_field_int(allow_retry_split, UVM_DEFAULT)
    `uvm_field_int(monitor_enable, UVM_DEFAULT)
    `uvm_field_int(coverage_enable, UVM_DEFAULT)
    `uvm_field_int(trace_enable, UVM_DEFAULT)
    `uvm_field_int(handshake_timeout_cycles, UVM_DEFAULT)
    `uvm_field_int(tr_record_enable, UVM_DEFAULT)
    `uvm_field_string(tr_stream_name, UVM_DEFAULT)
  `uvm_object_utils_end
`ifdef VERILATOR
  /* verilator lint_on WIDTHTRUNC */
  /* verilator lint_on WIDTHEXPAND */
`endif
endclass

// Agent config wrapper (role + active/passive)
class ahb_agent_cfg #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2,
  bit HAS_HMASTLOCK = 1'b0
) extends uvm_object;

  ahb_cfg#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK) cfg;

  bit is_master = 1'b1;
  bit is_slave  = 1'b0;
  uvm_active_passive_enum is_active = UVM_ACTIVE;

  function new(string name = "ahb_agent_cfg");
    super.new(name);
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
  `uvm_object_param_utils_begin(ahb_agent_cfg#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK))
    `uvm_field_object(cfg, UVM_DEFAULT)
    `uvm_field_int(is_master, UVM_DEFAULT)
    `uvm_field_int(is_slave, UVM_DEFAULT)
    `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_DEFAULT)
  `uvm_object_utils_end
`ifdef VERILATOR
  /* verilator lint_on WIDTHTRUNC */
  /* verilator lint_on WIDTHEXPAND */
`endif
endclass

class ahb_env_cfg #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2,
  bit HAS_HMASTLOCK = 1'b0
) extends uvm_object;

  ahb_agent_cfg#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK) agent_cfgs[$];

  function new(string name = "ahb_env_cfg");
    super.new(name);
  endfunction

  function void add_agent_cfg(ahb_agent_cfg#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK) c);
    agent_cfgs.push_back(c);
  endfunction

`ifdef VERILATOR
  /* verilator lint_off WIDTHEXPAND */
  /* verilator lint_off WIDTHTRUNC */
`endif
  `uvm_object_param_utils_begin(ahb_env_cfg#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK))
    `uvm_field_queue_object(agent_cfgs, UVM_DEFAULT)
  `uvm_object_utils_end
`ifdef VERILATOR
  /* verilator lint_on WIDTHTRUNC */
  /* verilator lint_on WIDTHEXPAND */
`endif
endclass

`endif // KVIPS_AHB_CFG_SVH
