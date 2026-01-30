//------------------------------------------------------------------------------
// AHB Configuration
//------------------------------------------------------------------------------
`ifndef KVIPS_AHB_CFG_SVH
`define KVIPS_AHB_CFG_SVH

class ahb_cfg #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2
) extends uvm_object;

  typedef virtual ahb_if #(ADDR_W, DATA_W, .HRESP_W(HRESP_W)) ahb_vif_t;
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

  // Checks/coverage/logging
  bit monitor_enable  = 1'b1;
  bit coverage_enable = 1'b0;
  bit trace_enable    = 1'b0;

  // Transaction recording (optional)
  bit    tr_record_enable = 1'b0;
  string tr_stream_name   = "kvips_ahb";

  function new(string name = "ahb_cfg");
    super.new(name);
  endfunction

  function void apply_plusargs();
    string s;
    if ($value$plusargs("AHB_MODE=%s", s)) begin
      if ((s == "AHB_LITE") || (s == "ahb_lite") || (s == "LITE") || (s == "lite")) mode = AHB_MODE_LITE;
      if ((s == "AHB_FULL") || (s == "ahb_full") || (s == "FULL") || (s == "full")) mode = AHB_MODE_FULL;
    end
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

  `uvm_object_param_utils_begin(ahb_cfg#(ADDR_W, DATA_W, HRESP_W))
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
    `uvm_field_int(monitor_enable, UVM_DEFAULT)
    `uvm_field_int(coverage_enable, UVM_DEFAULT)
    `uvm_field_int(trace_enable, UVM_DEFAULT)
    `uvm_field_int(tr_record_enable, UVM_DEFAULT)
    `uvm_field_string(tr_stream_name, UVM_DEFAULT)
  `uvm_object_utils_end
endclass

// Agent config wrapper (role + active/passive)
class ahb_agent_cfg #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2
) extends uvm_object;

  ahb_cfg#(ADDR_W, DATA_W, HRESP_W) cfg;

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

  `uvm_object_param_utils_begin(ahb_agent_cfg#(ADDR_W, DATA_W, HRESP_W))
    `uvm_field_object(cfg, UVM_DEFAULT)
    `uvm_field_int(is_master, UVM_DEFAULT)
    `uvm_field_int(is_slave, UVM_DEFAULT)
    `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_DEFAULT)
  `uvm_object_utils_end
endclass

class ahb_env_cfg #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2
) extends uvm_object;

  ahb_agent_cfg#(ADDR_W, DATA_W, HRESP_W) agent_cfgs[$];

  function new(string name = "ahb_env_cfg");
    super.new(name);
  endfunction

  function void add_agent_cfg(ahb_agent_cfg#(ADDR_W, DATA_W, HRESP_W) c);
    agent_cfgs.push_back(c);
  endfunction

  `uvm_object_param_utils_begin(ahb_env_cfg#(ADDR_W, DATA_W, HRESP_W))
    `uvm_field_queue_object(agent_cfgs, UVM_DEFAULT)
  `uvm_object_utils_end
endclass

`endif // KVIPS_AHB_CFG_SVH

