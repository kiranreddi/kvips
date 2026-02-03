//------------------------------------------------------------------------------
// APB Configuration
//------------------------------------------------------------------------------
`ifndef KVIPS_APB_CFG_SVH
`define KVIPS_APB_CFG_SVH

class apb_cfg #(
  int ADDR_W = 32,
  int DATA_W = 32,
  int NSEL   = 1
) extends uvm_object;

  typedef virtual interface apb_if #(ADDR_W, DATA_W, NSEL) apb_vif_t;

  apb_vif_t vif;

  apb_protocol_e protocol = APB_PROTOCOL_APB4;
  int unsigned   sel_index = 0;

  // Master behavior
  bit drop_psel_between = 1'b1;

  // Slave timing / wait-state insertion
  bit          allow_wait_states = 1'b1;
  int unsigned min_wait_cycles   = 0;
  int unsigned max_wait_cycles   = 0;

  // Error injection (slave)
  bit          slverr_enable      = 1'b0;
  int unsigned slverr_pct         = 0; // 0..100
  logic [ADDR_W-1:0] slverr_start = '0;
  logic [ADDR_W-1:0] slverr_end   = '0;

  // APB4 extras
  bit          randomize_pprot    = 1'b0;
  logic [2:0]  default_pprot      = 3'b000;
  bit          randomize_pstrb    = 1'b0;
  logic [(DATA_W/8)-1:0] default_pstrb = '1;

  // Monitor / checks
  bit monitor_enable   = 1'b1;
  bit coverage_enable  = 1'b0;
  bit trace_enable     = 1'b0;

  // Transaction recording
  bit    tr_record_enable = 1'b0;
  string tr_stream_name   = "kvips_apb";

  function new(string name = "apb_cfg");
    super.new(name);
  endfunction

  function void apply_plusargs();
    string s;
    int unsigned v;
    if ($value$plusargs("APB_PROTOCOL=%s", s)) begin
      if ((s == "APB3") || (s == "apb3")) protocol = APB_PROTOCOL_APB3;
      if ((s == "APB4") || (s == "apb4")) protocol = APB_PROTOCOL_APB4;
    end
    if ($value$plusargs("KVIPS_APB_COV=%d", v)) coverage_enable = (v != 0);
    if ($value$plusargs("KVIPS_COV=%d", v)) coverage_enable = (v != 0);
    if ($test$plusargs("KVIPS_FCOV")) coverage_enable = 1'b1;
    if ($test$plusargs("KVIPS_APB_TRACE")) trace_enable = 1'b1;
    if ($test$plusargs("KVIPS_APB_TR_RECORD")) tr_record_enable = 1'b1;
  endfunction

  function bit is_apb4();
    return (protocol == APB_PROTOCOL_APB4);
  endfunction

`ifdef VERILATOR
  /* verilator lint_off WIDTHEXPAND */
  /* verilator lint_off WIDTHTRUNC */
`endif
  `uvm_object_param_utils_begin(apb_cfg#(ADDR_W, DATA_W, NSEL))
    `uvm_field_enum(apb_protocol_e, protocol, UVM_DEFAULT)
    `uvm_field_int(sel_index, UVM_DEFAULT)
    `uvm_field_int(drop_psel_between, UVM_DEFAULT)
    `uvm_field_int(allow_wait_states, UVM_DEFAULT)
    `uvm_field_int(min_wait_cycles, UVM_DEFAULT)
    `uvm_field_int(max_wait_cycles, UVM_DEFAULT)
    `uvm_field_int(slverr_enable, UVM_DEFAULT)
    `uvm_field_int(slverr_pct, UVM_DEFAULT)
    `uvm_field_int(slverr_start, UVM_DEFAULT)
    `uvm_field_int(slverr_end, UVM_DEFAULT)
    `uvm_field_int(randomize_pprot, UVM_DEFAULT)
    `uvm_field_int(default_pprot, UVM_DEFAULT)
    `uvm_field_int(randomize_pstrb, UVM_DEFAULT)
    `uvm_field_int(default_pstrb, UVM_DEFAULT)
    `uvm_field_int(monitor_enable, UVM_DEFAULT)
    `uvm_field_int(coverage_enable, UVM_DEFAULT)
    `uvm_field_int(trace_enable, UVM_DEFAULT)
    `uvm_field_int(tr_record_enable, UVM_DEFAULT)
    `uvm_field_string(tr_stream_name, UVM_DEFAULT)
  `uvm_object_utils_end
`ifdef VERILATOR
  /* verilator lint_on WIDTHTRUNC */
  /* verilator lint_on WIDTHEXPAND */
`endif

endclass

// Agent config wrapper (role + active/passive)
class apb_agent_cfg #(
  int ADDR_W = 32,
  int DATA_W = 32,
  int NSEL   = 1
) extends uvm_object;

  apb_cfg#(ADDR_W, DATA_W, NSEL) cfg;

  bit is_master = 1'b1;
  bit is_slave  = 1'b0;
  uvm_active_passive_enum is_active = UVM_ACTIVE;

  function new(string name = "apb_agent_cfg");
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
  `uvm_object_param_utils_begin(apb_agent_cfg#(ADDR_W, DATA_W, NSEL))
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

class apb_env_cfg #(
  int ADDR_W = 32,
  int DATA_W = 32,
  int NSEL   = 1
) extends uvm_object;

  apb_agent_cfg#(ADDR_W, DATA_W, NSEL) agent_cfgs[$];

  function new(string name = "apb_env_cfg");
    super.new(name);
  endfunction

  function void add_agent_cfg(apb_agent_cfg#(ADDR_W, DATA_W, NSEL) c);
    agent_cfgs.push_back(c);
  endfunction

`ifdef VERILATOR
  /* verilator lint_off WIDTHEXPAND */
  /* verilator lint_off WIDTHTRUNC */
`endif
  `uvm_object_param_utils_begin(apb_env_cfg#(ADDR_W, DATA_W, NSEL))
    `uvm_field_queue_object(agent_cfgs, UVM_DEFAULT)
  `uvm_object_utils_end
`ifdef VERILATOR
  /* verilator lint_on WIDTHTRUNC */
  /* verilator lint_on WIDTHEXPAND */
`endif
endclass

`endif // KVIPS_APB_CFG_SVH
