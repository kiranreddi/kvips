`ifndef KVIPS_AHB_EX_TB_TESTS_SVH
`define KVIPS_AHB_EX_TB_TESTS_SVH

class ahb_objtn_clear_catcher extends uvm_report_catcher;
  function new(string name = "ahb_objtn_clear_catcher");
    super.new(name);
  endfunction

  virtual function action_e catch();
    if (get_id() == "OBJTN_CLEAR") begin
      return CAUGHT;
    end
    return THROW;
  endfunction
endclass

class ahb_b2b_base_test extends uvm_test;
  `uvm_component_utils(ahb_b2b_base_test)

  localparam int ADDR_W  = 16;
  localparam int DATA_W  = 32;
  localparam int HRESP_W = 2;

`ifdef VERILATOR
  typedef virtual ahb_if #(.ADDR_W(ADDR_W), .DATA_W(DATA_W), .HRESP_W(HRESP_W)) ahb_vif_t;
`else
  typedef virtual ahb_if #(.ADDR_W(ADDR_W), .DATA_W(DATA_W), .HRESP_W(HRESP_W)) ahb_vif_t;
`endif
  ahb_vif_t vif;

  ahb_env_cfg#(ADDR_W, DATA_W, HRESP_W) env_cfg;
  ahb_env#(ADDR_W, DATA_W, HRESP_W)     env;

  ahb_cfg#(ADDR_W, DATA_W, HRESP_W) m_cfg;
  ahb_cfg#(ADDR_W, DATA_W, HRESP_W) s_cfg;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  virtual function void post_build_cfg();
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

`ifdef VERILATOR
    uvm_root::get().set_report_severity_id_action(UVM_WARNING, "OBJTN_CLEAR", UVM_NO_ACTION);
  uvm_root::get().set_report_id_action("OBJTN_CLEAR", UVM_NO_ACTION);
    begin
      uvm_phase run_phase;
      uvm_objection run_obj;
      run_phase = uvm_run_phase::get();
      run_obj = (run_phase == null) ? null : run_phase.get_objection();
      if (run_obj != null) begin
        run_obj.set_report_severity_id_action(UVM_WARNING, "OBJTN_CLEAR", UVM_NO_ACTION);
        run_obj.set_report_id_action("OBJTN_CLEAR", UVM_NO_ACTION);
      end
    end
    begin
      ahb_objtn_clear_catcher c;
      c = new();
      uvm_report_cb::add(null, c);
    end
`endif
  `ifdef UVM_NO_DPI
    uvm_root::get().set_report_severity_id_action(UVM_WARNING, "UVM/COMP/NAME", UVM_NO_ACTION);
    uvm_root::get().set_report_severity_id_action(UVM_INFO, "UVM/COMP/NAMECHECK", UVM_NO_ACTION);
  `endif

    if (!uvm_config_db#(virtual interface ahb_if #(.ADDR_W(ADDR_W), .DATA_W(DATA_W), .HRESP_W(HRESP_W)))::get(this, "", "vif", vif)) begin
      `uvm_fatal("AHB_TB", "Missing vif in config DB (key: vif)")
    end

    env_cfg = ahb_env_cfg#(ADDR_W, DATA_W, HRESP_W)::type_id::create("env_cfg");

    // Master agent
    begin
      ahb_agent_cfg#(ADDR_W, DATA_W, HRESP_W) a;
      m_cfg = ahb_cfg#(ADDR_W, DATA_W, HRESP_W)::type_id::create("m_cfg");
      m_cfg.vif = vif;
      m_cfg.apply_plusargs();
      if ($test$plusargs("VIP_TRACE")) m_cfg.trace_enable = 1'b1;
      if ($test$plusargs("VIP_COV"))   m_cfg.coverage_enable = 1'b1;

      a = ahb_agent_cfg#(ADDR_W, DATA_W, HRESP_W)::type_id::create("m_agent_cfg");
      a.set_role_master();
      a.is_active = UVM_ACTIVE;
      a.cfg = m_cfg;
      env_cfg.add_agent_cfg(a);
    end

    // Slave agent
    begin
      ahb_agent_cfg#(ADDR_W, DATA_W, HRESP_W) a;
      s_cfg = ahb_cfg#(ADDR_W, DATA_W, HRESP_W)::type_id::create("s_cfg");
      s_cfg.vif = vif;
      s_cfg.apply_plusargs();
      // Avoid duplicate monitoring when master+slave share a single vif.
      s_cfg.monitor_enable = 1'b0;
      if ($test$plusargs("VIP_TRACE")) s_cfg.trace_enable = 1'b1;

      a = ahb_agent_cfg#(ADDR_W, DATA_W, HRESP_W)::type_id::create("s_agent_cfg");
      a.set_role_slave();
      a.is_active = UVM_ACTIVE;
      a.cfg = s_cfg;
      env_cfg.add_agent_cfg(a);
    end

    post_build_cfg();

    uvm_config_db#(ahb_env_cfg#(ADDR_W, DATA_W, HRESP_W))::set(this, "env", "cfg", env_cfg);
    env = ahb_env#(ADDR_W, DATA_W, HRESP_W)::type_id::create("env", this);
  endfunction

  function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    `uvm_info("AHB_TB",
      $sformatf("AHB mode=%s (plusarg +AHB_MODE=AHB_LITE|AHB_FULL)",
        (m_cfg.mode == AHB_MODE_LITE) ? "AHB_LITE" : "AHB_FULL"),
      UVM_LOW)
  endfunction
endclass

class ahb_smoke_test extends ahb_b2b_base_test;
  `uvm_component_utils(ahb_smoke_test)
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  task run_phase(uvm_phase phase);
    ahb_sequencer#(ADDR_W, DATA_W, HRESP_W) seqr;
    ahb_smoke_seq#(ADDR_W, DATA_W, HRESP_W) seq;
    phase.raise_objection(this);
    seqr = env.get_master_sequencer(0);
    seq = new("seq");
    seq.num_txns = 10;
    seq.start(seqr);
    phase.drop_objection(this);
  endtask
endclass

class ahb_single_read_write_test extends ahb_b2b_base_test;
  `uvm_component_utils(ahb_single_read_write_test)
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  task run_phase(uvm_phase phase);
    ahb_sequencer#(ADDR_W, DATA_W, HRESP_W) seqr;
    ahb_single_rw_seq#(ADDR_W, DATA_W, HRESP_W) seq;
    phase.raise_objection(this);
    seqr = env.get_master_sequencer(0);
    seq = new("seq");
    seq.num_txns = 50;
    seq.span_bytes = 1024;
    seq.start(seqr);
    phase.drop_objection(this);
  endtask
endclass

class ahb_wait_state_test extends ahb_b2b_base_test;
  `uvm_component_utils(ahb_wait_state_test)
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  virtual function void post_build_cfg();
    s_cfg.allow_wait_states = 1'b1;
    s_cfg.min_wait = 0;
    s_cfg.max_wait = 8;
  endfunction
  task run_phase(uvm_phase phase);
    ahb_sequencer#(ADDR_W, DATA_W, HRESP_W) seqr;
    ahb_wait_state_seq#(ADDR_W, DATA_W, HRESP_W) seq;
    phase.raise_objection(this);
    seqr = env.get_master_sequencer(0);
    seq = new("seq");
    seq.num_txns = 300;
    seq.start(seqr);
    phase.drop_objection(this);
  endtask
endclass

class ahb_incr_burst_test extends ahb_b2b_base_test;
  `uvm_component_utils(ahb_incr_burst_test)
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  task run_phase(uvm_phase phase);
    ahb_sequencer#(ADDR_W, DATA_W, HRESP_W) seqr;
    ahb_incr_burst_seq#(ADDR_W, DATA_W, HRESP_W) seq;
    phase.raise_objection(this);
    seqr = env.get_master_sequencer(0);
    seq = new("seq");
    seq.num_txns = 100;
    seq.start(seqr);
    phase.drop_objection(this);
  endtask
endclass

class ahb_wrap_burst_test extends ahb_b2b_base_test;
  `uvm_component_utils(ahb_wrap_burst_test)
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  task run_phase(uvm_phase phase);
    ahb_sequencer#(ADDR_W, DATA_W, HRESP_W) seqr;
    ahb_wrap_burst_seq#(ADDR_W, DATA_W, HRESP_W) seq;
    phase.raise_objection(this);
    seqr = env.get_master_sequencer(0);
    seq = new("seq");
    seq.num_txns = 100;
    seq.start(seqr);
    phase.drop_objection(this);
  endtask
endclass

class ahb_back_to_back_test extends ahb_b2b_base_test;
  `uvm_component_utils(ahb_back_to_back_test)
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  task run_phase(uvm_phase phase);
    ahb_sequencer#(ADDR_W, DATA_W, HRESP_W) seqr;
    ahb_back_to_back_seq#(ADDR_W, DATA_W, HRESP_W) seq;
    phase.raise_objection(this);
    seqr = env.get_master_sequencer(0);
    seq = new("seq");
    seq.num_txns = 1000;
    seq.start(seqr);
    phase.drop_objection(this);
  endtask
endclass

class ahb_error_response_test extends ahb_b2b_base_test;
  `uvm_component_utils(ahb_error_response_test)
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  virtual function void post_build_cfg();
    s_cfg.err_enable = 1'b1;
    s_cfg.err_pct = 100;
    s_cfg.err_addr_lo = 16'h0100;
    s_cfg.err_addr_hi = 16'h01ff;
    uvm_config_db#(bit)::set(this, "env.sb", "enable", 1'b0);
  endfunction
  task run_phase(uvm_phase phase);
    ahb_sequencer#(ADDR_W, DATA_W, HRESP_W) seqr;
    ahb_error_seq#(ADDR_W, DATA_W, HRESP_W) seq;
    phase.raise_objection(this);
    seqr = env.get_master_sequencer(0);
    seq = new("seq");
    seq.num_txns = 300;
    seq.base_addr = 16'h0000;
    seq.span_bytes = 512;
    seq.start(seqr);
    phase.drop_objection(this);
  endtask
endclass

class ahb_random_stress_test extends ahb_b2b_base_test;
  `uvm_component_utils(ahb_random_stress_test)
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  task run_phase(uvm_phase phase);
    ahb_sequencer#(ADDR_W, DATA_W, HRESP_W) seqr;
    ahb_random_stress_seq#(ADDR_W, DATA_W, HRESP_W) seq;
    phase.raise_objection(this);
    seqr = env.get_master_sequencer(0);
    seq = new("seq");
    seq.num_txns = 2000;
    seq.span_bytes = 4096;
    seq.start(seqr);
    phase.drop_objection(this);
  endtask
endclass

`endif // KVIPS_AHB_EX_TB_TESTS_SVH
