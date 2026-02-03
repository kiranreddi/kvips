//------------------------------------------------------------------------------
// APB Demo TB Package
//------------------------------------------------------------------------------

package tb_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import apb_types_pkg::*;
  import apb_uvm_pkg::*;

  class apb_objtn_clear_catcher extends uvm_report_catcher;
    function new(string name = "apb_objtn_clear_catcher");
      super.new(name);
    endfunction

    virtual function action_e catch();
      if (get_id() == "OBJTN_CLEAR") begin
        return CAUGHT;
      end
      return THROW;
    endfunction
  endclass

  class apb_b2b_base_test extends uvm_test;
    `uvm_component_utils(apb_b2b_base_test)

    localparam int ADDR_W = 16;
    localparam int DATA_W = 32;
    localparam int NSEL   = 1;

    typedef virtual apb_if #(ADDR_W, DATA_W, NSEL) apb_vif_t;

    apb_vif_t vif;

    apb_env_cfg#(ADDR_W, DATA_W, NSEL) env_cfg;
    apb_env#(ADDR_W, DATA_W, NSEL)     env;
    apb_txn_logger#(ADDR_W, DATA_W)    logger;
    apb_scoreboard#(ADDR_W, DATA_W)    sb;

    apb_cfg#(ADDR_W, DATA_W, NSEL) m_cfg;
    apb_cfg#(ADDR_W, DATA_W, NSEL) s_cfg;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    // Hook for derived tests to tweak cfg after creation.
    virtual function void post_build_cfg();
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);

`ifdef VERILATOR
  uvm_root::get().set_report_severity_id_action(UVM_WARNING, "OBJTN_CLEAR", UVM_NO_ACTION);
  begin
    apb_objtn_clear_catcher c;
    c = new();
    uvm_report_cb::add(null, c);
  end
`endif

      if (!uvm_config_db#(apb_vif_t)::get(this, "", "vif", vif)) begin
        `uvm_fatal("APB_TB", "Missing vif in config DB (key: vif)")
      end

      env_cfg = apb_env_cfg#(ADDR_W, DATA_W, NSEL)::type_id::create("env_cfg");

      // Master agent
      begin
        apb_agent_cfg#(ADDR_W, DATA_W, NSEL) a;
        m_cfg = apb_cfg#(ADDR_W, DATA_W, NSEL)::type_id::create("m_cfg");
        m_cfg.vif = vif;
        m_cfg.apply_plusargs();
        if ($test$plusargs("VIP_TRACE")) m_cfg.trace_enable = 1'b1;
        if ($test$plusargs("VIP_TR")) m_cfg.tr_record_enable = 1'b1;
        if ($test$plusargs("VIP_COV")) m_cfg.coverage_enable = 1'b1;
        if ($test$plusargs("VIP_DROP_PSEL_OFF")) m_cfg.drop_psel_between = 1'b0;

        a = apb_agent_cfg#(ADDR_W, DATA_W, NSEL)::type_id::create("m_agent_cfg");
        a.set_role_master();
        a.is_active = UVM_ACTIVE;
        a.cfg = m_cfg;
        env_cfg.add_agent_cfg(a);
      end

      // Slave agent
      begin
        apb_agent_cfg#(ADDR_W, DATA_W, NSEL) a;
        s_cfg = apb_cfg#(ADDR_W, DATA_W, NSEL)::type_id::create("s_cfg");
        s_cfg.vif = vif;
        s_cfg.apply_plusargs();
        // Disable to avoid duplicate monitoring when master+slave share a vif.
        s_cfg.monitor_enable = 1'b0;
        if ($test$plusargs("VIP_TRACE")) s_cfg.trace_enable = 1'b1;
        if ($test$plusargs("VIP_TR")) s_cfg.tr_record_enable = 1'b1;

        a = apb_agent_cfg#(ADDR_W, DATA_W, NSEL)::type_id::create("s_agent_cfg");
        a.set_role_slave();
        a.is_active = UVM_ACTIVE;
        a.cfg = s_cfg;
        env_cfg.add_agent_cfg(a);
      end

      post_build_cfg();

      uvm_config_db#(apb_env_cfg#(ADDR_W, DATA_W, NSEL))::set(this, "env", "cfg", env_cfg);
      env = apb_env#(ADDR_W, DATA_W, NSEL)::type_id::create("env", this);
      logger = apb_txn_logger#(ADDR_W, DATA_W)::type_id::create("logger", this);
      if ($test$plusargs("VIP_TRACE")) logger.enable = 1'b1;
      sb = apb_scoreboard#(ADDR_W, DATA_W)::type_id::create("sb", this);
    endfunction

    function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      env.ap.connect(logger.analysis_export);
      env.ap.connect(sb.analysis_export);
    endfunction

    function void end_of_elaboration_phase(uvm_phase phase);
      super.end_of_elaboration_phase(phase);
      `uvm_info("APB_TB",
        $sformatf("APB mode=%s (plusarg +APB_PROTOCOL=APB3|APB4)",
          (m_cfg.protocol == APB_PROTOCOL_APB3) ? "APB3" : "APB4"),
        UVM_LOW)
    endfunction
  endclass

  class apb_b2b_reset_sanity_test extends apb_b2b_base_test;
    `uvm_component_utils(apb_b2b_reset_sanity_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
    task run_phase(uvm_phase phase);
      phase.raise_objection(this);
      repeat (20) @(posedge vif.PCLK);
      phase.drop_objection(this);
    endtask
  endclass

  class apb_b2b_smoke_test extends apb_b2b_base_test;
    `uvm_component_utils(apb_b2b_smoke_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
    task run_phase(uvm_phase phase);
      apb_sequencer#(ADDR_W, DATA_W) seqr;
      apb_smoke_rw_seq#(ADDR_W, DATA_W) seq;
      phase.raise_objection(this);
      seqr = env.get_master_sequencer(0);
      seq = new("seq");
      seq.num_txns = 10;
      seq.base_addr = '0;
      seq.start(seqr);
      phase.drop_objection(this);
    endtask
  endclass

  class apb_b2b_wait_state_test extends apb_b2b_base_test;
    `uvm_component_utils(apb_b2b_wait_state_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
    virtual function void post_build_cfg();
      s_cfg.allow_wait_states = 1'b1;
      s_cfg.min_wait_cycles = 0;
      s_cfg.max_wait_cycles = 8;
    endfunction
    task run_phase(uvm_phase phase);
      apb_sequencer#(ADDR_W, DATA_W) seqr;
      apb_random_stress_seq#(ADDR_W, DATA_W) seq;
      phase.raise_objection(this);
      seqr = env.get_master_sequencer(0);
      seq = new("seq");
      seq.num_txns = 200;
      seq.enable_apb4 = m_cfg.is_apb4();
      seq.start(seqr);
      phase.drop_objection(this);
    endtask
  endclass

  class apb_b2b_back_to_back_test extends apb_b2b_base_test;
    `uvm_component_utils(apb_b2b_back_to_back_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
    virtual function void post_build_cfg();
      m_cfg.drop_psel_between = 1'b0;
    endfunction
    task run_phase(uvm_phase phase);
      apb_sequencer#(ADDR_W, DATA_W) seqr;
      apb_random_stress_seq#(ADDR_W, DATA_W) seq;
      phase.raise_objection(this);
      seqr = env.get_master_sequencer(0);
      seq = new("seq");
      seq.num_txns = 500;
      seq.wr_pct = 50;
      seq.enable_apb4 = m_cfg.is_apb4();
      seq.start(seqr);
      phase.drop_objection(this);
    endtask
  endclass

  class apb_b2b_error_injection_test extends apb_b2b_base_test;
    `uvm_component_utils(apb_b2b_error_injection_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
    virtual function void post_build_cfg();
      s_cfg.slverr_enable = 1'b1;
      s_cfg.slverr_pct = 100;
      s_cfg.slverr_start = 16'h0080;
      s_cfg.slverr_end   = 16'h00FF;
      // Disable scoreboard (reads in error region are expected to error).
      uvm_config_db#(bit)::set(this, "sb", "enable", 1'b0);
    endfunction
    task run_phase(uvm_phase phase);
      apb_sequencer#(ADDR_W, DATA_W) seqr;
      apb_random_stress_seq#(ADDR_W, DATA_W) seq;
      phase.raise_objection(this);
      seqr = env.get_master_sequencer(0);
      seq = new("seq");
      seq.num_txns = 200;
      seq.base_addr = 16'h0000;
      seq.span_bytes = 256;
      seq.enable_apb4 = m_cfg.is_apb4();
      seq.start(seqr);
      phase.drop_objection(this);
    endtask
  endclass

  class apb_b2b_apb4_strobe_mask_test extends apb_b2b_base_test;
    `uvm_component_utils(apb_b2b_apb4_strobe_mask_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
    virtual function void post_build_cfg();
      // Keep directed PSTRB/PPROT stable for this test.
      m_cfg.randomize_pstrb = 1'b0;
      m_cfg.randomize_pprot = 1'b0;
    endfunction
    task run_phase(uvm_phase phase);
      apb_sequencer#(ADDR_W, DATA_W) seqr;
      phase.raise_objection(this);
      if (!m_cfg.is_apb4()) begin
        `uvm_info("APB_TB", "Skipping APB4-only test in APB3 mode", UVM_LOW)
        phase.drop_objection(this);
        return;
      end
      seqr = env.get_master_sequencer(0);
      begin
        apb_apb4_strobe_mask_seq#(ADDR_W, DATA_W) seq;
        seq = new("seq");
        seq.addr = 16'h0010;
        seq.full_data = 32'hA5A5_5A5A;
        seq.mask_data = 32'hDEAD_BEEF;
        seq.strb = 4'b0001; // Update byte0 only (little-endian lane 0).
        seq.prot = 3'b000;
        seq.start(seqr);
      end
      phase.drop_objection(this);
    endtask
  endclass

  class apb_b2b_apb4_pprot_variation_test extends apb_b2b_base_test;
    `uvm_component_utils(apb_b2b_apb4_pprot_variation_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
    virtual function void post_build_cfg();
      m_cfg.randomize_pprot = 1'b1;
    endfunction
    task run_phase(uvm_phase phase);
      apb_sequencer#(ADDR_W, DATA_W) seqr;
      apb_random_stress_seq#(ADDR_W, DATA_W) seq;
      phase.raise_objection(this);
      if (!m_cfg.is_apb4()) begin
        `uvm_info("APB_TB", "Skipping APB4-only test in APB3 mode", UVM_LOW)
        phase.drop_objection(this);
        return;
      end
      seqr = env.get_master_sequencer(0);
      seq = new("seq");
      seq.num_txns = 500;
      seq.enable_apb4 = 1'b1;
      seq.start(seqr);
      phase.drop_objection(this);
    endtask
  endclass

  class apb_b2b_random_stress_test extends apb_b2b_base_test;
    `uvm_component_utils(apb_b2b_random_stress_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
    virtual function void post_build_cfg();
      s_cfg.allow_wait_states = 1'b1;
      s_cfg.min_wait_cycles = 0;
      s_cfg.max_wait_cycles = 8;
      if (m_cfg.is_apb4()) begin
        m_cfg.randomize_pstrb = 1'b1;
        m_cfg.randomize_pprot = 1'b1;
      end
    endfunction
    task run_phase(uvm_phase phase);
      apb_sequencer#(ADDR_W, DATA_W) seqr;
      apb_random_stress_seq#(ADDR_W, DATA_W) seq;
      phase.raise_objection(this);
      seqr = env.get_master_sequencer(0);
      seq = new("seq");
      seq.num_txns = 2000;
      seq.enable_apb4 = m_cfg.is_apb4();
      seq.start(seqr);
      phase.drop_objection(this);
    endtask
  endclass

endpackage
