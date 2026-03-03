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
      if (get_id() == "OBJTN_CLEAR") return CAUGHT;
      return THROW;
    endfunction
  endclass

  class apb_real_base_test extends uvm_test;
    `uvm_component_utils(apb_real_base_test)

    localparam int ADDR_W = 16;
    localparam int DATA_W = 32;
    localparam int NSEL   = 1;

    typedef virtual apb_if #(ADDR_W, DATA_W, NSEL) apb_vif_t;
    apb_vif_t vif;

    apb_env_cfg#(ADDR_W, DATA_W, NSEL) env_cfg;
    apb_env#(ADDR_W, DATA_W, NSEL)     env;
    apb_scoreboard#(ADDR_W, DATA_W)    sb;
    apb_cfg#(ADDR_W, DATA_W, NSEL) m_cfg;
    apb_cfg#(ADDR_W, DATA_W, NSEL) s_cfg;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void post_build_cfg();
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);

`ifdef VERILATOR
      uvm_root::get().set_report_severity_id_action(UVM_WARNING, "OBJTN_CLEAR", UVM_NO_ACTION);
      begin
        uvm_phase run_phase;
        uvm_objection run_obj;
        run_phase = uvm_run_phase::get();
        run_obj = (run_phase == null) ? null : run_phase.get_objection();
        if (run_obj != null) begin
          run_obj.set_report_severity_id_action(UVM_WARNING, "OBJTN_CLEAR", UVM_NO_ACTION);
          run_obj.set_report_id_action("OBJTN_CLEAR", UVM_NO_ACTION);
          run_obj.set_drain_time(this, 20_000ns);
        end
      end
      begin
        apb_objtn_clear_catcher c;
        c = new();
        uvm_report_cb::add(null, c);
      end
`endif
`ifdef UVM_NO_DPI
      uvm_root::get().set_report_severity_id_action(UVM_WARNING, "UVM/COMP/NAME", UVM_NO_ACTION);
      uvm_root::get().set_report_severity_id_action(UVM_INFO, "UVM/COMP/NAMECHECK", UVM_NO_ACTION);
`endif

      if (!uvm_config_db#(virtual interface apb_if #(ADDR_W, DATA_W, NSEL))::get(this, "", "vif", vif)) begin
        `uvm_fatal("APB_TB", "Missing vif in config DB (key: vif)")
      end

      env_cfg = apb_env_cfg#(ADDR_W, DATA_W, NSEL)::type_id::create("env_cfg");

      begin
        apb_agent_cfg#(ADDR_W, DATA_W, NSEL) a;
        m_cfg = apb_cfg#(ADDR_W, DATA_W, NSEL)::type_id::create("m_cfg");
        m_cfg.vif = vif;
        m_cfg.apply_plusargs();
        a = apb_agent_cfg#(ADDR_W, DATA_W, NSEL)::type_id::create("m_agent_cfg");
        a.set_role_master();
        a.is_active = UVM_ACTIVE;
        a.cfg = m_cfg;
        env_cfg.add_agent_cfg(a);
      end

      begin
        apb_agent_cfg#(ADDR_W, DATA_W, NSEL) a;
        s_cfg = apb_cfg#(ADDR_W, DATA_W, NSEL)::type_id::create("s_cfg");
        s_cfg.vif = vif;
        s_cfg.monitor_enable = 1'b0;
        a = apb_agent_cfg#(ADDR_W, DATA_W, NSEL)::type_id::create("s_agent_cfg");
        a.set_role_slave();
        a.is_active = UVM_ACTIVE;
        a.is_slave = 1'b0;
        a.cfg = s_cfg;
        env_cfg.add_agent_cfg(a);
      end

      post_build_cfg();
      uvm_config_db#(apb_env_cfg#(ADDR_W, DATA_W, NSEL))::set(this, "env", "cfg", env_cfg);
      env = apb_env#(ADDR_W, DATA_W, NSEL)::type_id::create("env", this);
      sb = apb_scoreboard#(ADDR_W, DATA_W)::type_id::create("sb", this);
    endfunction

    function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      env.ap.connect(sb.analysis_export);
    endfunction
  endclass

  class apb_real_smoke_test extends apb_real_base_test;
    `uvm_component_utils(apb_real_smoke_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
    task run_phase(uvm_phase phase);
      apb_sequencer#(ADDR_W, DATA_W) seqr;
      apb_smoke_rw_seq#(ADDR_W, DATA_W) seq;
      `uvm_info("APB_TB", "apb_real_smoke_test run_phase start", UVM_LOW)
      phase.raise_objection(this);
      if ((env.agents.size() == 0) || (env.agents[0].m_drv == null) || (env.agents[0].sequencer == null))
        `uvm_fatal("APB_TB", "Master agent/driver/sequencer not constructed")
      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal("APB_TB", "Master sequencer not found at index 0")
      seq = new("seq");
      seq.num_txns = $urandom_range(24, 64);
      seq.base_addr = '0;
      seq.start(seqr);
      wait (vif.PRESETn === 1'b1);
      repeat (128) @(posedge vif.PCLK);
      phase.drop_objection(this);
    endtask
  endclass

  class apb_real_back_to_back_test extends apb_real_base_test;
    `uvm_component_utils(apb_real_back_to_back_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
    virtual function void post_build_cfg();
      m_cfg.drop_psel_between = 1'b0;
    endfunction
    task run_phase(uvm_phase phase);
      apb_sequencer#(ADDR_W, DATA_W) seqr;
      apb_random_stress_seq#(ADDR_W, DATA_W) seq;
      `uvm_info("APB_TB", "apb_real_back_to_back_test run_phase start", UVM_LOW)
      phase.raise_objection(this);
      if ((env.agents.size() == 0) || (env.agents[0].m_drv == null) || (env.agents[0].sequencer == null))
        `uvm_fatal("APB_TB", "Master agent/driver/sequencer not constructed")
      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal("APB_TB", "Master sequencer not found at index 0")
      seq = new("seq");
      seq.num_txns = $urandom_range(160, 320);
      seq.wr_pct = $urandom_range(40, 75);
      seq.enable_apb4 = m_cfg.is_apb4();
      seq.start(seqr);
      wait (vif.PRESETn === 1'b1);
      repeat (256) @(posedge vif.PCLK);
      phase.drop_objection(this);
    endtask
  endclass

  class apb_real_apb4_strobe_test extends apb_real_base_test;
    `uvm_component_utils(apb_real_apb4_strobe_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
    task run_phase(uvm_phase phase);
      apb_sequencer#(ADDR_W, DATA_W) seqr;
      `uvm_info("APB_TB", "apb_real_apb4_strobe_test run_phase start", UVM_LOW)
      phase.raise_objection(this);
      if (!m_cfg.is_apb4()) begin
        `uvm_info("APB_TB", "Skipping APB4-only test in APB3 mode", UVM_LOW)
        phase.drop_objection(this);
        return;
      end
      if ((env.agents.size() == 0) || (env.agents[0].m_drv == null) || (env.agents[0].sequencer == null))
        `uvm_fatal("APB_TB", "Master agent/driver/sequencer not constructed")
      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal("APB_TB", "Master sequencer not found at index 0")
      begin
        apb_apb4_strobe_mask_seq#(ADDR_W, DATA_W) seq;
        seq = new("seq");
        seq.addr = 16'h0010;
        seq.full_data = 32'h1122_3344;
        seq.mask_data = 32'hAABB_CCDD;
        seq.strb = 4'b0101;
        seq.prot = 3'b001;
        seq.start(seqr);
      end
      wait (vif.PRESETn === 1'b1);
      repeat (64) @(posedge vif.PCLK);
      phase.drop_objection(this);
    endtask
  endclass

endpackage
