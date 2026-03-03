package tb_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import axi4_types_pkg::*;
  import axi4_uvm_pkg::*;

  class axi4_objtn_clear_catcher extends uvm_report_catcher;
    function new(string name = "axi4_objtn_clear_catcher");
      super.new(name);
    endfunction
    virtual function action_e catch();
      if (get_id() == "OBJTN_CLEAR") return CAUGHT;
      return THROW;
    endfunction
  endclass

  class axi4_real_base_test extends uvm_test;
    `uvm_component_utils(axi4_real_base_test)

    localparam int ADDR_W = 32;
    localparam int DATA_W = 64;
    localparam int ID_W   = 4;
    localparam int USER_W = 1;

`ifdef VERILATOR
    virtual axi4_if #(ADDR_W, DATA_W, ID_W, USER_W) vif;
`else
    typedef virtual axi4_if #(ADDR_W, DATA_W, ID_W, USER_W) axi4_vif_t;
    axi4_vif_t vif;
`endif

    axi4_env_cfg#(ADDR_W, DATA_W, ID_W, USER_W) env_cfg;
    axi4_env#(ADDR_W, DATA_W, ID_W, USER_W)     env;
    axi4_scoreboard#(ADDR_W, DATA_W, ID_W, USER_W) sb;

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
          run_obj.set_drain_time(this, 20_000ns);
        end
      end
      begin
        axi4_objtn_clear_catcher c;
        c = new();
        uvm_report_cb::add(null, c);
      end
`endif
`ifdef UVM_NO_DPI
      uvm_root::get().set_report_severity_id_action(UVM_WARNING, "UVM/COMP/NAME", UVM_NO_ACTION);
      uvm_root::get().set_report_severity_id_action(UVM_INFO, "UVM/COMP/NAMECHECK", UVM_NO_ACTION);
`endif

      if (!uvm_config_db#(virtual interface axi4_if #(ADDR_W, DATA_W, ID_W, USER_W))::get(this, "", "vif", vif)) begin
        `uvm_fatal(get_type_name(), "Missing vif in config DB (key: vif)")
      end

      env_cfg = axi4_env_cfg#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("env_cfg");

      begin
        axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W) m_cfg;
        m_cfg = axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("m_cfg");
        m_cfg.set_role_master();
        m_cfg.vif = vif;
        m_cfg.monitor_enable = 1'b1;
        env_cfg.add_agent_cfg(m_cfg);
      end

      begin
        axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W) s_cfg;
        s_cfg = axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("s_cfg");
        s_cfg.set_role_slave();
        s_cfg.vif = vif;
        s_cfg.is_slave = 1'b0;
        s_cfg.monitor_enable = 1'b0;
        s_cfg.slave_mem_enable = 1'b0;
        env_cfg.add_agent_cfg(s_cfg);
      end

      post_build_cfg();

      uvm_config_db#(axi4_env_cfg#(ADDR_W, DATA_W, ID_W, USER_W))::set(this, "env", "cfg", env_cfg);
      env = axi4_env#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("env", this);
      sb = axi4_scoreboard#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("sb", this);
    endfunction

    function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      env.ap.connect(sb.analysis_export);
    endfunction
  endclass

  class axi4_real_smoke_test extends axi4_real_base_test;
    `uvm_component_utils(axi4_real_smoke_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
    task run_phase(uvm_phase phase);
      axi4_sequencer#(ADDR_W, DATA_W, ID_W, USER_W) seqr;
      axi4_write_readback_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
      phase.raise_objection(this);
      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal(get_type_name(), "Master sequencer not found at index 0")
      seq = new("seq");
      seq.num_txns = $urandom_range(64, 32);
      seq.max_len  = 3;
      seq.enable_incr  = 1'b1;
      seq.enable_fixed = 1'b0;
      seq.enable_wrap  = 1'b0;
      seq.enable_narrow = 1'b0;
      `uvm_info("AXI4_DUT_SUMMARY", $sformatf("txns=%0d wr_txns=%0d rd_txns=%0d", seq.num_txns, seq.num_txns, seq.num_txns), UVM_NONE)
      seq.start(seqr);
      wait (vif.areset_n === 1'b1);
      repeat (128) @(posedge vif.aclk);
      phase.drop_objection(this);
    endtask
  endclass

  class axi4_real_burst_mix_test extends axi4_real_base_test;
    `uvm_component_utils(axi4_real_burst_mix_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
    task run_phase(uvm_phase phase);
      axi4_sequencer#(ADDR_W, DATA_W, ID_W, USER_W) seqr;
      axi4_write_readback_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
      phase.raise_objection(this);
      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal(get_type_name(), "Master sequencer not found at index 0")
      seq = new("seq");
      seq.num_txns = $urandom_range(128, 64);
      seq.max_len  = 7;
      seq.enable_incr  = 1'b1;
      seq.enable_fixed = 1'b1;
      seq.enable_wrap  = 1'b0;
      seq.enable_narrow = 1'b0;
      `uvm_info("AXI4_DUT_SUMMARY", $sformatf("txns=%0d wr_txns=%0d rd_txns=%0d", seq.num_txns, seq.num_txns, seq.num_txns), UVM_NONE)
      seq.start(seqr);
      wait (vif.areset_n === 1'b1);
      repeat (256) @(posedge vif.aclk);
      phase.drop_objection(this);
    endtask
  endclass

  class axi4_real_narrow_test extends axi4_real_base_test;
    `uvm_component_utils(axi4_real_narrow_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
    task run_phase(uvm_phase phase);
      axi4_sequencer#(ADDR_W, DATA_W, ID_W, USER_W) seqr;
      axi4_write_readback_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
      phase.raise_objection(this);
      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal(get_type_name(), "Master sequencer not found at index 0")
      seq = new("seq");
      seq.num_txns = $urandom_range(96, 48);
      seq.max_len  = 3;
      seq.enable_incr  = 1'b1;
      seq.enable_fixed = 1'b0;
      seq.enable_wrap  = 1'b0;
      seq.enable_narrow = 1'b1;
      `uvm_info("AXI4_DUT_SUMMARY", $sformatf("txns=%0d wr_txns=%0d rd_txns=%0d", seq.num_txns, seq.num_txns, seq.num_txns), UVM_NONE)
      seq.start(seqr);
      wait (vif.areset_n === 1'b1);
      repeat (192) @(posedge vif.aclk);
      phase.drop_objection(this);
    endtask
  endclass

  // DUT naming aliases (backward-compatible with *_real_* classes)
  class axi4_dut_smoke_test extends axi4_real_smoke_test;
    `uvm_component_utils(axi4_dut_smoke_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
  endclass

  class axi4_dut_burst_mix_test extends axi4_real_burst_mix_test;
    `uvm_component_utils(axi4_dut_burst_mix_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
  endclass

  class axi4_dut_narrow_test extends axi4_real_narrow_test;
    `uvm_component_utils(axi4_dut_narrow_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
  endclass

endpackage
