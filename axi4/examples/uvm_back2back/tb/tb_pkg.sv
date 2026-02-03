//------------------------------------------------------------------------------
// Demo TB Package
//------------------------------------------------------------------------------

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
      if (get_id() == "OBJTN_CLEAR") begin
        return CAUGHT;
      end
      return THROW;
    endfunction
  endclass

  class axi4_b2b_base_test extends uvm_test;
    `uvm_component_utils(axi4_b2b_base_test)

    localparam int ADDR_W = 32;
    localparam int DATA_W = 64;
    localparam int ID_W   = 4;
    localparam int USER_W = 1;

    virtual interface axi4_if #(ADDR_W, DATA_W, ID_W, USER_W) vif;

    axi4_env_cfg#(ADDR_W, DATA_W, ID_W, USER_W) env_cfg;
    axi4_env#(ADDR_W, DATA_W, ID_W, USER_W)     env;
    axi4_txn_logger#(ADDR_W, DATA_W, ID_W, USER_W) logger;
    axi4_scoreboard#(ADDR_W, DATA_W, ID_W, USER_W) sb;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    // Hook for derived tests to tweak config after creation.
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

      // Agent 0: Master
      begin
        axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W) m_cfg;
        int unsigned mo;
        int unsigned win;
        m_cfg = axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("m_cfg");
        m_cfg.set_role_master();
        m_cfg.vif = vif;
        m_cfg.monitor_enable = 1'b1;
        if ($test$plusargs("VIP_TRACE")) m_cfg.trace_enable = 1'b1;
        if ($test$plusargs("VIP_TR")) m_cfg.tr_record_enable = 1'b1;
        if ($test$plusargs("VIP_PIPE")) m_cfg.master_pipelined = 1'b1;
        if ($test$plusargs("VIP_STATS")) m_cfg.stats_enable = 1'b1;
        win = 0;
        if ($value$plusargs("VIP_STATS_WIN=%d", win)) begin
          m_cfg.stats_enable = 1'b1;
          m_cfg.stats_window_cycles = win;
        end
        if ($test$plusargs("VIP_COV")) m_cfg.coverage_enable = 1'b1;
        mo = 0;
        if ($value$plusargs("VIP_MAX_OUTS=%d", mo)) begin
          if (mo != 0) begin
            m_cfg.max_outstanding_reads  = mo;
            m_cfg.max_outstanding_writes = mo;
          end
        end
        env_cfg.add_agent_cfg(m_cfg);
      end

      // Agent 1: Slave (memory model)
      begin
        axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W) s_cfg;
        s_cfg = axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("s_cfg");
        s_cfg.set_role_slave();
        s_cfg.vif = vif;
        // Disable to avoid duplicate monitoring when master+slave share a vif.
        s_cfg.monitor_enable = 1'b0;
        s_cfg.slave_mem_enable = 1'b1;
        s_cfg.slave_mem_bytes  = 256*1024;
        if ($test$plusargs("VIP_TRACE")) s_cfg.trace_enable = 1'b1;
        if ($test$plusargs("VIP_TR")) s_cfg.tr_record_enable = 1'b1;
        if ($test$plusargs("VIP_REORDER_B")) s_cfg.slave_reorder_b = 1'b1;
        if ($test$plusargs("VIP_INTERLEAVE_R")) s_cfg.slave_interleave_r = 1'b1;
        env_cfg.add_agent_cfg(s_cfg);
      end

      post_build_cfg();

      uvm_config_db#(axi4_env_cfg#(ADDR_W, DATA_W, ID_W, USER_W))::set(this, "env", "cfg", env_cfg);
      env = axi4_env#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("env", this);
      logger = axi4_txn_logger#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("logger", this);
      if ($test$plusargs("VIP_TRACE")) logger.enable = 1'b1;
      sb = axi4_scoreboard#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("sb", this);
    endfunction

    function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      env.ap.connect(logger.analysis_export);
      env.ap.connect(sb.analysis_export);
    endfunction
  endclass

  class axi4_b2b_smoke_test extends axi4_b2b_base_test;
    `uvm_component_utils(axi4_b2b_smoke_test)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
      axi4_sequencer#(ADDR_W, DATA_W, ID_W, USER_W) seqr;
      axi4_write_readback_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
      phase.raise_objection(this);

      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal(get_type_name(), "Master sequencer not found at index 0")

      seq = new("seq");
      seq.num_txns = 50;
      seq.max_len  = 7;
      seq.enable_incr  = 1'b1;
      seq.enable_fixed = 1'b0;
      seq.enable_wrap  = 1'b0;
      seq.enable_narrow = 1'b1;
      seq.start(seqr);

      phase.drop_objection(this);
    endtask
  endclass

  class axi4_b2b_burst_types_test extends axi4_b2b_base_test;
    `uvm_component_utils(axi4_b2b_burst_types_test)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
      axi4_sequencer#(ADDR_W, DATA_W, ID_W, USER_W) seqr;
      axi4_write_readback_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
      phase.raise_objection(this);

      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal(get_type_name(), "Master sequencer not found at index 0")

      seq = new("seq");
      seq.num_txns = 60;
      seq.max_len  = 7;
      seq.enable_incr  = 1'b1;
      seq.enable_fixed = 1'b1;
      seq.enable_wrap  = 1'b1;
      seq.enable_narrow = 1'b0;
      seq.start(seqr);

      phase.drop_objection(this);
    endtask
  endclass

  class axi4_b2b_backpressure_test extends axi4_b2b_base_test;
    `uvm_component_utils(axi4_b2b_backpressure_test)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void post_build_cfg();
      // Slave backpressure / latency knobs.
      env_cfg.agent_cfgs[1].ready_min = 0;
      env_cfg.agent_cfgs[1].ready_max = 5;
      env_cfg.agent_cfgs[1].resp_min  = 0;
      env_cfg.agent_cfgs[1].resp_max  = 10;
    endfunction

    task run_phase(uvm_phase phase);
      axi4_sequencer#(ADDR_W, DATA_W, ID_W, USER_W) seqr;
      axi4_write_readback_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
      phase.raise_objection(this);

      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal(get_type_name(), "Master sequencer not found at index 0")

      seq = new("seq");
      seq.num_txns = 100;
      seq.max_len  = 15;
      // Keep narrow off until lane/unaligned corner tests are expanded.
      seq.enable_narrow = 1'b0;
      seq.start(seqr);

      phase.drop_objection(this);
    endtask
  endclass

  class axi4_b2b_lane_sweep_test extends axi4_b2b_base_test;
    `uvm_component_utils(axi4_b2b_lane_sweep_test)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
      axi4_sequencer#(ADDR_W, DATA_W, ID_W, USER_W) seqr;
      axi4_lane_sweep_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
      phase.raise_objection(this);

      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal(get_type_name(), "Master sequencer not found at index 0")

      seq = new("seq");
      seq.base_addr = 32'h4000;
      seq.start(seqr);

      phase.drop_objection(this);
    endtask
  endclass

  class axi4_b2b_corner_case_test extends axi4_b2b_base_test;
    `uvm_component_utils(axi4_b2b_corner_case_test)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
      axi4_sequencer#(ADDR_W, DATA_W, ID_W, USER_W) seqr;
      axi4_corner_case_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
      phase.raise_objection(this);

      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal(get_type_name(), "Master sequencer not found at index 0")

      seq = new("seq");
      seq.base_addr = 32'h10000;
      seq.start(seqr);

      phase.drop_objection(this);
    endtask
  endclass

  class axi4_b2b_randomized_features_test extends axi4_b2b_base_test;
    `uvm_component_utils(axi4_b2b_randomized_features_test)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
      axi4_sequencer#(ADDR_W, DATA_W, ID_W, USER_W) seqr;
      axi4_write_readback_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
      phase.raise_objection(this);

      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal(get_type_name(), "Master sequencer not found at index 0")

      seq = new("seq");
      seq.num_txns = 200;
      seq.max_len  = 15;
      seq.enable_incr  = 1'b1;
      seq.enable_fixed = 1'b1;
      seq.enable_wrap  = 1'b1;
      seq.enable_narrow = 1'b1;
      seq.enable_random_id = 1'b1;
      seq.base_addr = 32'h8000;
      seq.start(seqr);

      phase.drop_objection(this);
    endtask
  endclass

  class axi4_b2b_pipelined_outstanding_test extends axi4_b2b_base_test;
    `uvm_component_utils(axi4_b2b_pipelined_outstanding_test)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void post_build_cfg();
      // Enable master pipelining and slave response scheduling to stress
      // outstanding + ID-based association in monitor/scoreboard.
      env_cfg.agent_cfgs[0].master_pipelined = 1'b1;
      env_cfg.agent_cfgs[0].max_outstanding_reads  = 8;
      env_cfg.agent_cfgs[0].max_outstanding_writes = 8;

      env_cfg.agent_cfgs[1].slave_reorder_b    = 1'b1;
      env_cfg.agent_cfgs[1].slave_interleave_r = 1'b1;
      env_cfg.agent_cfgs[1].ready_min = 0;
      env_cfg.agent_cfgs[1].ready_max = 3;
      env_cfg.agent_cfgs[1].resp_min  = 0;
      env_cfg.agent_cfgs[1].resp_max  = 5;
    endfunction

    task run_phase(uvm_phase phase);
      axi4_sequencer#(ADDR_W, DATA_W, ID_W, USER_W) seqr;
      axi4_pipelined_stress_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
      phase.raise_objection(this);

      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal(get_type_name(), "Master sequencer not found at index 0")

      seq = new("seq");
      seq.num_pairs = 200;
      seq.max_len   = 31;
      seq.enable_narrow = 1'b1;
      seq.enable_wrap   = 1'b1;
      seq.enable_fixed  = 1'b1;
      seq.enable_incr   = 1'b1;
      seq.base_addr     = 32'h10000;
      seq.start(seqr);

      phase.drop_objection(this);
    endtask
  endclass

  class axi4_b2b_pipelined_rready_backpressure_test extends axi4_b2b_base_test;
    `uvm_component_utils(axi4_b2b_pipelined_rready_backpressure_test)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void post_build_cfg();
      env_cfg.agent_cfgs[0].master_pipelined = 1'b1;
      env_cfg.agent_cfgs[0].max_outstanding_reads  = 8;
      env_cfg.agent_cfgs[0].max_outstanding_writes = 8;
      env_cfg.agent_cfgs[0].master_rready_random = 1'b1;
      env_cfg.agent_cfgs[0].master_rready_low_min = 1;
      env_cfg.agent_cfgs[0].master_rready_low_max = 5;

      env_cfg.agent_cfgs[1].slave_interleave_r = 1'b1;
      env_cfg.agent_cfgs[1].ready_min = 0;
      env_cfg.agent_cfgs[1].ready_max = 3;
      env_cfg.agent_cfgs[1].resp_min  = 0;
      env_cfg.agent_cfgs[1].resp_max  = 5;
    endfunction

    task run_phase(uvm_phase phase);
      axi4_sequencer#(ADDR_W, DATA_W, ID_W, USER_W) seqr;
      axi4_pipelined_stress_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
      phase.raise_objection(this);

      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal(get_type_name(), "Master sequencer not found at index 0")

      seq = new("seq");
      seq.num_pairs = 100;
      seq.max_len   = 15;
      seq.enable_narrow = 1'b1;
      seq.enable_wrap   = 1'b1;
      seq.enable_fixed  = 1'b1;
      seq.enable_incr   = 1'b1;
      seq.base_addr     = 32'h18000;
      seq.start(seqr);

      phase.drop_objection(this);
    endtask
  endclass

  class axi4_b2b_exclusive_basic_test extends axi4_b2b_base_test;
    `uvm_component_utils(axi4_b2b_exclusive_basic_test)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void post_build_cfg();
      // Keep master in non-pipelined mode to validate immediate response semantics.
      env_cfg.agent_cfgs[0].master_pipelined = 1'b0;
      env_cfg.agent_cfgs[1].slave_exclusive_enable = 1'b1;
    endfunction

    task run_phase(uvm_phase phase);
      axi4_sequencer#(ADDR_W, DATA_W, ID_W, USER_W) seqr;
      axi4_exclusive_basic_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
      phase.raise_objection(this);

      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal(get_type_name(), "Master sequencer not found at index 0")

      seq = new("seq");
      seq.addr = 32'h2000;
      seq.start(seqr);

      phase.drop_objection(this);
    endtask
  endclass

  class axi4_b2b_exclusive_fail_test extends axi4_b2b_base_test;
    `uvm_component_utils(axi4_b2b_exclusive_fail_test)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void post_build_cfg();
      env_cfg.agent_cfgs[0].master_pipelined = 1'b0;
      env_cfg.agent_cfgs[1].slave_exclusive_enable = 1'b1;
    endfunction

    task run_phase(uvm_phase phase);
      axi4_sequencer#(ADDR_W, DATA_W, ID_W, USER_W) seqr;
      axi4_exclusive_fail_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
      phase.raise_objection(this);

      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal(get_type_name(), "Master sequencer not found at index 0")

      seq = new("seq");
      seq.addr = 32'h3000;
      seq.start(seqr);

      phase.drop_objection(this);
    endtask
  endclass

  class axi4_b2b_error_write_test extends axi4_b2b_base_test;
    `uvm_component_utils(axi4_b2b_error_write_test)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void post_build_cfg();
      env_cfg.agent_cfgs[0].master_pipelined = 1'b0;
      env_cfg.agent_cfgs[1].slave_err_enable   = 1'b1;
      env_cfg.agent_cfgs[1].slave_err_on_write = 1'b1;
      env_cfg.agent_cfgs[1].slave_err_on_read  = 1'b0;
      env_cfg.agent_cfgs[1].slave_err_start    = 32'h4000;
      env_cfg.agent_cfgs[1].slave_err_end      = 32'h4000;
      env_cfg.agent_cfgs[1].slave_err_resp     = AXI4_RESP_DECERR;
    endfunction

    task run_phase(uvm_phase phase);
      axi4_sequencer#(ADDR_W, DATA_W, ID_W, USER_W) seqr;
      axi4_error_write_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
      phase.raise_objection(this);

      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal(get_type_name(), "Master sequencer not found at index 0")

      seq = new("seq");
      seq.addr = 32'h4000;
      seq.expected_bresp = AXI4_RESP_DECERR;
      seq.start(seqr);

      phase.drop_objection(this);
    endtask
  endclass

  class axi4_b2b_error_read_test extends axi4_b2b_base_test;
    `uvm_component_utils(axi4_b2b_error_read_test)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void post_build_cfg();
      env_cfg.agent_cfgs[0].master_pipelined = 1'b0;
      env_cfg.agent_cfgs[1].slave_err_enable   = 1'b1;
      env_cfg.agent_cfgs[1].slave_err_on_write = 1'b0;
      env_cfg.agent_cfgs[1].slave_err_on_read  = 1'b1;
      env_cfg.agent_cfgs[1].slave_err_start    = 32'h5000;
      env_cfg.agent_cfgs[1].slave_err_end      = 32'h5000;
      env_cfg.agent_cfgs[1].slave_err_resp     = AXI4_RESP_DECERR;
    endfunction

    task run_phase(uvm_phase phase);
      axi4_sequencer#(ADDR_W, DATA_W, ID_W, USER_W) seqr;
      axi4_error_read_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
      phase.raise_objection(this);

      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal(get_type_name(), "Master sequencer not found at index 0")

      seq = new("seq");
      seq.addr = 32'h5000;
      seq.expected_rresp = AXI4_RESP_DECERR;
      seq.start(seqr);

      phase.drop_objection(this);
    endtask
  endclass

  class axi4_b2b_incr_256beat_test extends axi4_b2b_base_test;
    `uvm_component_utils(axi4_b2b_incr_256beat_test)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void post_build_cfg();
      // Keep simple (no interleave/reorder) to validate long INCR bursts.
      env_cfg.agent_cfgs[0].master_pipelined = 1'b0;
      env_cfg.agent_cfgs[1].slave_reorder_b = 1'b0;
      env_cfg.agent_cfgs[1].slave_interleave_r = 1'b0;
    endfunction

    task run_phase(uvm_phase phase);
      axi4_sequencer#(ADDR_W, DATA_W, ID_W, USER_W) seqr;
      axi4_incr_256b_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
      phase.raise_objection(this);

      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal(get_type_name(), "Master sequencer not found at index 0")

      seq = new("seq");
      seq.num_txns = 6;
      seq.base_addr = 32'h6000;
      seq.start(seqr);

      phase.drop_objection(this);
    endtask
  endclass

  class axi4_b2b_exclusive_illegal_test extends axi4_b2b_base_test;
    `uvm_component_utils(axi4_b2b_exclusive_illegal_test)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void post_build_cfg();
      env_cfg.agent_cfgs[0].master_pipelined = 1'b0;
      env_cfg.agent_cfgs[1].slave_exclusive_enable = 1'b1;
      // Make exclusives "illegal" via a tighter slave restriction while keeping
      // protocol legality intact (so assertions remain enabled).
      env_cfg.agent_cfgs[1].slave_exclusive_max_bytes = 64;
    endfunction

    task run_phase(uvm_phase phase);
      axi4_sequencer#(ADDR_W, DATA_W, ID_W, USER_W) seqr;
      axi4_exclusive_illegal_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
      phase.raise_objection(this);

      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal(get_type_name(), "Master sequencer not found at index 0")

      seq = new("seq");
      seq.addr = 32'h7000;
      seq.start(seqr);

      phase.drop_objection(this);
    endtask
  endclass

  class axi4_b2b_delay_stress_test extends axi4_b2b_base_test;
    `uvm_component_utils(axi4_b2b_delay_stress_test)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void post_build_cfg();
      env_cfg.agent_cfgs[0].master_aw_delay_min = 0;
      env_cfg.agent_cfgs[0].master_aw_delay_max = 5;
      env_cfg.agent_cfgs[0].master_ar_delay_min = 0;
      env_cfg.agent_cfgs[0].master_ar_delay_max = 5;
      env_cfg.agent_cfgs[0].master_w_beat_gap_min = 0;
      env_cfg.agent_cfgs[0].master_w_beat_gap_max = 3;
      env_cfg.agent_cfgs[0].master_rready_random = 1'b0;

      env_cfg.agent_cfgs[1].ready_min = 0;
      env_cfg.agent_cfgs[1].ready_max = 5;
      env_cfg.agent_cfgs[1].resp_min  = 0;
      env_cfg.agent_cfgs[1].resp_max  = 10;
    endfunction

    task run_phase(uvm_phase phase);
      axi4_sequencer#(ADDR_W, DATA_W, ID_W, USER_W) seqr;
      axi4_write_readback_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
      phase.raise_objection(this);

      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal(get_type_name(), "Master sequencer not found at index 0")

      seq = new("seq");
      seq.num_txns = 80;
      seq.max_len  = 15;
      seq.enable_narrow = 1'b1;
      seq.enable_wrap   = 1'b1;
      seq.enable_fixed  = 1'b1;
      seq.enable_incr   = 1'b1;
      seq.enable_random_id = 1'b1;
      seq.base_addr = 32'h9000;
      seq.start(seqr);

      phase.drop_objection(this);
    endtask
  endclass

  class axi4_b2b_concurrent_rw_test extends axi4_b2b_base_test;
    `uvm_component_utils(axi4_b2b_concurrent_rw_test)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void post_build_cfg();
      env_cfg.agent_cfgs[0].master_pipelined = 1'b1;
      env_cfg.agent_cfgs[0].max_outstanding_reads  = 8;
      env_cfg.agent_cfgs[0].max_outstanding_writes = 8;
      env_cfg.agent_cfgs[0].stats_enable = 1'b1;

      env_cfg.agent_cfgs[1].slave_reorder_b    = 1'b1;
      env_cfg.agent_cfgs[1].slave_interleave_r = 1'b1;
      env_cfg.agent_cfgs[1].ready_min = 0;
      env_cfg.agent_cfgs[1].ready_max = 3;
      env_cfg.agent_cfgs[1].resp_min  = 0;
      env_cfg.agent_cfgs[1].resp_max  = 5;
    endfunction

    task run_phase(uvm_phase phase);
      axi4_sequencer#(ADDR_W, DATA_W, ID_W, USER_W) seqr;
      axi4_concurrent_rw_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
      phase.raise_objection(this);

      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal(get_type_name(), "Master sequencer not found at index 0")

      seq = new("seq");
      seq.num_prefill = 32;
      seq.num_mixed   = 250;
      seq.num_b_writes = 40;
      seq.base_a = 32'hA000;
      seq.base_b = 32'hB000;
      seq.start(seqr);

      phase.drop_objection(this);
    endtask
  endclass

  // Backward-compatible name (smoke).
  class axi4_b2b_test extends axi4_b2b_smoke_test;
    `uvm_component_utils(axi4_b2b_test)
    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction
  endclass

  // Debug/reference: manual item driving (kept as a known-good fallback).
  class axi4_b2b_manual_test extends axi4_b2b_base_test;
    `uvm_component_utils(axi4_b2b_manual_test)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
      axi4_sequencer#(ADDR_W, DATA_W, ID_W, USER_W) seqr;
      phase.raise_objection(this);

      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal(get_type_name(), "Master sequencer not found at index 0")

      for (int unsigned t = 0; t < 10; t++) begin
        axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) wr;
        axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) rd;
        axi4_item_seq#(ADDR_W, DATA_W, ID_W, USER_W) wr_seq;
        axi4_item_seq#(ADDR_W, DATA_W, ID_W, USER_W) rd_seq;

        wr = new($sformatf("wr_%0d", t));
        rd = new($sformatf("rd_%0d", t));

        wr.is_write = 1;
        wr.id       = '0;
        wr.addr     = 32'h1000 + t*(DATA_W/8);
      `ifdef VERILATOR
        /* verilator lint_off WIDTHTRUNC */
        /* verilator lint_off WIDTHEXPAND */
      `endif
        wr.len      = $urandom_range(0, 7);
        wr.size     = $clog2(DATA_W/8);
        wr.burst    = AXI4_BURST_INCR;
        wr.user     = '0;
        wr.allocate_payload();
        for (int unsigned i = 0; i < wr.num_beats(); i++) begin
          wr.data[i] = {$urandom(), $urandom()};
          if (DATA_W <= 32) wr.data[i] = $urandom();
          wr.strb[i] = '1;
        end
      `ifdef VERILATOR
        /* verilator lint_on WIDTHEXPAND */
        /* verilator lint_on WIDTHTRUNC */
      `endif

        wr_seq = new($sformatf("wr_seq_%0d", t));
        wr_seq.item = wr;
        wr_seq.start(seqr);

        rd.is_write = 0;
        rd.id       = wr.id;
        rd.addr     = wr.addr;
        rd.len      = wr.len;
        rd.size     = wr.size;
        rd.burst    = wr.burst;
        rd.user     = wr.user;
        rd.allocate_payload();

        rd_seq = new($sformatf("rd_seq_%0d", t));
        rd_seq.item = rd;
        rd_seq.start(seqr);
      end

      phase.drop_objection(this);
    endtask
  endclass

endpackage
