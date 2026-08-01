`timescale 1ns/1ps

package tb_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import ahb_types_pkg::*;
  import ahb_uvm_pkg::*;

  class ahb_objtn_clear_catcher extends uvm_report_catcher;
    function new(string name = "ahb_objtn_clear_catcher");
      super.new(name);
    endfunction
    virtual function action_e catch();
      if (get_id() == "OBJTN_CLEAR") return CAUGHT;
      return THROW;
    endfunction
  endclass

  // Deterministic write/readback bursts keep the DUT gate independent of
  // random address collisions while exercising every INCR/WRAP length.
  class ahb_dut_burst_readback_seq #(
    int ADDR_W  = 32,
    int DATA_W  = 32,
    int HRESP_W = 2,
    bit WRAP    = 1'b0
  ) extends ahb_base_seq#(ADDR_W, DATA_W, HRESP_W);
    function new(string name = "ahb_dut_burst_readback_seq");
      super.new(name);
    endfunction

    task body();
      for (int unsigned k = 0; k < 3; k++) begin
        ahb_item#(ADDR_W, DATA_W, HRESP_W) wr;
        ahb_item#(ADDR_W, DATA_W, HRESP_W) rd;
        ahb_burst_e burst;
        int unsigned beats;
        logic [ADDR_W-1:0] base;
        burst = WRAP ? ((k == 0) ? AHB_BURST_WRAP4 : ((k == 1) ? AHB_BURST_WRAP8 : AHB_BURST_WRAP16))
                     : ((k == 0) ? AHB_BURST_INCR4 : ((k == 1) ? AHB_BURST_INCR8 : AHB_BURST_INCR16));
        beats = (k == 0) ? 4 : ((k == 1) ? 8 : 16);
        base = (k == 0) ? 16'h0100 : ((k == 1) ? 16'h0200 : 16'h0300);

        wr = ahb_item#(ADDR_W, DATA_W, HRESP_W)::type_id::create($sformatf("wr_%0d", k));
        start_item(wr);
        wr.write = 1'b1;
        wr.size  = AHB_SIZE_32;
        wr.burst = burst;
        wr.len   = beats;
        wr.addr  = base;
        wr.prot  = '0;
        wr.lock  = 1'b0;
        wr.wdata = new[beats];
        foreach (wr.wdata[j]) wr.wdata[j] = 32'h1000_0000 + (k * 32'h0010_0000) + j;
        finish_item(wr);

        rd = ahb_item#(ADDR_W, DATA_W, HRESP_W)::type_id::create($sformatf("rd_%0d", k));
        start_item(rd);
        rd.write = 1'b0;
        rd.size  = AHB_SIZE_32;
        rd.burst = burst;
        rd.len   = beats;
        rd.addr  = base;
        rd.prot  = '0;
        rd.lock  = 1'b0;
        finish_item(rd);
      end
    endtask
  endclass

  class ahb_dut_base_test extends uvm_test;
    `uvm_component_utils(ahb_dut_base_test)

    localparam int ADDR_W  = 16;
    localparam int DATA_W  = 32;
    localparam int HRESP_W = 2;

`ifdef VERILATOR
    virtual ahb_if #(.ADDR_W(ADDR_W), .DATA_W(DATA_W), .HRESP_W(HRESP_W)) vif;
`else
    typedef virtual ahb_if #(.ADDR_W(ADDR_W), .DATA_W(DATA_W), .HRESP_W(HRESP_W)) ahb_vif_t;
    ahb_vif_t vif;
`endif

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
          run_obj.set_drain_time(this, 20_000ns);
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

      begin
        ahb_agent_cfg#(ADDR_W, DATA_W, HRESP_W) a;
        m_cfg = ahb_cfg#(ADDR_W, DATA_W, HRESP_W)::type_id::create("m_cfg");
        m_cfg.vif = vif;
        m_cfg.apply_plusargs();
        a = ahb_agent_cfg#(ADDR_W, DATA_W, HRESP_W)::type_id::create("m_agent_cfg");
        a.set_role_master();
        a.is_active = UVM_ACTIVE;
        a.cfg = m_cfg;
        env_cfg.add_agent_cfg(a);
      end

      begin
        ahb_agent_cfg#(ADDR_W, DATA_W, HRESP_W) a;
        s_cfg = ahb_cfg#(ADDR_W, DATA_W, HRESP_W)::type_id::create("s_cfg");
        s_cfg.vif = vif;
        s_cfg.monitor_enable = 1'b0;
        a = ahb_agent_cfg#(ADDR_W, DATA_W, HRESP_W)::type_id::create("s_agent_cfg");
        a.set_role_slave();
        a.is_active = UVM_ACTIVE;
        a.is_slave = 1'b0;
        a.cfg = s_cfg;
        env_cfg.add_agent_cfg(a);
      end

      post_build_cfg();

      uvm_config_db#(ahb_env_cfg#(ADDR_W, DATA_W, HRESP_W))::set(this, "env", "cfg", env_cfg);
      env = ahb_env#(ADDR_W, DATA_W, HRESP_W)::type_id::create("env", this);
    endfunction
  endclass

  class ahb_dut_smoke_test extends ahb_dut_base_test;
    `uvm_component_utils(ahb_dut_smoke_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
    task run_phase(uvm_phase phase);
      ahb_sequencer#(ADDR_W, DATA_W, HRESP_W) seqr;
      ahb_smoke_seq#(ADDR_W, DATA_W, HRESP_W) seq;
      phase.raise_objection(this);
      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal("AHB_TB", "Master sequencer not found at index 0")
      seq = new("seq");
      seq.num_txns = $urandom_range(64, 24);
      `uvm_info("AHB_DUT_SUMMARY", $sformatf("txns=%0d", seq.num_txns), UVM_NONE)
      seq.start(seqr);
      wait (vif.HRESETn === 1'b1);
      repeat (128) @(posedge vif.HCLK);
      phase.drop_objection(this);
    endtask
  endclass

  class ahb_dut_incr_burst_test extends ahb_dut_base_test;
    `uvm_component_utils(ahb_dut_incr_burst_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
    task run_phase(uvm_phase phase);
      ahb_sequencer#(ADDR_W, DATA_W, HRESP_W) seqr;
      ahb_dut_burst_readback_seq#(ADDR_W, DATA_W, HRESP_W, 1'b0) seq;
      phase.raise_objection(this);
      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal("AHB_TB", "Master sequencer not found at index 0")
      seq = new("seq");
      `uvm_info("AHB_DUT_SUMMARY", "INCR4/8/16 write/readback", UVM_NONE)
      seq.start(seqr);
      wait (vif.HRESETn === 1'b1);
      repeat (256) @(posedge vif.HCLK);
      phase.drop_objection(this);
    endtask
  endclass

  class ahb_dut_wrap_burst_test extends ahb_dut_base_test;
    `uvm_component_utils(ahb_dut_wrap_burst_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
    task run_phase(uvm_phase phase);
      ahb_sequencer#(ADDR_W, DATA_W, HRESP_W) seqr;
      ahb_dut_burst_readback_seq#(ADDR_W, DATA_W, HRESP_W, 1'b1) seq;
      phase.raise_objection(this);
      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal("AHB_TB", "Master sequencer not found at index 0")
      seq = new("seq");
      `uvm_info("AHB_DUT_SUMMARY", "WRAP4/8/16 write/readback", UVM_NONE)
      seq.start(seqr);
      wait (vif.HRESETn === 1'b1);
      repeat (256) @(posedge vif.HCLK);
      phase.drop_objection(this);
    endtask
  endclass

  class ahb_dut_wait_state_test extends ahb_dut_base_test;
    `uvm_component_utils(ahb_dut_wait_state_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
    task run_phase(uvm_phase phase);
      ahb_sequencer#(ADDR_W, DATA_W, HRESP_W) seqr;
      ahb_wait_state_seq#(ADDR_W, DATA_W, HRESP_W) seq;
      phase.raise_objection(this);
      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal("AHB_TB", "Master sequencer not found at index 0")
      seq = new("seq");
      seq.num_txns = 64;
      seq.wr_pct = 50;
      `uvm_info("AHB_DUT_SUMMARY", $sformatf("txns=%0d wait_state_test=1", seq.num_txns), UVM_NONE)
      seq.start(seqr);
      wait (vif.HRESETn === 1'b1);
      repeat (256) @(posedge vif.HCLK);
      phase.drop_objection(this);
    endtask
  endclass

  class ahb_dut_stress_test extends ahb_dut_base_test;
    `uvm_component_utils(ahb_dut_stress_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
    task run_phase(uvm_phase phase);
      ahb_sequencer#(ADDR_W, DATA_W, HRESP_W) seqr;
      ahb_dut_burst_readback_seq#(ADDR_W, DATA_W, HRESP_W, 1'b0) seq;
      phase.raise_objection(this);
      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal("AHB_TB", "Master sequencer not found at index 0")
      seq = new("seq");
      `uvm_info("AHB_DUT_SUMMARY", "back-to-back burst readback stress", UVM_NONE)
      seq.start(seqr);
      wait (vif.HRESETn === 1'b1);
      repeat (512) @(posedge vif.HCLK);
      phase.drop_objection(this);
    endtask
  endclass

  class ahb_dut_full_mode_test extends ahb_dut_base_test;
    `uvm_component_utils(ahb_dut_full_mode_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
    task run_phase(uvm_phase phase);
      ahb_sequencer#(ADDR_W, DATA_W, HRESP_W) seqr;
      ahb_dut_burst_readback_seq#(ADDR_W, DATA_W, HRESP_W, 1'b0) seq;
      phase.raise_objection(this);
      seqr = env.get_master_sequencer(0);
      if (seqr == null) `uvm_fatal("AHB_TB", "Master sequencer not found at index 0")
      seq = new("seq");
      `uvm_info("AHB_DUT_SUMMARY", "AHB_FULL INCR burst readback", UVM_NONE)
      seq.start(seqr);
      wait (vif.HRESETn === 1'b1);
      repeat (512) @(posedge vif.HCLK);
      phase.drop_objection(this);
    endtask
  endclass

endpackage
