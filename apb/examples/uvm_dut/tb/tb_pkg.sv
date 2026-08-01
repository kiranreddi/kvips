//------------------------------------------------------------------------------
// APB4 RTL-DUT verification package
//------------------------------------------------------------------------------

package tb_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import apb_types_pkg::*;
  import apb_uvm_pkg::*;

  class apb_dut_base_test extends uvm_test;
    `uvm_component_utils(apb_dut_base_test)

    localparam int ADDR_W = 16;
    localparam int DATA_W = 32;
    localparam int NSEL   = 1;

    typedef virtual apb_if #(ADDR_W, DATA_W, NSEL) apb_vif_t;
    apb_vif_t vif;

    apb_env_cfg#(ADDR_W, DATA_W, NSEL) env_cfg;
    apb_env#(ADDR_W, DATA_W, NSEL)      env;
    apb_scoreboard#(ADDR_W, DATA_W)     sb;
    apb_cfg#(ADDR_W, DATA_W, NSEL)      m_cfg;
    apb_cfg#(ADDR_W, DATA_W, NSEL)      s_cfg;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void post_build_cfg();
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);

`ifdef UVM_NO_DPI
      uvm_root::get().set_report_severity_id_action(UVM_WARNING, "UVM/COMP/NAME", UVM_NO_ACTION);
      uvm_root::get().set_report_severity_id_action(UVM_INFO, "UVM/COMP/NAMECHECK", UVM_NO_ACTION);
`endif

      if (!uvm_config_db#(virtual interface apb_if #(ADDR_W, DATA_W, NSEL))::get(this, "", "vif", vif)) begin
        `uvm_fatal("APB_DUT", "Missing vif in config DB (key: vif)")
      end

      env_cfg = apb_env_cfg#(ADDR_W, DATA_W, NSEL)::type_id::create("env_cfg");

      begin
        apb_agent_cfg#(ADDR_W, DATA_W, NSEL) a;
        m_cfg = apb_cfg#(ADDR_W, DATA_W, NSEL)::type_id::create("m_cfg");
        m_cfg.vif = vif;
        m_cfg.apply_plusargs();
        if ($test$plusargs("VIP_TRACE")) m_cfg.trace_enable = 1'b1;
        if ($test$plusargs("VIP_COV"))   m_cfg.coverage_enable = 1'b1;
        if ($test$plusargs("VIP_DROP_PSEL_OFF")) m_cfg.drop_psel_between = 1'b0;
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
        s_cfg.apply_plusargs();
        a = apb_agent_cfg#(ADDR_W, DATA_W, NSEL)::type_id::create("s_agent_cfg");
        a.set_role_slave();
        // The RTL DUT is the responder. Keep the VIP slave agent passive so it
        // cannot drive or mask the DUT response.
        a.is_active = UVM_PASSIVE;
        a.cfg = s_cfg;
        env_cfg.add_agent_cfg(a);
      end

      post_build_cfg();
      uvm_config_db#(apb_env_cfg#(ADDR_W, DATA_W, NSEL))::set(this, "env", "cfg", env_cfg);
      env = apb_env#(ADDR_W, DATA_W, NSEL)::type_id::create("env", this);
      sb  = apb_scoreboard#(ADDR_W, DATA_W)::type_id::create("sb", this);
    endfunction

    function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      env.ap.connect(sb.analysis_export);
    endfunction

    function void end_of_elaboration_phase(uvm_phase phase);
      super.end_of_elaboration_phase(phase);
      `uvm_info("APB_DUT",
        $sformatf("APB protocol=%s; RTL responder is active (use +APB_PROTOCOL=APB4)",
          m_cfg.is_apb4() ? "APB4" : "APB3"), UVM_LOW)
    endfunction

    task automatic settle(int unsigned cycles = 8);
      repeat (cycles) @(posedge vif.PCLK);
    endtask
  endclass

  class apb_dut_smoke_test extends apb_dut_base_test;
    `uvm_component_utils(apb_dut_smoke_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction

    task run_phase(uvm_phase phase);
      apb_smoke_rw_seq#(ADDR_W, DATA_W) seq;
      phase.raise_objection(this);
      seq = new("seq");
      seq.num_txns = 16;
      seq.base_addr = 16'h0000;
      seq.start(env.get_master_sequencer(0));
      settle();
      phase.drop_objection(this);
    endtask
  endclass

  class apb_dut_back_to_back_test extends apb_dut_base_test;
    `uvm_component_utils(apb_dut_back_to_back_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction

    virtual function void post_build_cfg();
      m_cfg.drop_psel_between = 1'b0;
    endfunction

    task run_phase(uvm_phase phase);
      apb_random_stress_seq#(ADDR_W, DATA_W) seq;
      phase.raise_objection(this);
      seq = new("seq");
      seq.num_txns = 160;
      seq.base_addr = 16'h0100;
      seq.span_bytes = 512;
      seq.wr_pct = 55;
      seq.enable_apb4 = 1'b1;
      seq.start(env.get_master_sequencer(0));
      settle();
      phase.drop_objection(this);
    endtask
  endclass

  class apb_dut_apb4_strobe_test extends apb_dut_base_test;
    `uvm_component_utils(apb_dut_apb4_strobe_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction

    task run_phase(uvm_phase phase);
      apb_apb4_strobe_mask_seq#(ADDR_W, DATA_W) seq;
      phase.raise_objection(this);
      if (!m_cfg.is_apb4()) begin
        `uvm_fatal("APB_DUT", "apb_dut_apb4_strobe_test requires +APB_PROTOCOL=APB4")
      end
      seq = new("seq");
      seq.addr = 16'h0020;
      seq.full_data = 32'hA5A5_5A5A;
      seq.mask_data = 32'h1122_3344;
      seq.strb = 4'b0101;
      seq.prot = 3'b001;
      seq.start(env.get_master_sequencer(0));
      settle();
      phase.drop_objection(this);
    endtask
  endclass

  class apb_dut_pprot_test extends apb_dut_base_test;
    `uvm_component_utils(apb_dut_pprot_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction

    task run_phase(uvm_phase phase);
      apb_random_stress_seq#(ADDR_W, DATA_W) seq;
      phase.raise_objection(this);
      if (!m_cfg.is_apb4()) begin
        `uvm_fatal("APB_DUT", "apb_dut_pprot_test requires +APB_PROTOCOL=APB4")
      end
      seq = new("seq");
      seq.num_txns = 96;
      seq.base_addr = 16'h0400;
      seq.span_bytes = 512;
      seq.wr_pct = 50;
      seq.enable_apb4 = 1'b1;
      seq.start(env.get_master_sequencer(0));
      settle();
      phase.drop_objection(this);
    endtask
  endclass

  class apb_dut_wait_seq extends uvm_sequence #(apb_item#(16, 32));
    `uvm_object_utils(apb_dut_wait_seq)
    localparam int MIN_WAIT = 2;

    function new(string name = "apb_dut_wait_seq"); super.new(name); endfunction

    task automatic transfer(bit do_write, logic [15:0] addr, logic [31:0] data);
      apb_item#(16, 32) tr;
      tr = apb_item#(16, 32)::type_id::create("tr");
      start_item(tr);
      tr.write = do_write;
      tr.addr = addr;
      tr.wdata = data;
      tr.strb = 4'hF;
      tr.prot = 3'b000;
      finish_item(tr);
      if (tr.wait_cycles < MIN_WAIT) begin
        `uvm_error("APB_DUT", $sformatf("Expected at least %0d wait cycles, saw %0d at 0x%0h",
          MIN_WAIT, tr.wait_cycles, addr))
      end
    endtask

    task body();
      transfer(1'b1, 16'h0600, 32'hCAFE_0001);
      transfer(1'b1, 16'h0604, 32'hCAFE_0002);
      transfer(1'b0, 16'h0600, 32'h0);
      transfer(1'b0, 16'h0604, 32'h0);
    endtask
  endclass

  class apb_dut_wait_state_test extends apb_dut_base_test;
    `uvm_component_utils(apb_dut_wait_state_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction

    task run_phase(uvm_phase phase);
      apb_dut_wait_seq seq;
      phase.raise_objection(this);
      seq = new("seq");
      seq.start(env.get_master_sequencer(0));
      settle();
      phase.drop_objection(this);
    endtask
  endclass

  class apb_dut_boundary_test extends apb_dut_base_test;
    `uvm_component_utils(apb_dut_boundary_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction

    task run_phase(uvm_phase phase);
      apb_apb4_strobe_mask_seq#(ADDR_W, DATA_W) seq;
      phase.raise_objection(this);
      seq = new("seq");
      seq.addr = 16'h0FFC;
      seq.full_data = 32'h0123_4567;
      seq.mask_data = 32'h89AB_CDEF;
      seq.strb = 4'hF;
      seq.prot = 3'b000;
      seq.start(env.get_master_sequencer(0));
      settle();
      phase.drop_objection(this);
    endtask
  endclass

  class apb_dut_error_seq extends uvm_sequence #(apb_item#(16, 32));
    `uvm_object_utils(apb_dut_error_seq)

    function new(string name = "apb_dut_error_seq"); super.new(name); endfunction

    task automatic check_transfer(bit do_write, logic [15:0] addr);
      apb_item#(16, 32) tr;
      tr = apb_item#(16, 32)::type_id::create("tr");
      start_item(tr);
      tr.write = do_write;
      tr.addr = addr;
      tr.wdata = 32'hDEAD_BEEF;
      tr.strb = 4'hF;
      tr.prot = 3'b000;
      finish_item(tr);
      if (!tr.slverr) begin
        `uvm_error("APB_DUT", $sformatf("Expected PSLVERR for unmapped %s at 0x%0h",
          do_write ? "write" : "read", addr))
      end
    endtask

    task body();
      check_transfer(1'b1, 16'h1000);
      check_transfer(1'b0, 16'h1000);
    endtask
  endclass

  class apb_dut_error_test extends apb_dut_base_test;
    `uvm_component_utils(apb_dut_error_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction

    task run_phase(uvm_phase phase);
      apb_dut_error_seq seq;
      phase.raise_objection(this);
      seq = new("seq");
      seq.start(env.get_master_sequencer(0));
      settle();
      phase.drop_objection(this);
    endtask
  endclass

  class apb_dut_stress_test extends apb_dut_base_test;
    `uvm_component_utils(apb_dut_stress_test)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction

    virtual function void post_build_cfg();
      m_cfg.randomize_pprot = 1'b1;
      m_cfg.randomize_pstrb = 1'b1;
    endfunction

    task run_phase(uvm_phase phase);
      apb_random_stress_seq#(ADDR_W, DATA_W) seq;
      phase.raise_objection(this);
      seq = new("seq");
      seq.num_txns = 256;
      seq.base_addr = 16'h0800;
      seq.span_bytes = 1024;
      seq.wr_pct = 60;
      seq.enable_apb4 = 1'b1;
      seq.start(env.get_master_sequencer(0));
      settle();
      phase.drop_objection(this);
    endtask
  endclass

endpackage
