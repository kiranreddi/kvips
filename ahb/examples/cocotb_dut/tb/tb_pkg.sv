//------------------------------------------------------------------------------
// AHB cocotb bridge test — serves Python commands via UVM VIP
//------------------------------------------------------------------------------

package tb_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import ahb_types_pkg::*;
  import ahb_uvm_pkg::*;
  import kvips_cocotb_dpi_pkg::*;

  `include "kvips_cocotb_opcodes.svh"

  class ahb_objtn_clear_catcher extends uvm_report_catcher;
    function new(string name = "ahb_objtn_clear_catcher");
      super.new(name);
    endfunction
    virtual function action_e catch();
      if (get_id() == "OBJTN_CLEAR") return CAUGHT;
      return THROW;
    endfunction
  endclass

  class ahb_cocotb_item_seq extends uvm_sequence #(ahb_item#(16, 32, 2));
    `uvm_object_utils(ahb_cocotb_item_seq)
    ahb_item#(16, 32, 2) item;
    function new(string name = "ahb_cocotb_item_seq");
      super.new(name);
    endfunction
    task body();
      start_item(item);
      finish_item(item);
    endtask
  endclass

  class ahb_cocotb_bridge_test extends uvm_test;
    `uvm_component_utils(ahb_cocotb_bridge_test)

    localparam int ADDR_W  = 16;
    localparam int DATA_W  = 32;
    localparam int HRESP_W = 2;

`ifdef VERILATOR
    virtual ahb_if #(.ADDR_W(ADDR_W), .DATA_W(DATA_W), .HRESP_W(HRESP_W)) vif;
`else
    typedef virtual ahb_if #(.ADDR_W(ADDR_W), .DATA_W(DATA_W), .HRESP_W(HRESP_W)) ahb_vif_t;
    ahb_vif_t vif;
`endif
    typedef virtual kvips_cocotb_bridge_if bridge_vif_t;
    bridge_vif_t bif;

    ahb_env_cfg#(ADDR_W, DATA_W, HRESP_W) env_cfg;
    ahb_env#(ADDR_W, DATA_W, HRESP_W)     env;
    ahb_cfg#(ADDR_W, DATA_W, HRESP_W) m_cfg;
    ahb_cfg#(ADDR_W, DATA_W, HRESP_W) s_cfg;

    longint unsigned cmd_count;
    longint unsigned mon_count;
    bit finish_req;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);

`ifdef VERILATOR
      uvm_root::get().set_report_severity_id_action(UVM_WARNING, "OBJTN_CLEAR", UVM_NO_ACTION);
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

      kvips_dpi_reset();
      kvips_dpi_log("AHB cocotb bridge build_phase");

      if (!uvm_config_db#(virtual interface ahb_if #(.ADDR_W(ADDR_W), .DATA_W(DATA_W), .HRESP_W(HRESP_W)))::get(this, "", "vif", vif))
        `uvm_fatal("AHB_COCOTB", "Missing AHB vif")
      if (!uvm_config_db#(virtual interface kvips_cocotb_bridge_if)::get(this, "", "bridge", bif))
        `uvm_fatal("AHB_COCOTB", "Missing cocotb bridge vif")

      env_cfg = ahb_env_cfg#(ADDR_W, DATA_W, HRESP_W)::type_id::create("env_cfg");

      begin
        ahb_agent_cfg#(ADDR_W, DATA_W, HRESP_W) a;
        m_cfg = ahb_cfg#(ADDR_W, DATA_W, HRESP_W)::type_id::create("m_cfg");
        m_cfg.vif = vif;
        m_cfg.insert_busy = 1'b1;
        m_cfg.busy_pct = 40;
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

      uvm_config_db#(ahb_env_cfg#(ADDR_W, DATA_W, HRESP_W))::set(this, "env", "cfg", env_cfg);
      env = ahb_env#(ADDR_W, DATA_W, HRESP_W)::type_id::create("env", this);
    endfunction

    task automatic publish_mon(bit write, logic [63:0] addr, logic [63:0] data,
                               int resp, int strb);
      bif.mon_proto = KVIPS_PROTO_AHB;
      bif.mon_write = write;
      bif.mon_addr  = addr;
      bif.mon_data  = data;
      bif.mon_resp  = resp;
      bif.mon_strb  = strb;
      bif.mon_len   = 0;
      bif.mon_id    = 0;
      bif.mon_valid = 1'b1;
      kvips_dpi_mon_push(int'(KVIPS_PROTO_AHB), int'(write), longint'(addr),
                         longint'(data), resp, strb, 0, 0);
      mon_count++;
      @(posedge bif.clk);
      bif.mon_valid = 1'b0;
    endtask

    task automatic do_item(ahb_item#(ADDR_W, DATA_W, HRESP_W) tr);
      ahb_cocotb_item_seq iseq;
      iseq = ahb_cocotb_item_seq::type_id::create("iseq");
      iseq.item = tr;
      iseq.start(env.get_master_sequencer(0));
      if (tr.write)
        publish_mon(1'b1, tr.addr, (tr.wdata.size() ? tr.wdata[0] : 0),
                    (tr.resp.size() ? int'(tr.resp[0]) : 0), 0);
      else
        publish_mon(1'b0, tr.addr, (tr.rdata.size() ? tr.rdata[0] : 0),
                    (tr.resp.size() ? int'(tr.resp[0]) : 0), 0);
    endtask

    task automatic respond(logic [31:0] status, logic [63:0] d0 = 0, logic [63:0] d1 = 0,
                           logic [63:0] d2 = 0, logic [63:0] d3 = 0);
      bif.rsp_status = status;
      bif.rsp_d0 = d0; bif.rsp_d1 = d1; bif.rsp_d2 = d2; bif.rsp_d3 = d3;
      kvips_dpi_rsp_push(int'(status), longint'(d0), longint'(d1), longint'(d2), longint'(d3));
      bif.rsp_valid = 1'b1;
      repeat (8) @(posedge bif.clk);
      bif.rsp_valid = 1'b0;
    endtask

    task automatic serve_cmd();
      logic [7:0] op;
      logic [63:0] a0, a1, a2, a3, a4, a5;
      ahb_item#(ADDR_W, DATA_W, HRESP_W) tr;
      op = bif.req_opcode;
      a0 = bif.req_a0; a1 = bif.req_a1; a2 = bif.req_a2;
      a3 = bif.req_a3; a4 = bif.req_a4; a5 = bif.req_a5;
      cmd_count++;
      bif.req_ready = 1'b1;
      @(posedge bif.clk);
      bif.req_ready = 1'b0;

      case (op)
        KVIPS_OP_PING: respond(KVIPS_RSP_OK, 64'h4B564950);
        KVIPS_OP_GET_STATS: respond(KVIPS_RSP_OK, cmd_count, mon_count);
        KVIPS_OP_FINISH: begin finish_req = 1'b1; respond(KVIPS_RSP_OK); end

        KVIPS_AHB_WRITE: begin
          tr = ahb_item#(ADDR_W, DATA_W, HRESP_W)::type_id::create("wr");
          tr.write = 1'b1;
          tr.addr = ADDR_W'(a0);
          tr.size = ahb_size_e'(a2);
          tr.burst = ahb_burst_e'(a3);
          tr.prot = 4'(a4);
          tr.nonsec = a5[0];
          tr.lock = 1'b0;
          tr.len = 1;
          tr.wdata = new[1];
          tr.wdata[0] = DATA_W'(a1);
          do_item(tr);
          respond(KVIPS_RSP_OK, (tr.resp.size() ? tr.resp[0] : 0));
        end

        KVIPS_AHB_READ: begin
          tr = ahb_item#(ADDR_W, DATA_W, HRESP_W)::type_id::create("rd");
          tr.write = 1'b0;
          tr.addr = ADDR_W'(a0);
          tr.size = ahb_size_e'(a2);
          tr.burst = ahb_burst_e'(a3);
          tr.prot = 4'(a4);
          tr.nonsec = a5[0];
          tr.lock = 1'b0;
          tr.len = 1;
          do_item(tr);
          respond(KVIPS_RSP_OK, (tr.rdata.size() ? tr.rdata[0] : 0),
                  (tr.resp.size() ? tr.resp[0] : 0));
        end

        KVIPS_AHB_SEQ_SMOKE: begin
          ahb_smoke_seq#(ADDR_W, DATA_W, HRESP_W) seq;
          seq = new("smoke");
          seq.num_txns = int'(a0);
          seq.base_addr = ADDR_W'(a1 & ~64'h3FF); // force 1KB align
          seq.span_bytes = 1024;
          seq.wr_pct = int'(a2);
          kvips_dpi_log($sformatf("AHB SEQ_SMOKE start num=%0d base=0x%0h", seq.num_txns, seq.base_addr));
          seq.start(env.get_master_sequencer(0));
          kvips_dpi_log("AHB SEQ_SMOKE done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AHB_SEQ_SINGLE: begin
          ahb_single_rw_seq#(ADDR_W, DATA_W, HRESP_W) seq;
          seq = new("single");
          seq.num_txns = int'(a0);
          seq.base_addr = ADDR_W'(a1 & ~64'h3FF);
          seq.span_bytes = 1024;
          seq.wr_pct = int'(a2);
          kvips_dpi_log($sformatf("AHB SEQ_SINGLE start num=%0d base=0x%0h", seq.num_txns, seq.base_addr));
          seq.start(env.get_master_sequencer(0));
          kvips_dpi_log("AHB SEQ_SINGLE done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AHB_SEQ_INCR: begin
          ahb_incr_burst_seq#(ADDR_W, DATA_W, HRESP_W) seq;
          seq = new("incr");
          seq.num_txns = int'(a0);
          seq.base_addr = ADDR_W'(a1 & ~64'h3FF);
          seq.span_bytes = 1024;
          kvips_dpi_log($sformatf("AHB SEQ_INCR start num=%0d base=0x%0h", seq.num_txns, seq.base_addr));
          seq.start(env.get_master_sequencer(0));
          kvips_dpi_log("AHB SEQ_INCR done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AHB_SEQ_WRAP: begin
          ahb_wrap_burst_seq#(ADDR_W, DATA_W, HRESP_W) seq;
          seq = new("wrap");
          seq.num_txns = int'(a0);
          seq.base_addr = ADDR_W'(a1 & ~64'h3FF);
          seq.span_bytes = 1024;
          kvips_dpi_log($sformatf("AHB SEQ_WRAP start num=%0d base=0x%0h", seq.num_txns, seq.base_addr));
          seq.start(env.get_master_sequencer(0));
          kvips_dpi_log("AHB SEQ_WRAP done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AHB_SEQ_B2B: begin
          ahb_back_to_back_seq#(ADDR_W, DATA_W, HRESP_W) seq;
          seq = new("b2b");
          seq.num_txns = int'(a0);
          seq.base_addr = ADDR_W'(a1 & ~64'h3FF);
          seq.span_bytes = 1024;
          seq.wr_pct = int'(a2);
          kvips_dpi_log($sformatf("AHB SEQ_B2B start num=%0d base=0x%0h", seq.num_txns, seq.base_addr));
          seq.start(env.get_master_sequencer(0));
          kvips_dpi_log("AHB SEQ_B2B done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AHB_SEQ_WAIT: begin
          ahb_wait_state_seq#(ADDR_W, DATA_W, HRESP_W) seq;
          seq = new("wait");
          seq.num_txns = int'(a0);
          seq.base_addr = ADDR_W'(a1 & ~64'h3FF);
          seq.span_bytes = 1024;
          kvips_dpi_log($sformatf("AHB SEQ_WAIT start num=%0d base=0x%0h", seq.num_txns, seq.base_addr));
          seq.start(env.get_master_sequencer(0));
          kvips_dpi_log("AHB SEQ_WAIT done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AHB_SEQ_STRESS: begin
          ahb_random_stress_seq#(ADDR_W, DATA_W, HRESP_W) seq;
          seq = new("stress");
          seq.num_txns = int'(a0);
          seq.base_addr = ADDR_W'(a1 & ~64'h3FF);
          seq.span_bytes = 1024;
          seq.wr_pct = int'(a2);
          kvips_dpi_log($sformatf("AHB SEQ_STRESS start num=%0d base=0x%0h", seq.num_txns, seq.base_addr));
          seq.start(env.get_master_sequencer(0));
          kvips_dpi_log("AHB SEQ_STRESS done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AHB_SEQ_BUSY: begin
          ahb_busy_seq#(ADDR_W, DATA_W, HRESP_W) seq;
          seq = new("busy");
          seq.base_addr = ADDR_W'(a1 & ~64'h3FF);
          seq.span_bytes = 1024;
          kvips_dpi_log("AHB SEQ_BUSY start");
          seq.start(env.get_master_sequencer(0));
          kvips_dpi_log("AHB SEQ_BUSY done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AHB_SEQ_BOUNDARY: begin
          // Legal 1KB-edge INCR4 at 0x3F0 (does not cross the boundary).
          ahb_boundary_seq#(ADDR_W, DATA_W, HRESP_W) seq;
          seq = new("boundary");
          kvips_dpi_log("AHB SEQ_BOUNDARY start");
          seq.start(env.get_master_sequencer(0));
          kvips_dpi_log("AHB SEQ_BOUNDARY done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AHB_SEQ_ENDIAN: begin
          ahb_endian_seq#(ADDR_W, DATA_W, HRESP_W) seq;
          seq = new("endian");
          seq.endian = AHB_ENDIAN_LITTLE;
          kvips_dpi_log("AHB SEQ_ENDIAN start");
          seq.start(env.get_master_sequencer(0));
          kvips_dpi_log("AHB SEQ_ENDIAN done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AHB_SEQ_FULL_RESP: begin
          ahb_full_response_seq#(ADDR_W, DATA_W, HRESP_W) seq;
          seq = new("full_resp");
          seq.expected_resp = AHB_RESP_OKAY;
          kvips_dpi_log("AHB SEQ_FULL_RESP start");
          seq.start(env.get_master_sequencer(0));
          kvips_dpi_log("AHB SEQ_FULL_RESP done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AHB_SEQ_SECURITY,
        KVIPS_AHB_SEQ_ERROR: begin
          kvips_dpi_log($sformatf("AHB opcode 0x%0h unsupported on RAM DUT (needs policy/err slave)", op));
          respond(KVIPS_RSP_INVAL);
        end

        default: begin
          `uvm_error("AHB_COCOTB", $sformatf("Unknown opcode 0x%0h", op))
          respond(KVIPS_RSP_INVAL);
        end
      endcase
    endtask

    task run_phase(uvm_phase phase);
      phase.raise_objection(this);
      bif.bridge_ready = 1'b0;
      bif.req_ready = 1'b0;
      bif.rsp_valid = 1'b0;
      bif.mon_valid = 1'b0;
      wait (bif.rst_n === 1'b1);
      repeat (5) @(posedge bif.clk);
      bif.bridge_ready = 1'b1;
      kvips_dpi_log("AHB cocotb bridge ready");

      finish_req = 1'b0;
      while (!finish_req) begin
        @(posedge bif.clk);
        if (bif.req_valid) serve_cmd();
      end

      repeat (10) @(posedge bif.clk);
      bif.bridge_ready = 1'b0;
      kvips_dpi_log("AHB cocotb bridge finished");
      phase.drop_objection(this);
    endtask

    function void report_phase(uvm_phase phase);
      bit en;
      longint unsigned wr_cnt, rd_cnt, err_cnt, mis_cnt;
      super.report_phase(phase);
      if (env != null && env.sb != null) begin
        env.sb.get_summary(en, wr_cnt, rd_cnt, err_cnt, mis_cnt);
        `uvm_info("AHB_COCOTB",
          $sformatf("cmds=%0d mon_dpi=%0d sb_wr=%0d sb_rd=%0d sb_mis=%0d",
            cmd_count, mon_count, wr_cnt, rd_cnt, mis_cnt), UVM_LOW)
        if (en && ((wr_cnt + rd_cnt) == 0) && cmd_count > 2)
          `uvm_error("AHB_COCOTB", "Scoreboard saw zero transactions after traffic")
      end
    endfunction
  endclass

endpackage
