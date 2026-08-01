//------------------------------------------------------------------------------
// APB cocotb bridge test — serves Python commands via UVM VIP
//------------------------------------------------------------------------------

package tb_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import apb_types_pkg::*;
  import apb_uvm_pkg::*;
  import kvips_cocotb_dpi_pkg::*;

  `include "kvips_cocotb_opcodes.svh"

  // One-item sequence helper for Python-driven single transfers
  class apb_cocotb_item_seq extends uvm_sequence #(apb_item#(16, 32));
    `uvm_object_utils(apb_cocotb_item_seq)
    apb_item#(16, 32) item;
    function new(string name = "apb_cocotb_item_seq");
      super.new(name);
    endfunction
    task body();
      start_item(item);
      finish_item(item);
    endtask
  endclass

  class apb_cocotb_bridge_test extends uvm_test;
    `uvm_component_utils(apb_cocotb_bridge_test)

    localparam int ADDR_W = 16;
    localparam int DATA_W = 32;
    localparam int NSEL   = 1;
    localparam int STRB_W = DATA_W/8;

    typedef virtual apb_if #(ADDR_W, DATA_W, NSEL) apb_vif_t;
    typedef virtual kvips_cocotb_bridge_if bridge_vif_t;

    apb_vif_t    vif;
    bridge_vif_t bif;

    apb_env_cfg#(ADDR_W, DATA_W, NSEL) env_cfg;
    apb_env#(ADDR_W, DATA_W, NSEL)      env;
    apb_scoreboard#(ADDR_W, DATA_W)     sb;
    apb_cfg#(ADDR_W, DATA_W, NSEL)      m_cfg;
    apb_cfg#(ADDR_W, DATA_W, NSEL)      s_cfg;

    longint unsigned cmd_count;
    longint unsigned mon_count;
    bit finish_req;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);

`ifdef UVM_NO_DPI
      uvm_root::get().set_report_severity_id_action(UVM_WARNING, "UVM/COMP/NAME", UVM_NO_ACTION);
      uvm_root::get().set_report_severity_id_action(UVM_INFO, "UVM/COMP/NAMECHECK", UVM_NO_ACTION);
`endif

      kvips_dpi_reset();
      kvips_dpi_log("APB cocotb bridge build_phase");

      if (!uvm_config_db#(virtual interface apb_if #(ADDR_W, DATA_W, NSEL))::get(this, "", "vif", vif))
        `uvm_fatal("APB_COCOTB", "Missing APB vif")
      if (!uvm_config_db#(virtual interface kvips_cocotb_bridge_if)::get(this, "", "bridge", bif))
        `uvm_fatal("APB_COCOTB", "Missing cocotb bridge vif")

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
        s_cfg.apply_plusargs();
        a = apb_agent_cfg#(ADDR_W, DATA_W, NSEL)::type_id::create("s_agent_cfg");
        a.set_role_slave();
        a.is_active = UVM_PASSIVE;
        a.cfg = s_cfg;
        env_cfg.add_agent_cfg(a);
      end

      uvm_config_db#(apb_env_cfg#(ADDR_W, DATA_W, NSEL))::set(this, "env", "cfg", env_cfg);
      env = apb_env#(ADDR_W, DATA_W, NSEL)::type_id::create("env", this);
      sb  = apb_scoreboard#(ADDR_W, DATA_W)::type_id::create("sb", this);
    endfunction

    function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      env.ap.connect(sb.analysis_export);
    endfunction

    task automatic publish_mon(bit write, logic [63:0] addr, logic [63:0] data,
                               int resp, int strb);
      bif.mon_proto = KVIPS_PROTO_APB;
      bif.mon_write = write;
      bif.mon_addr  = addr;
      bif.mon_data  = data;
      bif.mon_resp  = resp;
      bif.mon_strb  = strb;
      bif.mon_len   = 0;
      bif.mon_id    = 0;
      bif.mon_valid = 1'b1;
      kvips_dpi_mon_push(int'(KVIPS_PROTO_APB), int'(write), longint'(addr),
                         longint'(data), resp, strb, 0, 0);
      mon_count++;
      @(posedge bif.clk);
      bif.mon_valid = 1'b0;
    endtask

    task automatic do_item(bit write, logic [ADDR_W-1:0] addr, logic [DATA_W-1:0] wdata,
                           logic [STRB_W-1:0] strb, logic [2:0] prot,
                           output logic [DATA_W-1:0] rdata);
      apb_cocotb_item_seq iseq;
      apb_item#(ADDR_W, DATA_W) tr;
      tr = apb_item#(ADDR_W, DATA_W)::type_id::create("tr");
      tr.write = write;
      tr.addr  = addr;
      tr.wdata = wdata;
      tr.strb  = strb;
      tr.prot  = prot;
      iseq = apb_cocotb_item_seq::type_id::create("iseq");
      iseq.item = tr;
      iseq.start(env.get_master_sequencer(0));
      rdata = tr.rdata;
      publish_mon(write, addr, write ? wdata : rdata, int'(tr.slverr), int'(strb));
    endtask

    task automatic respond(logic [31:0] status, logic [63:0] d0 = 0, logic [63:0] d1 = 0,
                           logic [63:0] d2 = 0, logic [63:0] d3 = 0);
      bif.rsp_status = status;
      bif.rsp_d0 = d0;
      bif.rsp_d1 = d1;
      bif.rsp_d2 = d2;
      bif.rsp_d3 = d3;
      kvips_dpi_rsp_push(int'(status), longint'(d0), longint'(d1), longint'(d2), longint'(d3));
      bif.rsp_valid = 1'b1;
      repeat (8) @(posedge bif.clk);
      bif.rsp_valid = 1'b0;
    endtask

    task automatic serve_cmd();
      logic [7:0] op;
      logic [63:0] a0, a1, a2, a3, a4;
      logic [DATA_W-1:0] rdata;
      op = bif.req_opcode;
      a0 = bif.req_a0; a1 = bif.req_a1; a2 = bif.req_a2; a3 = bif.req_a3; a4 = bif.req_a4;
      cmd_count++;
      bif.req_ready = 1'b1;
      @(posedge bif.clk);
      bif.req_ready = 1'b0;

      case (op)
        KVIPS_OP_PING: begin
          respond(KVIPS_RSP_OK, 64'h4B564950);
        end
        KVIPS_OP_GET_STATS: begin
          respond(KVIPS_RSP_OK, cmd_count, mon_count);
        end
        KVIPS_OP_FINISH: begin
          finish_req = 1'b1;
          respond(KVIPS_RSP_OK);
        end
        KVIPS_APB_WRITE: begin
          do_item(1'b1, ADDR_W'(a0), DATA_W'(a1), STRB_W'(a2), 3'(a3), rdata);
          respond(KVIPS_RSP_OK);
        end
        KVIPS_APB_READ: begin
          do_item(1'b0, ADDR_W'(a0), '0, '1, 3'(a3), rdata);
          respond(KVIPS_RSP_OK, rdata);
        end
        KVIPS_APB_SEQ_SMOKE: begin
          apb_smoke_rw_seq#(ADDR_W, DATA_W) seq;
          seq = new("smoke");
          seq.num_txns = int'(a0);
          seq.base_addr = ADDR_W'(a1);
          seq.start(env.get_master_sequencer(0));
          respond(KVIPS_RSP_OK);
        end
        KVIPS_APB_SEQ_STRESS: begin
          apb_random_stress_seq#(ADDR_W, DATA_W) seq;
          seq = new("stress");
          seq.num_txns = int'(a0);
          seq.base_addr = ADDR_W'(a1);
          seq.span_bytes = int'(a2);
          seq.wr_pct = int'(a3);
          seq.enable_apb4 = 1'b1;
          seq.start(env.get_master_sequencer(0));
          respond(KVIPS_RSP_OK);
        end
        KVIPS_APB_SEQ_STROBE: begin
          apb_apb4_strobe_mask_seq#(ADDR_W, DATA_W) seq;
          seq = new("strobe");
          seq.addr = ADDR_W'(a0);
          seq.full_data = DATA_W'(a1);
          seq.mask_data = DATA_W'(a2);
          seq.strb = STRB_W'(a3);
          seq.prot = 3'(a4);
          seq.start(env.get_master_sequencer(0));
          respond(KVIPS_RSP_OK);
        end
        default: begin
          `uvm_error("APB_COCOTB", $sformatf("Unknown opcode 0x%0h", op))
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
      kvips_dpi_log("APB cocotb bridge ready");

      // Stay alive for the whole cocotb regression. FINISH is optional; cocotb
      // ends the simulation when all Python tests complete.
      finish_req = 1'b0;
      while (!finish_req) begin
        @(posedge bif.clk);
        if (bif.req_valid) begin
          serve_cmd();
        end
      end

      repeat (10) @(posedge bif.clk);
      bif.bridge_ready = 1'b0;
      kvips_dpi_log("APB cocotb bridge finished");
      phase.drop_objection(this);
    endtask

    function void report_phase(uvm_phase phase);
      bit en;
      longint unsigned wr_cnt, rd_cnt, err_cnt, mis;
      super.report_phase(phase);
      sb.get_summary(en, wr_cnt, rd_cnt, err_cnt, mis);
      `uvm_info("APB_COCOTB",
        $sformatf("cmds=%0d mon_dpi=%0d sb_wr=%0d sb_rd=%0d sb_err=%0d sb_mis=%0d",
          cmd_count, mon_count, wr_cnt, rd_cnt, err_cnt, mis), UVM_LOW)
      if (en && ((wr_cnt + rd_cnt) == 0) && cmd_count > 2)
        `uvm_error("APB_COCOTB", "Scoreboard saw zero transactions after traffic")
    endfunction
  endclass

endpackage
