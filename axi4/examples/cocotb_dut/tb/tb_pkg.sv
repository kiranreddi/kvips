//------------------------------------------------------------------------------
// AXI4 cocotb bridge test — serves Python commands via UVM VIP
//------------------------------------------------------------------------------

package tb_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import axi4_types_pkg::*;
  import axi4_uvm_pkg::*;
  import kvips_cocotb_dpi_pkg::*;

  `include "kvips_cocotb_opcodes.svh"

  class axi4_objtn_clear_catcher extends uvm_report_catcher;
    function new(string name = "axi4_objtn_clear_catcher");
      super.new(name);
    endfunction
    virtual function action_e catch();
      if (get_id() == "OBJTN_CLEAR") return CAUGHT;
      return THROW;
    endfunction
  endclass

  class axi4_cocotb_bridge_test extends uvm_test;
    `uvm_component_utils(axi4_cocotb_bridge_test)

    localparam int ADDR_W = 32;
    localparam int DATA_W = 64;
    localparam int ID_W   = 4;
    localparam int USER_W = 1;
    localparam int STRB_W = DATA_W/8;

`ifdef VERILATOR
    virtual axi4_if #(ADDR_W, DATA_W, ID_W, USER_W) vif;
`else
    typedef virtual axi4_if #(ADDR_W, DATA_W, ID_W, USER_W) axi4_vif_t;
    axi4_vif_t vif;
`endif
    typedef virtual kvips_cocotb_bridge_if bridge_vif_t;
    bridge_vif_t bif;

    axi4_env_cfg#(ADDR_W, DATA_W, ID_W, USER_W) env_cfg;
    axi4_env#(ADDR_W, DATA_W, ID_W, USER_W)     env;
    axi4_scoreboard#(ADDR_W, DATA_W, ID_W, USER_W) sb;

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
        axi4_objtn_clear_catcher c;
        c = new();
        uvm_report_cb::add(null, c);
      end
`endif
`ifdef UVM_NO_DPI
      uvm_root::get().set_report_severity_id_action(UVM_WARNING, "UVM/COMP/NAME", UVM_NO_ACTION);
      uvm_root::get().set_report_severity_id_action(UVM_INFO, "UVM/COMP/NAMECHECK", UVM_NO_ACTION);
`endif

      kvips_dpi_reset();
      kvips_dpi_log("AXI4 cocotb bridge build_phase");

      if (!uvm_config_db#(virtual interface axi4_if #(ADDR_W, DATA_W, ID_W, USER_W))::get(this, "", "vif", vif))
        `uvm_fatal("AXI4_COCOTB", "Missing AXI4 vif")
      if (!uvm_config_db#(virtual interface kvips_cocotb_bridge_if)::get(this, "", "bridge", bif))
        `uvm_fatal("AXI4_COCOTB", "Missing cocotb bridge vif")

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

      uvm_config_db#(axi4_env_cfg#(ADDR_W, DATA_W, ID_W, USER_W))::set(this, "env", "cfg", env_cfg);
      env = axi4_env#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("env", this);
      sb  = axi4_scoreboard#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("sb", this);
    endfunction

    function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      env.ap.connect(sb.analysis_export);
    endfunction

    task automatic publish_mon(bit write, logic [63:0] addr, logic [63:0] data,
                               int resp, int strb, int len, int id);
      bif.mon_proto = KVIPS_PROTO_AXI4;
      bif.mon_write = write;
      bif.mon_addr  = addr;
      bif.mon_data  = data;
      bif.mon_resp  = resp;
      bif.mon_strb  = strb;
      bif.mon_len   = len;
      bif.mon_id    = id;
      bif.mon_valid = 1'b1;
      kvips_dpi_mon_push(int'(KVIPS_PROTO_AXI4), int'(write), longint'(addr),
                         longint'(data), resp, strb, len, id);
      mon_count++;
      @(posedge bif.clk);
      bif.mon_valid = 1'b0;
    endtask

    task automatic do_item(axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) tr);
      axi4_item_seq#(ADDR_W, DATA_W, ID_W, USER_W) iseq;
      iseq = axi4_item_seq#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("iseq");
      iseq.item = tr;
      iseq.start(env.get_master_sequencer(0));
      if (tr.is_write)
        publish_mon(1'b1, tr.addr, (tr.data.size() ? tr.data[0] : 0), int'(tr.bresp),
                    (tr.strb.size() ? int'(tr.strb[0]) : 0), int'(tr.len), int'(tr.id));
      else
        publish_mon(1'b0, tr.addr, (tr.data.size() ? tr.data[0] : 0),
                    (tr.rresp.size() ? int'(tr.rresp[0]) : 0), 0, int'(tr.len), int'(tr.id));
    endtask

    task automatic respond(logic [31:0] status, logic [63:0] d0 = 0, logic [63:0] d1 = 0,
                           logic [63:0] d2 = 0, logic [63:0] d3 = 0);
      bif.rsp_status = status;
      bif.rsp_d0 = d0; bif.rsp_d1 = d1; bif.rsp_d2 = d2; bif.rsp_d3 = d3;
      // DPI mailbox is the reliable completion path; IF pulse is best-effort.
      kvips_dpi_rsp_push(int'(status), longint'(d0), longint'(d1), longint'(d2), longint'(d3));
      bif.rsp_valid = 1'b1;
      repeat (8) @(posedge bif.clk);
      bif.rsp_valid = 1'b0;
    endtask

    task automatic serve_cmd();
      logic [7:0] op;
      logic [63:0] a0, a1, a2, a3, a4, a5, a6, a7;
      axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) tr;
      int unsigned nbeats;
      // Latch the full request while req_valid is stable.
      op = bif.req_opcode;
      a0 = bif.req_a0; a1 = bif.req_a1; a2 = bif.req_a2; a3 = bif.req_a3;
      a4 = bif.req_a4; a5 = bif.req_a5; a6 = bif.req_a6; a7 = bif.req_a7;
      cmd_count++;
      bif.req_ready = 1'b1;
      @(posedge bif.clk);
      bif.req_ready = 1'b0;

      case (op)
        KVIPS_OP_PING: respond(KVIPS_RSP_OK, 64'h4B564950);
        KVIPS_OP_GET_STATS: respond(KVIPS_RSP_OK, cmd_count, mon_count);
        KVIPS_OP_FINISH: begin finish_req = 1'b1; respond(KVIPS_RSP_OK); end

        KVIPS_AXI4_WRITE: begin
          tr = axi4_item#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("wr");
          tr.is_write = 1'b1;
          tr.addr = ADDR_W'(a0);
          tr.len = 0;
          tr.size = 3'(a2);
          tr.id = ID_W'(a3);
          tr.burst = AXI4_BURST_INCR;
          tr.allocate_payload();
          tr.data[0] = DATA_W'(a1);
          tr.strb[0] = STRB_W'(a4);
          do_item(tr);
          respond(KVIPS_RSP_OK, tr.bresp);
        end

        KVIPS_AXI4_READ: begin
          tr = axi4_item#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("rd");
          tr.is_write = 1'b0;
          tr.addr = ADDR_W'(a0);
          tr.len = 0;
          tr.size = 3'(a2);
          tr.id = ID_W'(a3);
          tr.burst = AXI4_BURST_INCR;
          tr.allocate_payload();
          do_item(tr);
          respond(KVIPS_RSP_OK, tr.data[0], (tr.rresp.size() ? tr.rresp[0] : 0));
        end

        KVIPS_AXI4_WRITE_BURST: begin
          nbeats = int'(a1) + 1;
          tr = axi4_item#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("wbr");
          tr.is_write = 1'b1;
          tr.addr = ADDR_W'(a0);
          tr.len = 8'(a1);
          tr.size = 3'(a2);
          tr.id = ID_W'(a3);
          tr.burst = AXI4_BURST_INCR;
          tr.allocate_payload();
          for (int i = 0; i < nbeats; i++) begin
            tr.data[i] = DATA_W'(bif.beat_data[i]);
            tr.strb[i] = STRB_W'(bif.beat_strb[i] != 0 ? bif.beat_strb[i] : a4);
          end
          do_item(tr);
          respond(KVIPS_RSP_OK, tr.bresp);
        end

        KVIPS_AXI4_READ_BURST: begin
          nbeats = int'(a1) + 1;
          tr = axi4_item#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("rbr");
          tr.is_write = 1'b0;
          tr.addr = ADDR_W'(a0);
          tr.len = 8'(a1);
          tr.size = 3'(a2);
          tr.id = ID_W'(a3);
          tr.burst = AXI4_BURST_INCR;
          tr.allocate_payload();
          do_item(tr);
          for (int i = 0; i < nbeats; i++)
            bif.rsp_beat[i] = (i < tr.data.size()) ? tr.data[i] : 64'h0;
          respond(KVIPS_RSP_OK, (tr.rresp.size() ? tr.rresp[0] : 0));
        end

        KVIPS_AXI4_SEQ_WRB: begin
          axi4_write_readback_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
          seq = axi4_write_readback_seq#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("wrb");
          seq.num_txns = int'(a0);
          seq.base_addr = ADDR_W'(a1);
          seq.max_len = int'(a2);
          seq.enable_incr = 1'b1;
          seq.enable_fixed = 1'b0;
          seq.enable_wrap = 1'b0;
          seq.enable_narrow = 1'b0;
          kvips_dpi_log($sformatf("AXI4 SEQ_WRB start num=%0d base=0x%0h max_len=%0d", seq.num_txns, seq.base_addr, seq.max_len));
          seq.start(env.get_master_sequencer(0));
          kvips_dpi_log("AXI4 SEQ_WRB done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AXI4_SEQ_WBRST: begin
          // Directed bursts — avoid item.randomize() (needs Verilator+z3).
          int unsigned n_txns;
          int unsigned max_len_i;
          logic [ADDR_W-1:0] start_a;
          n_txns = int'(a0);
          start_a = ADDR_W'(a1);
          max_len_i = int'(a2);
          kvips_dpi_log($sformatf("AXI4 SEQ_WBRST start num=%0d addr=0x%0h max_len=%0d", n_txns, start_a, max_len_i));
          for (int unsigned t = 0; t < n_txns; t++) begin
            axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) wr;
            int unsigned len_i;
            len_i = (max_len_i == 0) ? 0 : (t % (max_len_i + 1));
            wr = axi4_item#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create($sformatf("wbrst_%0d", t));
            wr.is_write = 1'b1;
            wr.addr = start_a + t * STRB_W;
            wr.len = 8'(len_i);
            wr.size = $clog2(STRB_W);
            wr.id = ID_W'(t);
            wr.burst = AXI4_BURST_INCR;
            wr.allocate_payload();
            for (int unsigned i = 0; i < wr.num_beats(); i++) begin
              wr.data[i] = DATA_W'(64'hB000_0000 + (t << 8) + i);
              wr.strb[i] = '1;
            end
            do_item(wr);
          end
          kvips_dpi_log("AXI4 SEQ_WBRST done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AXI4_SEQ_RBRST: begin
          int unsigned n_txns;
          int unsigned max_len_i;
          logic [ADDR_W-1:0] start_a;
          n_txns = int'(a0);
          start_a = ADDR_W'(a1);
          max_len_i = int'(a2);
          kvips_dpi_log($sformatf("AXI4 SEQ_RBRST start num=%0d addr=0x%0h max_len=%0d", n_txns, start_a, max_len_i));
          for (int unsigned t = 0; t < n_txns; t++) begin
            axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) rd;
            int unsigned len_i;
            len_i = (max_len_i == 0) ? 0 : (t % (max_len_i + 1));
            rd = axi4_item#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create($sformatf("rbrst_%0d", t));
            rd.is_write = 1'b0;
            rd.addr = start_a + t * STRB_W;
            rd.len = 8'(len_i);
            rd.size = $clog2(STRB_W);
            rd.id = ID_W'(t);
            rd.burst = AXI4_BURST_INCR;
            rd.allocate_payload();
            do_item(rd);
          end
          kvips_dpi_log("AXI4 SEQ_RBRST done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AXI4_SEQ_STRESS: begin
          // Cocotb bridge keeps the master non-pipelined so Python write/read
          // and write_readback sequences complete before the next item.
          // axi4_pipelined_stress_seq requires get_response() from a pipelined
          // master, so stress here is a heavier write_readback pass.
          axi4_write_readback_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
          seq = axi4_write_readback_seq#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("stress");
          seq.num_txns = int'(a0);
          seq.base_addr = ADDR_W'(a1);
          seq.max_len = int'(a2);
          seq.enable_incr = 1'b1;
          seq.enable_fixed = 1'b0;
          seq.enable_wrap = 1'b0;
          seq.enable_narrow = 1'b0;
          kvips_dpi_log($sformatf("AXI4 SEQ_STRESS start num=%0d base=0x%0h max_len=%0d", seq.num_txns, seq.base_addr, seq.max_len));
          seq.start(env.get_master_sequencer(0));
          kvips_dpi_log("AXI4 SEQ_STRESS done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AXI4_SEQ_LANE: begin
          axi4_lane_sweep_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
          seq = axi4_lane_sweep_seq#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("lane");
          seq.base_addr = ADDR_W'(a0);
          kvips_dpi_log($sformatf("AXI4 SEQ_LANE start base=0x%0h", seq.base_addr));
          seq.start(env.get_master_sequencer(0));
          kvips_dpi_log("AXI4 SEQ_LANE done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AXI4_SEQ_STROBE: begin
          axi4_strobe_patterns_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
          seq = axi4_strobe_patterns_seq#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("strobe");
          seq.base_addr = ADDR_W'(a0);
          kvips_dpi_log($sformatf("AXI4 SEQ_STROBE start base=0x%0h", seq.base_addr));
          seq.start(env.get_master_sequencer(0));
          kvips_dpi_log("AXI4 SEQ_STROBE done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AXI4_SEQ_CONCURRENT: begin
          // Non-pipelined-safe mixed traffic: prefill writes, then reads +
          // extra writes. (Library concurrent_rw_seq needs pipelined responses.)
          int unsigned n_prefill;
          int unsigned n_mixed;
          logic [ADDR_W-1:0] base_a;
          n_prefill = int'(a0);
          n_mixed = int'(a1);
          base_a = ADDR_W'(a2);
          kvips_dpi_log($sformatf("AXI4 SEQ_CONCURRENT start prefill=%0d mixed=%0d base=0x%0h",
                                  n_prefill, n_mixed, base_a));
          for (int unsigned i = 0; i < n_prefill; i++) begin
            axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) wr;
            wr = axi4_item#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create($sformatf("c_wr_%0d", i));
            wr.is_write = 1'b1;
            wr.addr = base_a + i * STRB_W;
            wr.len = 0;
            wr.size = $clog2(STRB_W);
            wr.id = ID_W'(i);
            wr.burst = AXI4_BURST_INCR;
            wr.allocate_payload();
            wr.data[0] = DATA_W'(64'hA5A5_0000 + i);
            wr.strb[0] = '1;
            do_item(wr);
          end
          for (int unsigned k = 0; k < n_mixed; k++) begin
            if ((k % 2) == 0) begin
              axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) rd;
              int unsigned idx;
              idx = (n_prefill == 0) ? 0 : (k % n_prefill);
              rd = axi4_item#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create($sformatf("c_rd_%0d", k));
              rd.is_write = 1'b0;
              rd.addr = base_a + idx * STRB_W;
              rd.len = 0;
              rd.size = $clog2(STRB_W);
              rd.id = ID_W'(k);
              rd.burst = AXI4_BURST_INCR;
              rd.allocate_payload();
              do_item(rd);
            end else begin
              axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) wr;
              wr = axi4_item#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create($sformatf("c_mix_wr_%0d", k));
              wr.is_write = 1'b1;
              wr.addr = base_a + 16'h800 + (k * STRB_W);
              wr.len = 0;
              wr.size = $clog2(STRB_W);
              wr.id = ID_W'(k);
              wr.burst = AXI4_BURST_INCR;
              wr.allocate_payload();
              wr.data[0] = DATA_W'(64'hC0C0_0000 + k);
              wr.strb[0] = '1;
              do_item(wr);
            end
          end
          kvips_dpi_log("AXI4 SEQ_CONCURRENT done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AXI4_SEQ_UNALIGNED: begin
          axi4_unaligned_byte_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
          seq = axi4_unaligned_byte_seq#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("unaligned");
          seq.base_addr = ADDR_W'(a0);
          kvips_dpi_log($sformatf("AXI4 SEQ_UNALIGNED start base=0x%0h", seq.base_addr));
          seq.start(env.get_master_sequencer(0));
          kvips_dpi_log("AXI4 SEQ_UNALIGNED done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AXI4_SEQ_CORNER: begin
          // Library axi4_corner_case_seq issues a 256-beat size=0 transfer,
          // too heavy for CI under Verilator. Directed stand-in: medium INCR +
          // edge-of-4KB INCR/FIXED/WRAP inside 64KB RAM.
          logic [ADDR_W-1:0] base4k;
          axi4_burst_e bursts[$];
          base4k = ADDR_W'((a0 != 0 ? a0 : 64'hE000) & ~64'hFFF);
          kvips_dpi_log($sformatf("AXI4 SEQ_CORNER start base4k=0x%0h", base4k));
          begin
            axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) wr, rd;
            wr = axi4_item#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("corner_mid");
            wr.is_write = 1'b1; wr.id = '0; wr.addr = base4k; wr.len = 8'd31;
            wr.size = 3'd0; wr.burst = AXI4_BURST_INCR; wr.allocate_payload();
            for (int unsigned i = 0; i < wr.num_beats(); i++) begin
              wr.data[i] = DATA_W'(64'hC000_0000 + i); wr.strb[i] = '1;
            end
            do_item(wr);
            rd = axi4_item#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("corner_mid_rd");
            rd.is_write = 1'b0; rd.id = '0; rd.addr = wr.addr; rd.len = wr.len;
            rd.size = wr.size; rd.burst = wr.burst; rd.allocate_payload();
            do_item(rd);
          end
          bursts.push_back(AXI4_BURST_INCR);
          bursts.push_back(AXI4_BURST_FIXED);
          bursts.push_back(AXI4_BURST_WRAP);
          foreach (bursts[bi]) begin
            axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) wr, rd;
            int unsigned size, len, bpb, total, max_off, off;
            logic [ADDR_W-1:0] addr;
            size = (bi == 0) ? 0 : ((bi == 1) ? 1 : $clog2(STRB_W));
            len  = (bursts[bi] == AXI4_BURST_INCR) ? 7 : 3;
            bpb = 1 << size; total = (len + 1) * bpb;
            max_off = (total >= 4096) ? 0 : (4096 - total);
            off = (max_off / bpb) * bpb;
            addr = base4k + off;
            if (bursts[bi] == AXI4_BURST_WRAP) addr = ADDR_W'((longint'(addr) / total) * total);
            wr = axi4_item#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create($sformatf("corner_edge_%0d", bi));
            wr.is_write = 1'b1; wr.id = ID_W'(bi); wr.addr = addr; wr.len = len[7:0];
            wr.size = size[2:0]; wr.burst = bursts[bi]; wr.allocate_payload();
            for (int unsigned i = 0; i < wr.num_beats(); i++) begin
              wr.data[i] = DATA_W'(64'hE000_0000 + bi*256 + i); wr.strb[i] = '1;
            end
            do_item(wr);
            rd = axi4_item#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create($sformatf("corner_edge_rd_%0d", bi));
            rd.is_write = 1'b0; rd.id = wr.id; rd.addr = wr.addr; rd.len = wr.len;
            rd.size = wr.size; rd.burst = wr.burst; rd.allocate_payload();
            do_item(rd);
          end
          kvips_dpi_log("AXI4 SEQ_CORNER done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AXI4_SEQ_INCR256: begin
          // Library axi4_incr_256b_seq urandoms len up to 255, too heavy for CI
          // under Verilator. Directed stand-in: full-width INCR16 write+readback.
          int unsigned n;
          logic [ADDR_W-1:0] base;
          n = (int'(a0) == 0) ? 1 : int'(a0);
          if (n > 2) n = 2;
          base = ADDR_W'(a1 != 0 ? a1 : 64'h6000);
          kvips_dpi_log($sformatf("AXI4 SEQ_INCR256 start num=%0d base=0x%0h", n, base));
          for (int unsigned t = 0; t < n; t++) begin
            axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) wr, rd;
            wr = axi4_item#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create($sformatf("incr_wr_%0d", t));
            wr.is_write = 1'b1; wr.id = ID_W'(t); wr.addr = base + t * 256;
            wr.len = 8'd15; wr.size = $clog2(STRB_W); wr.burst = AXI4_BURST_INCR;
            wr.allocate_payload();
            for (int unsigned i = 0; i < wr.num_beats(); i++) begin
              wr.data[i] = DATA_W'(64'h2560_0000 + t*64 + i); wr.strb[i] = '1;
            end
            do_item(wr);
            rd = axi4_item#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create($sformatf("incr_rd_%0d", t));
            rd.is_write = 1'b0; rd.id = wr.id; rd.addr = wr.addr; rd.len = wr.len;
            rd.size = wr.size; rd.burst = wr.burst; rd.allocate_payload();
            do_item(rd);
          end
          kvips_dpi_log("AXI4 SEQ_INCR256 done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AXI4_SEQ_PHASE_API: begin
          axi4_phase_api_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
          seq = axi4_phase_api_seq#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("phase");
          seq.base_addr = ADDR_W'(a0 != 0 ? a0 : 64'hD000);
          kvips_dpi_log($sformatf("AXI4 SEQ_PHASE_API start base=0x%0h", seq.base_addr));
          seq.start(env.get_master_sequencer(0));
          kvips_dpi_log("AXI4 SEQ_PHASE_API done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AXI4_SEQ_WR_EXPECT: begin
          axi4_write_expect_resp_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
          seq = axi4_write_expect_resp_seq#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("wr_exp");
          seq.addr = ADDR_W'(a0);
          seq.expected_bresp = axi4_resp_e'(a1);
          kvips_dpi_log($sformatf("AXI4 SEQ_WR_EXPECT addr=0x%0h exp=%0d", seq.addr, a1));
          seq.start(env.get_master_sequencer(0));
          kvips_dpi_log("AXI4 SEQ_WR_EXPECT done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AXI4_SEQ_RD_EXPECT: begin
          axi4_read_expect_resp_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
          seq = axi4_read_expect_resp_seq#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("rd_exp");
          seq.addr = ADDR_W'(a0);
          seq.expected_rresp = axi4_resp_e'(a1);
          kvips_dpi_log($sformatf("AXI4 SEQ_RD_EXPECT addr=0x%0h exp=%0d", seq.addr, a1));
          seq.start(env.get_master_sequencer(0));
          kvips_dpi_log("AXI4 SEQ_RD_EXPECT done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AXI4_SEQ_SAME_ID: begin
          // Non-pipe directed same-ID traffic (library needs pipelined master).
          int unsigned n;
          logic [ADDR_W-1:0] base;
          n = (int'(a0) == 0) ? 8 : int'(a0);
          base = ADDR_W'(a1 != 0 ? a1 : 64'h7000);
          kvips_dpi_log($sformatf("AXI4 SEQ_SAME_ID start num=%0d base=0x%0h", n, base));
          for (int unsigned t = 0; t < n; t++) begin
            axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) wr, rd;
            wr = axi4_item#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create($sformatf("sid_wr_%0d", t));
            wr.is_write = 1'b1; wr.id = '0; wr.addr = base + t * STRB_W;
            wr.len = 0; wr.size = $clog2(STRB_W); wr.burst = AXI4_BURST_INCR;
            wr.allocate_payload(); wr.data[0] = DATA_W'(64'h5A00_0000 + t); wr.strb[0] = '1;
            do_item(wr);
            rd = axi4_item#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create($sformatf("sid_rd_%0d", t));
            rd.is_write = 1'b0; rd.id = '0; rd.addr = wr.addr;
            rd.len = 0; rd.size = wr.size; rd.burst = AXI4_BURST_INCR;
            rd.allocate_payload();
            do_item(rd);
          end
          kvips_dpi_log("AXI4 SEQ_SAME_ID done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AXI4_SEQ_SIDEBAND: begin
          // Directed remapped sideband traffic (library hardcodes OOR 0x3D000).
          logic [ADDR_W-1:0] addr;
          axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) wr, rd;
          addr = ADDR_W'(a0 != 0 ? a0 : 64'h8000);
          kvips_dpi_log($sformatf("AXI4 SEQ_SIDEBAND start addr=0x%0h", addr));
          wr = axi4_item#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("sb_wr");
          wr.is_write = 1'b1; wr.id = 0; wr.addr = addr; wr.len = 0;
          wr.size = $clog2(STRB_W); wr.burst = AXI4_BURST_INCR;
          wr.cache = 4; wr.prot = 3; wr.qos = 1; wr.region = 1;
          wr.allocate_payload(); wr.data[0] = DATA_W'(64'hABCD); wr.strb[0] = '1;
          do_item(wr);
          rd = axi4_item#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("sb_rd");
          rd.is_write = 1'b0; rd.id = 0; rd.addr = addr; rd.len = 0;
          rd.size = wr.size; rd.burst = AXI4_BURST_INCR;
          rd.cache = wr.cache; rd.prot = wr.prot; rd.qos = wr.qos; rd.region = wr.region;
          rd.allocate_payload();
          do_item(rd);
          kvips_dpi_log("AXI4 SEQ_SIDEBAND done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AXI4_SEQ_ERR_WR: begin
          axi4_write_expect_resp_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
          seq = axi4_write_expect_resp_seq#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("err_wr");
          seq.addr = ADDR_W'(a0 != 0 ? a0 : 64'h0010_0000);
          seq.expected_bresp = AXI4_RESP_DECERR;
          kvips_dpi_log($sformatf("AXI4 SEQ_ERR_WR addr=0x%0h", seq.addr));
          seq.start(env.get_master_sequencer(0));
          kvips_dpi_log("AXI4 SEQ_ERR_WR done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AXI4_SEQ_ERR_RD: begin
          axi4_read_expect_resp_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
          seq = axi4_read_expect_resp_seq#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("err_rd");
          seq.addr = ADDR_W'(a0 != 0 ? a0 : 64'h0010_0000);
          seq.expected_rresp = AXI4_RESP_DECERR;
          kvips_dpi_log($sformatf("AXI4 SEQ_ERR_RD addr=0x%0h", seq.addr));
          seq.start(env.get_master_sequencer(0));
          kvips_dpi_log("AXI4 SEQ_ERR_RD done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AXI4_SEQ_PIPE_STRESS: begin
          // Same non-pipe stress body as SEQ_STRESS (pipe library needs get_response).
          axi4_write_readback_seq#(ADDR_W, DATA_W, ID_W, USER_W) seq;
          seq = axi4_write_readback_seq#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("pipe_stress");
          seq.num_txns = int'(a0);
          seq.base_addr = ADDR_W'(a1);
          seq.max_len = int'(a2);
          seq.enable_incr = 1'b1; seq.enable_fixed = 1'b0;
          seq.enable_wrap = 1'b0; seq.enable_narrow = 1'b0;
          kvips_dpi_log($sformatf("AXI4 SEQ_PIPE_STRESS start num=%0d", seq.num_txns));
          seq.start(env.get_master_sequencer(0));
          kvips_dpi_log("AXI4 SEQ_PIPE_STRESS done");
          respond(KVIPS_RSP_OK);
        end

        KVIPS_AXI4_SEQ_EXCL_BASIC,
        KVIPS_AXI4_SEQ_EXCL_FAIL,
        KVIPS_AXI4_SEQ_EXCL_XID,
        KVIPS_AXI4_SEQ_EXCL_ILL,
        KVIPS_AXI4_SEQ_RESET,
        KVIPS_AXI4_SEQ_NP_RESET,
        KVIPS_AXI4_SEQ_TIMEOUT: begin
          kvips_dpi_log($sformatf("AXI4 opcode 0x%0h unsupported on RAM DUT (needs VIP slave/reset/stall)", op));
          respond(KVIPS_RSP_INVAL);
        end

        default: begin
          `uvm_error("AXI4_COCOTB", $sformatf("Unknown opcode 0x%0h", op))
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
      kvips_dpi_log("AXI4 cocotb bridge ready");

      finish_req = 1'b0;
      while (!finish_req) begin
        @(posedge bif.clk);
        if (bif.req_valid) serve_cmd();
      end

      repeat (10) @(posedge bif.clk);
      bif.bridge_ready = 1'b0;
      kvips_dpi_log("AXI4 cocotb bridge finished");
      phase.drop_objection(this);
    endtask

    function void report_phase(uvm_phase phase);
      bit en;
      longint unsigned wr_txns, wr_err, rd_txns, rd_uninit, rd_mis;
      super.report_phase(phase);
      sb.get_summary(en, wr_txns, wr_err, rd_txns, rd_uninit, rd_mis);
      `uvm_info("AXI4_COCOTB",
        $sformatf("cmds=%0d mon_dpi=%0d sb_wr=%0d sb_rd=%0d sb_mis=%0d",
          cmd_count, mon_count, wr_txns, rd_txns, rd_mis), UVM_LOW)
      if (en && ((wr_txns + rd_txns) == 0) && cmd_count > 2)
        `uvm_error("AXI4_COCOTB", "Scoreboard saw zero transactions after traffic")
    endfunction
  endclass

endpackage
