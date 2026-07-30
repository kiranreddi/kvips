//------------------------------------------------------------------------------
// AXI4 independent channel-order checker
//------------------------------------------------------------------------------
// This checker observes the interface directly.  It deliberately does not use
// monitor reconstruction or the scoreboard, so orphaned and mis-framed B/R
// traffic is reported even when a monitor-side association would hide it.
//------------------------------------------------------------------------------

`ifndef KVIPS_AXI4_PROTOCOL_CHECKER_SVH
`define KVIPS_AXI4_PROTOCOL_CHECKER_SVH

class axi4_protocol_checker #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends uvm_component;

  localparam string RID = "AXI4_CHK";

`ifdef VERILATOR
  axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W) cfg;
  virtual axi4_if #(ADDR_W, DATA_W, ID_W, USER_W) vif;
`else
  typedef virtual axi4_if #(ADDR_W, DATA_W, ID_W, USER_W) axi4_vif_t;
  axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W) cfg;
  axi4_vif_t vif;
`endif

  typedef struct {
    logic [ID_W-1:0] id;
    int unsigned     beats;
  } aw_state_t;

  typedef struct {
    int unsigned beats_left;
  } rd_state_t;

  aw_state_t aw_q[$];
  int unsigned early_w_bursts[$];
  int unsigned w_beats;
  bit          w_active;
  int unsigned wr_done[logic [ID_W-1:0]][$];
  rd_state_t   rd_q[logic [ID_W-1:0]][$];

  longint unsigned aw_hs;
  longint unsigned w_hs;
  longint unsigned b_hs;
  longint unsigned ar_hs;
  longint unsigned r_hs;
  longint unsigned checker_errors;

  `uvm_component_param_utils(axi4_protocol_checker#(ADDR_W, DATA_W, ID_W, USER_W))

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W))::get(this, "", "cfg", cfg)) begin
      `uvm_fatal(RID, "Missing cfg in config DB (key: cfg)")
    end
    vif = cfg.vif;
`ifndef VERILATOR
    if (vif == null) `uvm_fatal(RID, "cfg.vif is null")
`endif
    clear_state();
  endfunction

  function void clear_state();
    aw_q.delete();
    early_w_bursts.delete();
    w_beats = 0;
    w_active = 1'b0;
    foreach (wr_done[id]) wr_done[id].delete();
    wr_done.delete();
    foreach (rd_q[id]) rd_q[id].delete();
    rd_q.delete();
  endfunction

  function void checker_error(string msg);
    checker_errors++;
    `uvm_error(RID, msg)
  endfunction

  function void complete_write_burst(int unsigned beats);
    aw_state_t aw;
    if (aw_q.size() != 0) begin
      aw = aw_q.pop_front();
      if (aw.beats != beats) begin
        checker_error($sformatf("W burst length mismatch for AWID=0x%0h expected=%0d observed=%0d",
                               aw.id, aw.beats, beats));
      end
      wr_done[aw.id].push_back(1);
    end else begin
      early_w_bursts.push_back(beats);
    end
  endfunction

  function void accept_aw();
    aw_state_t aw;
    aw.id = vif.awid;
    aw.beats = int'(vif.awlen) + 1;
    aw_hs++;
    // W is an independent channel.  If a complete W burst arrived before AW,
    // associate it now; otherwise retain the address in AXI AW order.
    if ((early_w_bursts.size() != 0) && !w_active && (aw_q.size() == 0)) begin
      if (early_w_bursts.pop_front() != aw.beats) begin
        checker_error($sformatf("Early W burst length mismatch for AWID=0x%0h", aw.id));
      end
      wr_done[aw.id].push_back(1);
    end else begin
      aw_q.push_back(aw);
    end
  endfunction

  function void accept_w();
    w_hs++;
    if (!w_active) begin
      w_active = 1'b1;
      w_beats = 0;
    end
    w_beats++;
    if (vif.wlast) begin
      complete_write_burst(w_beats);
      w_active = 1'b0;
      w_beats = 0;
    end
  endfunction

  function void accept_b();
    b_hs++;
    if (!wr_done.exists(vif.bid) || (wr_done[vif.bid].size() == 0)) begin
      checker_error($sformatf("B handshake has no completed write for BID=0x%0h", vif.bid));
    end else begin
      void'(wr_done[vif.bid].pop_front());
    end
  endfunction

  function void accept_ar();
    rd_state_t rd;
    rd.beats_left = int'(vif.arlen) + 1;
    rd_q[vif.arid].push_back(rd);
    ar_hs++;
  endfunction

  function void accept_r();
    rd_state_t rd;
    r_hs++;
    if (!rd_q.exists(vif.rid) || (rd_q[vif.rid].size() == 0)) begin
      checker_error($sformatf("R handshake has no outstanding read for RID=0x%0h", vif.rid));
      return;
    end
    rd = rd_q[vif.rid][0];
    if (rd.beats_left == 0) begin
      checker_error($sformatf("R beat overflow for RID=0x%0h", vif.rid));
    end else begin
      if (vif.rlast && (rd.beats_left != 1)) begin
        checker_error($sformatf("RLAST asserted early for RID=0x%0h beats_left=%0d", vif.rid, rd.beats_left));
      end
      if (!vif.rlast && (rd.beats_left == 1)) begin
        checker_error($sformatf("RLAST missing on final beat for RID=0x%0h", vif.rid));
      end
      rd.beats_left--;
      if (rd.beats_left == 0) begin
        void'(rd_q[vif.rid].pop_front());
      end else begin
        rd_q[vif.rid][0] = rd;
      end
    end
  endfunction

  task run_phase(uvm_phase phase);
    forever begin
      @(posedge vif.aclk);
      if (vif.areset_n !== 1'b1) begin
        clear_state();
        continue;
      end
      if (vif.awvalid && vif.awready) accept_aw();
      if (vif.wvalid  && vif.wready)  accept_w();
      if (vif.bvalid  && vif.bready)  accept_b();
      if (vif.arvalid && vif.arready) accept_ar();
      if (vif.rvalid  && vif.rready)  accept_r();
    end
  endtask

  function void report_phase(uvm_phase phase);
    `uvm_info(RID, $sformatf("Channel checker summary: AW=%0d W=%0d B=%0d AR=%0d R=%0d errors=%0d",
                             aw_hs, w_hs, b_hs, ar_hs, r_hs, checker_errors), UVM_LOW)
  endfunction

endclass

`endif // KVIPS_AXI4_PROTOCOL_CHECKER_SVH
