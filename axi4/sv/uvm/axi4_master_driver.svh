//------------------------------------------------------------------------------
// AXI4 Master Driver
//------------------------------------------------------------------------------

`ifndef KVIPS_AXI4_MASTER_DRIVER_SVH
`define KVIPS_AXI4_MASTER_DRIVER_SVH

class axi4_req_ctx #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends uvm_object;
  typedef axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) item_t;

  item_t            tr;
  uvm_sequence_item id_info;
  int unsigned      beats;
  int unsigned      beat_idx;
  bit               reset_reported;
  longint unsigned  issue_seq;

  `uvm_object_param_utils(axi4_req_ctx#(ADDR_W, DATA_W, ID_W, USER_W))

  function new(string name = "axi4_req_ctx");
    super.new(name);
    reset_reported = 1'b0;
    issue_seq = 0;
  endfunction
endclass

class axi4_master_driver #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends uvm_driver #(axi4_item#(ADDR_W, DATA_W, ID_W, USER_W));

  localparam int STRB_W = DATA_W/8;
  localparam string RID = "AXI4_MDRV";

`ifdef VERILATOR
  axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W) cfg;
  virtual axi4_if #(ADDR_W, DATA_W, ID_W, USER_W) vif;
`else
  typedef virtual axi4_if #(ADDR_W, DATA_W, ID_W, USER_W) axi4_vif_t;
  axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W) cfg;
  axi4_vif_t vif;
`endif

  int unsigned outstanding_w;
  int unsigned outstanding_r;
  bit          wr_launch_active;
  bit          rd_launch_active;
  semaphore    issue_order_sem;
  longint unsigned next_issue_seq;
  bit          accept_grant_active;
  axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) accept_req;

`ifdef VERILATOR
`define AXI4_M_EVT posedge vif.aclk
`else
`define AXI4_M_EVT vif.m_cb
`endif

  `uvm_component_param_utils(axi4_master_driver#(ADDR_W, DATA_W, ID_W, USER_W))

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
    issue_order_sem = new(1);
    next_issue_seq = 0;
    accept_grant_active = 1'b0;
    accept_req = null;
    wr_launch_active = 1'b0;
    rd_launch_active = 1'b0;
  endfunction

  task automatic drive_idle();
    vif.awvalid <= 1'b0;
    vif.wvalid  <= 1'b0;
    vif.bready  <= 1'b0;
    vif.arvalid <= 1'b0;
    vif.rready  <= 1'b0;
  endtask

  task automatic wait_reset_release();
    drive_idle();
    while (vif.areset_n !== 1'b1) @(posedge vif.aclk);
    @(posedge vif.aclk);
  endtask

  function automatic int unsigned rand_in_range(int unsigned lo, int unsigned hi);
    int unsigned v;
    if (hi <= lo) return lo;
`ifdef VERILATOR
    v = $urandom_range(hi, lo);
`else
    void'(std::randomize(v) with { v inside {[lo:hi]}; });
`endif
    return v;
  endfunction

  task automatic maybe_wait_cycles(int unsigned min_c, int unsigned max_c);
    int unsigned c;
    c = rand_in_range(min_c, max_c);
    repeat (c) @(posedge vif.aclk);
  endtask

  task run_phase(uvm_phase phase);
    wait_reset_release();

    if (!cfg.master_pipelined) begin
      axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) tr;
      forever begin
        seq_item_port.get_next_item(tr);
        tr.reset_aborted = 1'b0;
        if (vif.areset_n !== 1'b1) wait_reset_release();
        if (cfg.trace_enable) `uvm_info(RID, {"DRV got item:\n", tr.sprint()}, UVM_MEDIUM)
        if (tr.is_write) drive_write(tr);
        else            drive_read(tr);
        seq_item_port.item_done();

        if (cfg.inter_txn_gap_max != 0) begin
          int unsigned gap;
          gap = rand_in_range(cfg.inter_txn_gap_min, cfg.inter_txn_gap_max);
          repeat (gap) @(`AXI4_M_EVT);
        end
      end
    end else begin
      fork
        pipelined_accept_loop();
        pipelined_aw_loop();
        pipelined_w_loop();
        pipelined_b_loop();
        pipelined_ar_loop();
        pipelined_r_loop();
        pipelined_reset_loop();
      join
    end
  endtask

  // -------------------------
  // Pipelined (multi-outstanding) engine
  // -------------------------

  typedef axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) item_t;
  typedef axi4_req_ctx#(ADDR_W, DATA_W, ID_W, USER_W) axi4_req_ctx_t;

  axi4_req_ctx_t wr_issue_q[$];
  axi4_req_ctx_t wr_w_q[$];
  axi4_req_ctx_t wr_wait_b[logic [ID_W-1:0]][$];
  axi4_req_ctx_t wr_active_aw;
  axi4_req_ctx_t wr_active_w;

  axi4_req_ctx_t rd_issue_q[$];
  axi4_req_ctx_t rd_wait_r[logic [ID_W-1:0]][$];
  axi4_req_ctx_t rd_active_ar;

  task automatic put_reset_response(axi4_req_ctx_t ctx, bit is_write);
    item_t rsp;
    if ((ctx == null) || ctx.reset_reported) return;
    ctx.reset_reported = 1'b1;
    rsp = new(is_write ? "reset_wr_rsp" : "reset_rd_rsp");
    rsp.copy(ctx.tr);
    rsp.reset_aborted = 1'b1;
    if (is_write) begin
      rsp.bresp = AXI4_RESP_OKAY;
    end else begin
      rsp.allocate_payload();
      foreach (rsp.rresp[i]) rsp.rresp[i] = AXI4_RESP_OKAY;
    end
    if (ctx.id_info != null) rsp.set_id_info(ctx.id_info);
    seq_item_port.put_response(rsp);
  endtask

  task automatic put_reset_item_response(item_t tr);
    item_t rsp;
    if (tr == null) return;
    rsp = new("reset_accept_rsp");
    rsp.copy(tr);
    rsp.set_id_info(tr);
    rsp.reset_aborted = 1'b1;
    if (rsp.is_write) begin
      rsp.bresp = AXI4_RESP_OKAY;
    end else begin
      rsp.allocate_payload();
      foreach (rsp.rresp[i]) rsp.rresp[i] = AXI4_RESP_OKAY;
    end
    seq_item_port.put_response(rsp);
  endtask

  task automatic reset_flush_pipelined();
    if (accept_grant_active) begin
      // A reset can interrupt the tiny window between try_next_item() and
      // item_done().  Complete that grant before starting a new epoch.
      seq_item_port.item_done();
      put_reset_item_response(accept_req);
      accept_req = null;
      accept_grant_active = 1'b0;
    end
    foreach (wr_issue_q[i]) put_reset_response(wr_issue_q[i], 1'b1);
    foreach (wr_w_q[i])     put_reset_response(wr_w_q[i], 1'b1);
    foreach (wr_wait_b[id]) begin
      for (int unsigned i = 0; i < wr_wait_b[id].size(); i++)
        put_reset_response(wr_wait_b[id][i], 1'b1);
    end
    foreach (rd_issue_q[i]) put_reset_response(rd_issue_q[i], 1'b0);
    foreach (rd_wait_r[id]) begin
      for (int unsigned i = 0; i < rd_wait_r[id].size(); i++)
        put_reset_response(rd_wait_r[id][i], 1'b0);
    end
    put_reset_response(wr_active_aw, 1'b1);
    put_reset_response(wr_active_w, 1'b1);
    put_reset_response(rd_active_ar, 1'b0);

    wr_issue_q.delete();
    wr_w_q.delete();
    foreach (wr_wait_b[id]) wr_wait_b[id].delete();
    wr_wait_b.delete();
    rd_issue_q.delete();
    foreach (rd_wait_r[id]) rd_wait_r[id].delete();
    rd_wait_r.delete();
    wr_active_aw = null;
    wr_active_w  = null;
    rd_active_ar = null;
    outstanding_w = 0;
    outstanding_r = 0;
    wr_launch_active = 1'b0;
    rd_launch_active = 1'b0;
    issue_order_sem = new(1);
    drive_idle();
  endtask

  task automatic pipelined_reset_loop();
    forever begin
      @(negedge vif.areset_n);
      if (!cfg.master_reset_flush) begin
        `uvm_fatal(RID, "AXI4 reset observed while master_reset_flush is disabled")
      end
      reset_flush_pipelined();
    end
  endtask

  function automatic axi4_rw_order_mode_e effective_rw_order_mode();
    if (cfg.rw_order_mode != AXI4_RW_ORDER_ALLOW) return cfg.rw_order_mode;
    return cfg.order_overlapping_rw ? AXI4_RW_ORDER_ALLOW : AXI4_RW_ORDER_SERIALIZE;
  endfunction

  function automatic bit ctx_ranges_overlap(axi4_req_ctx_t a, axi4_req_ctx_t b);
    longint unsigned a_start;
    longint unsigned b_start;
    longint unsigned a_bytes;
    longint unsigned b_bytes;
    longint unsigned a_end;
    longint unsigned b_end;
    if ((a == null) || (b == null)) return 1'b0;
    a_start = longint'(a.tr.addr);
    b_start = longint'(b.tr.addr);
    a_bytes = axi4_total_bytes(int'(a.tr.size), int'(a.tr.len));
    b_bytes = axi4_total_bytes(int'(b.tr.size), int'(b.tr.len));
    a_end = (a_bytes == 0) ? a_start : a_start + a_bytes - 1;
    b_end = (b_bytes == 0) ? b_start : b_start + b_bytes - 1;
    return (a_start <= b_end) && (b_start <= a_end);
  endfunction

  function automatic bit rw_range_conflict(axi4_req_ctx_t candidate, bit candidate_write);
    if (effective_rw_order_mode() != AXI4_RW_ORDER_RANGE_AWARE) return 1'b0;
    if (candidate_write) begin
      foreach (rd_issue_q[i]) if ((rd_issue_q[i].issue_seq < candidate.issue_seq) &&
                                  ctx_ranges_overlap(candidate, rd_issue_q[i])) return 1'b1;
      foreach (rd_wait_r[id]) begin
        for (int unsigned i = 0; i < rd_wait_r[id].size(); i++)
          if ((rd_wait_r[id][i].issue_seq < candidate.issue_seq) &&
              ctx_ranges_overlap(candidate, rd_wait_r[id][i])) return 1'b1;
      end
      if ((rd_active_ar != null) && (rd_active_ar.issue_seq < candidate.issue_seq) &&
          ctx_ranges_overlap(candidate, rd_active_ar)) return 1'b1;
    end else begin
      foreach (wr_issue_q[i]) if ((wr_issue_q[i].issue_seq < candidate.issue_seq) &&
                                  ctx_ranges_overlap(candidate, wr_issue_q[i])) return 1'b1;
      foreach (wr_w_q[i]) if ((wr_w_q[i].issue_seq < candidate.issue_seq) &&
                              ctx_ranges_overlap(candidate, wr_w_q[i])) return 1'b1;
      foreach (wr_wait_b[id]) begin
        for (int unsigned i = 0; i < wr_wait_b[id].size(); i++)
          if ((wr_wait_b[id][i].issue_seq < candidate.issue_seq) &&
              ctx_ranges_overlap(candidate, wr_wait_b[id][i])) return 1'b1;
      end
      if ((wr_active_aw != null) && (wr_active_aw.issue_seq < candidate.issue_seq) &&
          ctx_ranges_overlap(candidate, wr_active_aw)) return 1'b1;
      if ((wr_active_w != null) && (wr_active_w.issue_seq < candidate.issue_seq) &&
          ctx_ranges_overlap(candidate, wr_active_w)) return 1'b1;
    end
    return 1'b0;
  endfunction

  task automatic pipelined_accept_loop();
    item_t req;
    wait_reset_release();
    forever begin
      if (vif.areset_n !== 1'b1) begin
        wait_reset_release();
        continue;
      end
      // Do not hold a sequencer grant across a reset epoch.  A blocking
      // get_next_item() can be killed by reset before item_done(), leaving the
      // sequencer in a permanently granted state when the epoch restarts.
      req = null;
      seq_item_port.try_next_item(req);
      if (req == null) begin
        @(posedge vif.aclk);
        continue;
      end
      accept_grant_active = 1'b1;
      accept_req = req;

      // Soft backpressure on the sequencer to avoid unbounded queueing.
      while ((wr_issue_q.size() + rd_issue_q.size()) > (4 * (cfg.max_outstanding_reads + cfg.max_outstanding_writes))) begin
        if (vif.areset_n !== 1'b1) begin
          while (accept_grant_active && (vif.areset_n !== 1'b1)) @(posedge vif.aclk);
          if (!accept_grant_active) begin
            accept_req = null;
            break;
          end
        end
        @(posedge vif.aclk);
      end

      if ((vif.areset_n !== 1'b1) || !accept_grant_active) begin
        if (accept_grant_active) begin
          seq_item_port.item_done();
          put_reset_item_response(accept_req);
          accept_grant_active = 1'b0;
        end
        accept_req = null;
        continue;
      end

      begin
        axi4_req_ctx_t ctx;
        ctx = new("ctx");
        ctx.tr = new("req_tr");
        ctx.tr.copy(req);
        ctx.tr.allocate_payload();
        ctx.beats    = ctx.tr.num_beats();
        ctx.beat_idx = 0;
        ctx.issue_seq = next_issue_seq++;

        // Create a minimal id_info carrier for responses.
        ctx.id_info = new("id_info");
        ctx.id_info.set_sequence_id(req.get_sequence_id());
        ctx.id_info.set_transaction_id(req.get_transaction_id());

        if (cfg.trace_enable) `uvm_info(RID, {"PIPE accept:\n", ctx.tr.sprint()}, UVM_MEDIUM)
        if (ctx.tr.is_write) wr_issue_q.push_back(ctx);
        else                 rd_issue_q.push_back(ctx);
      end

      // Release the sequence immediately; completion is indicated via put_response().
      seq_item_port.item_done();
      accept_grant_active = 1'b0;
      accept_req = null;
    end
  endtask

  task automatic pipelined_aw_loop();
    axi4_req_ctx_t ctx;
    bit hs_ok;
    wait_reset_release();
    forever begin
      if (vif.areset_n !== 1'b1) begin
        wait_reset_release();
        continue;
      end
      if (wr_issue_q.size() == 0) begin
        @(posedge vif.aclk);
        continue;
      end
      if ((outstanding_w >= cfg.max_outstanding_writes) ||
          ((cfg.max_outstanding_total != 0) &&
           ((outstanding_w + outstanding_r) >= cfg.max_outstanding_total))) begin
        @(posedge vif.aclk);
        continue;
      end
      ctx = wr_issue_q[0];
      if (effective_rw_order_mode() == AXI4_RW_ORDER_SERIALIZE) begin
        forever begin
          issue_order_sem.get(1);
          if (!rd_launch_active && (outstanding_r == 0)) begin
            wr_launch_active = 1'b1;
            issue_order_sem.put(1);
            break;
          end
          issue_order_sem.put(1);
          @(posedge vif.aclk);
        end
      end else if (effective_rw_order_mode() == AXI4_RW_ORDER_RANGE_AWARE) begin
        while (rw_range_conflict(ctx, 1'b1)) begin
          if (vif.areset_n !== 1'b1) break;
          @(posedge vif.aclk);
        end
      end
      if (vif.areset_n !== 1'b1) continue;
      ctx = wr_issue_q.pop_front();
      wr_active_aw = ctx;

      if (ctx.tr.aw_delay_cycles >= 0) begin
        repeat (ctx.tr.aw_delay_cycles) @(posedge vif.aclk);
      end else begin
        maybe_wait_cycles(cfg.master_aw_delay_min, cfg.master_aw_delay_max);
      end
      if (vif.areset_n !== 1'b1) begin
        wr_active_aw = null;
        continue;
      end

      // AW
      @(negedge vif.aclk);
      vif.awid     <= ctx.tr.id;
      vif.awaddr   <= ctx.tr.addr;
      vif.awlen    <= ctx.tr.len;
      vif.awsize   <= ctx.tr.size;
      vif.awburst  <= ctx.tr.burst;
      vif.awlock   <= ctx.tr.lock;
      vif.awcache  <= ctx.tr.cache;
      vif.awprot   <= ctx.tr.prot;
      vif.awqos    <= ctx.tr.qos;
      vif.awregion <= ctx.tr.region;
      vif.awuser   <= ctx.tr.user;
      vif.awvalid  <= 1'b1;
      wait_aw_handshake(hs_ok);
      if (!hs_ok) begin
        vif.awvalid <= 1'b0;
        wr_active_aw = null;
        continue;
      end
      @(negedge vif.aclk);
      vif.awvalid <= 1'b0;

      if ((vif.areset_n !== 1'b1) || (wr_active_aw == null)) begin
        wr_active_aw = null;
        continue;
      end

      outstanding_w++;
      if (effective_rw_order_mode() == AXI4_RW_ORDER_SERIALIZE) begin
        issue_order_sem.get(1);
        wr_launch_active = 1'b0;
        issue_order_sem.put(1);
      end
      wr_active_aw = null;
      wr_w_q.push_back(ctx);
    end
  endtask

  task automatic pipelined_w_loop();
    axi4_req_ctx_t ctx;
    bit hs_ok;
    wait_reset_release();
    forever begin
      if (vif.areset_n !== 1'b1) begin
        wait_reset_release();
        continue;
      end
      if (wr_w_q.size() == 0) begin
        @(posedge vif.aclk);
        continue;
      end
      ctx = wr_w_q.pop_front();
      wr_active_w = ctx;
      for (int unsigned i = 0; i < ctx.beats; i++) begin
        if (vif.areset_n !== 1'b1) begin
          hs_ok = 1'b0;
          break;
        end
        if (i != 0) begin
          if (ctx.tr.w_beat_gap_cycles >= 0) begin
            repeat (ctx.tr.w_beat_gap_cycles) @(posedge vif.aclk);
          end else begin
            maybe_wait_cycles(cfg.master_w_beat_gap_min, cfg.master_w_beat_gap_max);
          end
        end
        if (vif.areset_n !== 1'b1) begin
          hs_ok = 1'b0;
          break;
        end
        @(negedge vif.aclk);
        vif.wdata  <= ctx.tr.data[i];
        vif.wstrb  <= (ctx.tr.strb.size() == ctx.beats) ? ctx.tr.strb[i] : '1;
        vif.wlast  <= (i == (ctx.beats-1));
        vif.wuser  <= ctx.tr.user;
        vif.wvalid <= 1'b1;
        wait_w_handshake(hs_ok);
        if (!hs_ok) begin
          vif.wvalid <= 1'b0;
          break;
        end
        @(negedge vif.aclk);
        vif.wvalid <= 1'b0;
      end
      if (!hs_ok || (vif.areset_n !== 1'b1)) begin
        wr_active_w = null;
        continue;
      end
      wr_active_w = null;
      wr_wait_b[ctx.tr.id].push_back(ctx);
    end
  endtask

  task automatic pipelined_b_loop();
    axi4_req_ctx_t ctx;
    int unsigned bready_low_left;
    wait_reset_release();
    bready_low_left = 0;
    forever begin
      if (vif.areset_n !== 1'b1) begin
        wait_reset_release();
        continue;
      end
      // Drive BREADY whenever we have outstanding writes, with optional
      // controlled backpressure for B-channel stress.
      @(negedge vif.aclk);
      if (outstanding_w == 0) begin
        vif.bready <= 1'b0;
      end else if (cfg.master_bready_random) begin
        if (bready_low_left != 0) begin
          vif.bready <= 1'b0;
          bready_low_left--;
        end else if (($urandom_range(0, 9) == 0) && (cfg.master_bready_low_max != 0)) begin
          bready_low_left = rand_in_range(cfg.master_bready_low_min, cfg.master_bready_low_max);
          vif.bready <= (bready_low_left == 0);
        end else begin
          vif.bready <= 1'b1;
        end
      end else begin
        vif.bready <= 1'b1;
      end

      @(posedge vif.aclk);
      if (!(vif.bvalid && vif.bready)) begin
        continue;
      end

      if (wr_wait_b.exists(vif.bid) && (wr_wait_b[vif.bid].size() != 0)) begin
        ctx = wr_wait_b[vif.bid].pop_front();
        ctx.tr.bresp = axi4_resp_e'(vif.bresp);

        begin
          item_t rsp;
          rsp = new("wr_rsp");
          rsp.copy(ctx.tr);
          if (ctx.id_info != null) rsp.set_id_info(ctx.id_info);
          seq_item_port.put_response(rsp);
        end
      end else begin
        `uvm_warning(RID, $sformatf("B seen with BID=0x%0h but no matching outstanding write ctx", vif.bid))
      end

      if (outstanding_w != 0) outstanding_w--;
    end
  endtask

  task automatic pipelined_ar_loop();
    axi4_req_ctx_t ctx;
    bit hs_ok;
    wait_reset_release();
    forever begin
      if (vif.areset_n !== 1'b1) begin
        wait_reset_release();
        continue;
      end
      if (rd_issue_q.size() == 0) begin
        @(posedge vif.aclk);
        continue;
      end
      if ((outstanding_r >= cfg.max_outstanding_reads) ||
          ((cfg.max_outstanding_total != 0) &&
           ((outstanding_w + outstanding_r) >= cfg.max_outstanding_total))) begin
        @(posedge vif.aclk);
        continue;
      end
      ctx = rd_issue_q[0];
      if (effective_rw_order_mode() == AXI4_RW_ORDER_SERIALIZE) begin
        forever begin
          issue_order_sem.get(1);
          if (!wr_launch_active && (outstanding_w == 0)) begin
            rd_launch_active = 1'b1;
            issue_order_sem.put(1);
            break;
          end
          issue_order_sem.put(1);
          @(posedge vif.aclk);
        end
      end else if (effective_rw_order_mode() == AXI4_RW_ORDER_RANGE_AWARE) begin
        while (rw_range_conflict(ctx, 1'b0)) begin
          if (vif.areset_n !== 1'b1) break;
          @(posedge vif.aclk);
        end
      end
      if (vif.areset_n !== 1'b1) continue;
      ctx = rd_issue_q.pop_front();
      rd_active_ar = ctx;

      if (ctx.tr.ar_delay_cycles >= 0) begin
        repeat (ctx.tr.ar_delay_cycles) @(posedge vif.aclk);
      end else begin
        maybe_wait_cycles(cfg.master_ar_delay_min, cfg.master_ar_delay_max);
      end
      if (vif.areset_n !== 1'b1) begin
        rd_active_ar = null;
        continue;
      end

      // AR
      @(negedge vif.aclk);
      vif.arid     <= ctx.tr.id;
      vif.araddr   <= ctx.tr.addr;
      vif.arlen    <= ctx.tr.len;
      vif.arsize   <= ctx.tr.size;
      vif.arburst  <= ctx.tr.burst;
      vif.arlock   <= ctx.tr.lock;
      vif.arcache  <= ctx.tr.cache;
      vif.arprot   <= ctx.tr.prot;
      vif.arqos    <= ctx.tr.qos;
      vif.arregion <= ctx.tr.region;
      vif.aruser   <= ctx.tr.user;
      vif.arvalid  <= 1'b1;
      wait_ar_handshake(hs_ok);
      if (!hs_ok) begin
        vif.arvalid <= 1'b0;
        rd_active_ar = null;
        continue;
      end
      @(negedge vif.aclk);
      vif.arvalid <= 1'b0;

      if ((vif.areset_n !== 1'b1) || (rd_active_ar == null)) begin
        rd_active_ar = null;
        continue;
      end

      outstanding_r++;
      if (effective_rw_order_mode() == AXI4_RW_ORDER_SERIALIZE) begin
        issue_order_sem.get(1);
        rd_launch_active = 1'b0;
        issue_order_sem.put(1);
      end
      rd_active_ar = null;
      rd_wait_r[ctx.tr.id].push_back(ctx);
    end
  endtask

  task automatic pipelined_r_loop();
    int unsigned rready_low_left;
    wait_reset_release();
    rready_low_left = 0;
    forever begin
      if (vif.areset_n !== 1'b1) begin
        wait_reset_release();
        continue;
      end
      // Drive RREADY whenever we have outstanding reads.
      @(negedge vif.aclk);
      if (outstanding_r == 0) begin
        vif.rready <= 1'b0;
      end else if (cfg.master_rready_random) begin
        if (rready_low_left != 0) begin
          vif.rready <= 1'b0;
          rready_low_left--;
        end else begin
          // Start a low stretch occasionally.
          if (($urandom_range(0, 9) == 0) && (cfg.master_rready_low_max != 0)) begin
            rready_low_left = rand_in_range(cfg.master_rready_low_min, cfg.master_rready_low_max);
            vif.rready <= (rready_low_left == 0);
          end else begin
            vif.rready <= 1'b1;
          end
        end
      end else begin
        vif.rready <= 1'b1;
      end

      @(posedge vif.aclk);
      if (!(vif.rvalid && vif.rready)) begin
        continue;
      end

      if (rd_wait_r.exists(vif.rid) && (rd_wait_r[vif.rid].size() != 0)) begin
        axi4_req_ctx_t ctx;
        ctx = rd_wait_r[vif.rid][0];

        if (ctx.beat_idx < ctx.beats) begin
          ctx.tr.data[ctx.beat_idx]  = vif.rdata;
          ctx.tr.rresp[ctx.beat_idx] = axi4_resp_e'(vif.rresp);
        end else begin
          `uvm_error(RID, $sformatf("R beat overflow rid=0x%0h beat_idx=%0d beats=%0d", vif.rid, ctx.beat_idx, ctx.beats))
        end
        ctx.beat_idx++;
        rd_wait_r[vif.rid][0] = ctx;

        if (vif.rlast) begin
          ctx = rd_wait_r[vif.rid].pop_front();
          begin
            item_t rsp;
            rsp = new("rd_rsp");
            rsp.copy(ctx.tr);
            if (ctx.id_info != null) rsp.set_id_info(ctx.id_info);
            seq_item_port.put_response(rsp);
          end
          if (outstanding_r != 0) outstanding_r--;
        end
      end else begin
        `uvm_warning(RID, $sformatf("R seen with RID=0x%0h but no matching outstanding read ctx", vif.rid))
      end

    end
  endtask

  task automatic wait_aw_handshake(output bit success);
    int unsigned cycles = 0;
    success = 1'b0;
    while (vif.areset_n === 1'b1) begin
      @(posedge vif.aclk);
      if (vif.awready) break;
      cycles++;
      if ((cfg.handshake_timeout_cycles != 0) && (cycles > cfg.handshake_timeout_cycles)) begin
        `uvm_fatal(RID, "Handshake timeout on AW")
      end
    end
    success = (vif.areset_n === 1'b1);
  endtask

  task automatic wait_w_handshake(output bit success);
    int unsigned cycles = 0;
    success = 1'b0;
    while (vif.areset_n === 1'b1) begin
      @(posedge vif.aclk);
      if (vif.wready) break;
      cycles++;
      if ((cfg.handshake_timeout_cycles != 0) && (cycles > cfg.handshake_timeout_cycles)) begin
        `uvm_fatal(RID, "Handshake timeout on W")
      end
    end
    success = (vif.areset_n === 1'b1);
  endtask

  task automatic wait_ar_handshake(output bit success);
    int unsigned cycles = 0;
    success = 1'b0;
    while (vif.areset_n === 1'b1) begin
      @(posedge vif.aclk);
      if (vif.arready) break;
      cycles++;
      if ((cfg.handshake_timeout_cycles != 0) && (cycles > cfg.handshake_timeout_cycles)) begin
        `uvm_fatal(RID, "Handshake timeout on AR")
      end
    end
    success = (vif.areset_n === 1'b1);
  endtask

  task automatic drive_write(axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) tr);
    int unsigned beats;
    int unsigned cycles;
    bit hs_ok;
    tr.reset_aborted = 1'b0;
    tr.allocate_payload();
    beats = tr.num_beats();

    if (tr.aw_delay_cycles >= 0) begin
      repeat (tr.aw_delay_cycles) @(posedge vif.aclk);
    end else begin
      maybe_wait_cycles(cfg.master_aw_delay_min, cfg.master_aw_delay_max);
    end

    // AW
    @(negedge vif.aclk);
    vif.awid     <= tr.id;
    vif.awaddr   <= tr.addr;
    vif.awlen    <= tr.len;
    vif.awsize   <= tr.size;
    vif.awburst  <= tr.burst;
    vif.awlock   <= tr.lock;
    vif.awcache  <= tr.cache;
    vif.awprot   <= tr.prot;
    vif.awqos    <= tr.qos;
    vif.awregion <= tr.region;
    vif.awuser   <= tr.user;
    vif.awvalid  <= 1'b1;
    wait_aw_handshake(hs_ok);
    @(negedge vif.aclk);
    vif.awvalid <= 1'b0;
    if (!hs_ok) begin
      tr.reset_aborted = 1'b1;
      drive_idle();
      return;
    end

    // W
    for (int unsigned i = 0; i < beats; i++) begin
      if (i != 0) begin
        if (tr.w_beat_gap_cycles >= 0) begin
          repeat (tr.w_beat_gap_cycles) @(posedge vif.aclk);
        end else begin
          maybe_wait_cycles(cfg.master_w_beat_gap_min, cfg.master_w_beat_gap_max);
        end
      end
      @(negedge vif.aclk);
      vif.wdata  <= tr.data[i];
      vif.wstrb  <= (tr.strb.size() == beats) ? tr.strb[i] : '1;
      vif.wlast  <= (i == (beats-1));
      vif.wuser  <= tr.user;
      vif.wvalid <= 1'b1;
      wait_w_handshake(hs_ok);
      @(negedge vif.aclk);
      vif.wvalid <= 1'b0;
      if (!hs_ok) begin
        tr.reset_aborted = 1'b1;
        drive_idle();
        return;
      end
    end

    // B
    @(negedge vif.aclk);
    vif.bready <= 1'b1;
    cycles = 0;
    while (1) begin
      @(posedge vif.aclk);
      if (vif.areset_n !== 1'b1) begin
        tr.reset_aborted = 1'b1;
        drive_idle();
        return;
      end
      if (vif.bvalid) break;
      cycles++;
      if ((cfg.handshake_timeout_cycles != 0) && (cycles > cfg.handshake_timeout_cycles)) begin
        `uvm_fatal(RID, "Timeout waiting for BVALID")
      end
    end
    tr.bresp = axi4_resp_e'(vif.bresp);
    @(negedge vif.aclk);
    vif.bready <= 1'b0;
  endtask

  task automatic drive_read(axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) tr);
    int unsigned beats;
    int unsigned cycles;
    bit hs_ok;
    tr.reset_aborted = 1'b0;
    tr.allocate_payload();
    beats = tr.num_beats();

    if (tr.ar_delay_cycles >= 0) begin
      repeat (tr.ar_delay_cycles) @(posedge vif.aclk);
    end else begin
      maybe_wait_cycles(cfg.master_ar_delay_min, cfg.master_ar_delay_max);
    end

    // AR
    @(negedge vif.aclk);
    vif.arid     <= tr.id;
    vif.araddr   <= tr.addr;
    vif.arlen    <= tr.len;
    vif.arsize   <= tr.size;
    vif.arburst  <= tr.burst;
    vif.arlock   <= tr.lock;
    vif.arcache  <= tr.cache;
    vif.arprot   <= tr.prot;
    vif.arqos    <= tr.qos;
    vif.arregion <= tr.region;
    vif.aruser   <= tr.user;
    vif.arvalid  <= 1'b1;
    wait_ar_handshake(hs_ok);
    @(negedge vif.aclk);
    vif.arvalid <= 1'b0;
    if (!hs_ok) begin
      tr.reset_aborted = 1'b1;
      drive_idle();
      return;
    end

    // R
    if (cfg.master_rready_random) begin
      `uvm_warning(RID, "master_rready_random is supported in pipelined mode; non-pipelined drive_read keeps RREADY asserted")
    end

    @(negedge vif.aclk);
    vif.rready <= 1'b1;
    for (int unsigned i = 0; i < beats; i++) begin
      cycles = 0;
      while (1) begin
        @(posedge vif.aclk);
        if (vif.areset_n !== 1'b1) begin
          tr.reset_aborted = 1'b1;
          drive_idle();
          return;
        end
        if (vif.rvalid) break;
        cycles++;
        if ((cfg.handshake_timeout_cycles != 0) && (cycles > cfg.handshake_timeout_cycles)) begin
          `uvm_fatal(RID, "Timeout waiting for RVALID")
        end
      end
      tr.data[i]  = vif.rdata;
      tr.rresp[i] = axi4_resp_e'(vif.rresp);
      if ((i == beats-1) && !vif.rlast) `uvm_error(RID, "Expected RLAST on final beat")
      if ((i != beats-1) && vif.rlast)  `uvm_error(RID, "Unexpected RLAST before final beat")
      @(posedge vif.aclk);
    end
    @(negedge vif.aclk);
    vif.rready <= 1'b0;
  endtask

endclass

`undef AXI4_M_EVT

`endif // KVIPS_AXI4_MASTER_DRIVER_SVH
