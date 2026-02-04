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

  `uvm_object_param_utils(axi4_req_ctx#(ADDR_W, DATA_W, ID_W, USER_W))

  function new(string name = "axi4_req_ctx");
    super.new(name);
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
  typedef axi4_if #(ADDR_W, DATA_W, ID_W, USER_W) axi4_vif_t;
`else
  typedef virtual axi4_if #(ADDR_W, DATA_W, ID_W, USER_W) axi4_vif_t;
`endif

  axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W) cfg;
`ifdef VERILATOR
  virtual axi4_vif_t vif;
`else
  axi4_vif_t vif;
`endif

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
    if (vif == null) `uvm_fatal(RID, "cfg.vif is null")
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

  axi4_req_ctx_t rd_issue_q[$];
  axi4_req_ctx_t rd_wait_r[logic [ID_W-1:0]][$];

  int unsigned outstanding_w;
  int unsigned outstanding_r;

  task automatic pipelined_accept_loop();
    item_t req;
    wait_reset_release();
    forever begin
      seq_item_port.get_next_item(req);
      if (req == null) begin
        seq_item_port.item_done();
        continue;
      end

      // Soft backpressure on the sequencer to avoid unbounded queueing.
      while ((wr_issue_q.size() + rd_issue_q.size()) > (4 * (cfg.max_outstanding_reads + cfg.max_outstanding_writes))) begin
        @(posedge vif.aclk);
      end

      begin
        axi4_req_ctx_t ctx;
        ctx = new("ctx");
        ctx.tr = new("req_tr");
        ctx.tr.copy(req);
        ctx.tr.allocate_payload();
        ctx.beats    = ctx.tr.num_beats();
        ctx.beat_idx = 0;

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
    end
  endtask

  task automatic pipelined_aw_loop();
    axi4_req_ctx_t ctx;
    wait_reset_release();
    forever begin
      if (wr_issue_q.size() == 0) begin
        @(posedge vif.aclk);
        continue;
      end
      if (outstanding_w >= cfg.max_outstanding_writes) begin
        @(posedge vif.aclk);
        continue;
      end
      ctx = wr_issue_q.pop_front();

      if (ctx.tr.aw_delay_cycles >= 0) begin
        repeat (ctx.tr.aw_delay_cycles) @(posedge vif.aclk);
      end else begin
        maybe_wait_cycles(cfg.master_aw_delay_min, cfg.master_aw_delay_max);
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
      wait_aw_handshake();
      @(negedge vif.aclk);
      vif.awvalid <= 1'b0;

      outstanding_w++;
      wr_w_q.push_back(ctx);
    end
  endtask

  task automatic pipelined_w_loop();
    axi4_req_ctx_t ctx;
    wait_reset_release();
    forever begin
      if (wr_w_q.size() == 0) begin
        @(posedge vif.aclk);
        continue;
      end
      ctx = wr_w_q.pop_front();
      for (int unsigned i = 0; i < ctx.beats; i++) begin
        if (i != 0) begin
          if (ctx.tr.w_beat_gap_cycles >= 0) begin
            repeat (ctx.tr.w_beat_gap_cycles) @(posedge vif.aclk);
          end else begin
            maybe_wait_cycles(cfg.master_w_beat_gap_min, cfg.master_w_beat_gap_max);
          end
        end
        @(negedge vif.aclk);
        vif.wdata  <= ctx.tr.data[i];
        vif.wstrb  <= (ctx.tr.strb.size() == ctx.beats) ? ctx.tr.strb[i] : '1;
        vif.wlast  <= (i == (ctx.beats-1));
        vif.wuser  <= ctx.tr.user;
        vif.wvalid <= 1'b1;
        wait_w_handshake();
        @(negedge vif.aclk);
        vif.wvalid <= 1'b0;
      end
      wr_wait_b[ctx.tr.id].push_back(ctx);
    end
  endtask

  task automatic pipelined_b_loop();
    axi4_req_ctx_t ctx;
    wait_reset_release();
    forever begin
      // Drive BREADY whenever we have outstanding writes.
      @(negedge vif.aclk);
      vif.bready <= (outstanding_w != 0);

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
    wait_reset_release();
    forever begin
      if (rd_issue_q.size() == 0) begin
        @(posedge vif.aclk);
        continue;
      end
      if (outstanding_r >= cfg.max_outstanding_reads) begin
        @(posedge vif.aclk);
        continue;
      end
      ctx = rd_issue_q.pop_front();

      if (ctx.tr.ar_delay_cycles >= 0) begin
        repeat (ctx.tr.ar_delay_cycles) @(posedge vif.aclk);
      end else begin
        maybe_wait_cycles(cfg.master_ar_delay_min, cfg.master_ar_delay_max);
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
      wait_ar_handshake();
      @(negedge vif.aclk);
      vif.arvalid <= 1'b0;

      outstanding_r++;
      rd_wait_r[ctx.tr.id].push_back(ctx);
    end
  endtask

  task automatic pipelined_r_loop();
    int unsigned rready_low_left;
    wait_reset_release();
    rready_low_left = 0;
    forever begin
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

  task automatic wait_aw_handshake();
    int unsigned cycles = 0;
    while (1) begin
      @(posedge vif.aclk);
      if (vif.awready) break;
      cycles++;
      if ((cfg.handshake_timeout_cycles != 0) && (cycles > cfg.handshake_timeout_cycles)) begin
        `uvm_fatal(RID, "Handshake timeout on AW")
      end
    end
  endtask

  task automatic wait_w_handshake();
    int unsigned cycles = 0;
    while (1) begin
      @(posedge vif.aclk);
      if (vif.wready) break;
      cycles++;
      if ((cfg.handshake_timeout_cycles != 0) && (cycles > cfg.handshake_timeout_cycles)) begin
        `uvm_fatal(RID, "Handshake timeout on W")
      end
    end
  endtask

  task automatic wait_ar_handshake();
    int unsigned cycles = 0;
    while (1) begin
      @(posedge vif.aclk);
      if (vif.arready) break;
      cycles++;
      if ((cfg.handshake_timeout_cycles != 0) && (cycles > cfg.handshake_timeout_cycles)) begin
        `uvm_fatal(RID, "Handshake timeout on AR")
      end
    end
  endtask

  task automatic drive_write(axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) tr);
    int unsigned beats;
    int unsigned cycles;
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
    wait_aw_handshake();
    @(negedge vif.aclk);
    vif.awvalid <= 1'b0;

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
      wait_w_handshake();
      @(negedge vif.aclk);
      vif.wvalid <= 1'b0;
    end

    // B
    @(negedge vif.aclk);
    vif.bready <= 1'b1;
    cycles = 0;
    while (1) begin
      @(posedge vif.aclk);
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
    wait_ar_handshake();
    @(negedge vif.aclk);
    vif.arvalid <= 1'b0;

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
