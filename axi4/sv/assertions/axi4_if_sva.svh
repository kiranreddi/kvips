//------------------------------------------------------------------------------
// AXI4 SVA (included inside axi4_if)
//------------------------------------------------------------------------------
// This file is `include`'d from `axi4_if.sv` to avoid simulator limitations
// around parameterized-interface ports on standalone assertion modules.
//
// Runtime switches (plusargs):
// - Disable all:         +KVIPS_AXI4_ASSERT_OFF
// - Enable known checks: +KVIPS_AXI4_ASSERT_KNOWN
//------------------------------------------------------------------------------

bit kvips_axi4_assertions_on;
bit kvips_axi4_known_checks_on;
bit kvips_axi4_burst_checks_on;
bit kvips_axi4_excl_checks_on;
int unsigned kvips_axi4_max_outs_w;
int unsigned kvips_axi4_max_outs_r;

localparam logic [1:0] KVIPS_AXI4_RESP_EXOKAY = 2'b01;

initial begin
  kvips_axi4_assertions_on   = !$test$plusargs("KVIPS_AXI4_ASSERT_OFF");
  kvips_axi4_known_checks_on =  $test$plusargs("KVIPS_AXI4_ASSERT_KNOWN");
  kvips_axi4_burst_checks_on = !$test$plusargs("KVIPS_AXI4_ASSERT_BURST_OFF");
  kvips_axi4_excl_checks_on  = !$test$plusargs("KVIPS_AXI4_ASSERT_EXCL_OFF");

  kvips_axi4_max_outs_w = 0;
  kvips_axi4_max_outs_r = 0;
  void'($value$plusargs("KVIPS_AXI4_ASSERT_MAX_OUTS_W=%d", kvips_axi4_max_outs_w));
  void'($value$plusargs("KVIPS_AXI4_ASSERT_MAX_OUTS_R=%d", kvips_axi4_max_outs_r));
end

function automatic longint unsigned kvips_bytes_per_beat(input logic [2:0] size);
  return (longint'(1) << size);
endfunction

function automatic longint unsigned kvips_total_bytes(input logic [7:0] len, input logic [2:0] size);
  return (longint'(len) + 1) * kvips_bytes_per_beat(size);
endfunction

function automatic bit kvips_wrap_len_legal(input logic [7:0] len);
  return (len == 8'd1) || (len == 8'd3) || (len == 8'd7) || (len == 8'd15);
endfunction

function automatic bit kvips_crosses_4kb(
  input logic [ADDR_W-1:0] addr,
  input logic [7:0]        len,
  input logic [2:0]        size,
  input logic [1:0]        burst
);
  longint unsigned start_b;
  longint unsigned end_b;
  longint unsigned total;
  if (burst == 2'b00) return 1'b0; // FIXED does not advance address
  total   = kvips_total_bytes(len, size);
  start_b = longint'(addr);
  end_b   = (total == 0) ? start_b : (start_b + total - 1);
  return ((start_b >> 12) != (end_b >> 12));
endfunction

function automatic bit kvips_wrap_addr_aligned(
  input logic [ADDR_W-1:0] addr,
  input logic [7:0]        len,
  input logic [2:0]        size
);
  longint unsigned container;
  container = kvips_total_bytes(len, size);
  if (container == 0) return 1'b1;
  return ((longint'(addr) % container) == 0);
endfunction

// VALID/payload stability while stalled (VALID && !READY)
property kvips_p_aw_hold;
  @(posedge aclk) disable iff (!areset_n || !kvips_axi4_assertions_on)
    (awvalid && !awready)
      |=> (awvalid &&
           $stable({awid, awaddr, awlen, awsize, awburst, awlock, awcache, awprot, awqos, awregion, awuser}));
endproperty
a_kvips_aw_hold: assert property (kvips_p_aw_hold);

property kvips_p_w_hold;
  @(posedge aclk) disable iff (!areset_n || !kvips_axi4_assertions_on)
    (wvalid && !wready)
      |=> (wvalid && $stable({wdata, wstrb, wlast, wuser}));
endproperty
a_kvips_w_hold: assert property (kvips_p_w_hold);

property kvips_p_b_hold;
  @(posedge aclk) disable iff (!areset_n || !kvips_axi4_assertions_on)
    (bvalid && !bready)
      |=> (bvalid && $stable({bid, bresp, buser}));
endproperty
a_kvips_b_hold: assert property (kvips_p_b_hold);

property kvips_p_ar_hold;
  @(posedge aclk) disable iff (!areset_n || !kvips_axi4_assertions_on)
    (arvalid && !arready)
      |=> (arvalid &&
           $stable({arid, araddr, arlen, arsize, arburst, arlock, arcache, arprot, arqos, arregion, aruser}));
endproperty
a_kvips_ar_hold: assert property (kvips_p_ar_hold);

property kvips_p_r_hold;
  @(posedge aclk) disable iff (!areset_n || !kvips_axi4_assertions_on)
    (rvalid && !rready)
      |=> (rvalid && $stable({rid, rdata, rresp, rlast, ruser}));
endproperty
a_kvips_r_hold: assert property (kvips_p_r_hold);

// Basic legality checks: SIZE vs DATA_W
property kvips_p_aw_size_legal;
  @(posedge aclk) disable iff (!areset_n || !kvips_axi4_assertions_on)
    awvalid |-> ((1 << awsize) <= STRB_W);
endproperty
a_kvips_aw_size_legal: assert property (kvips_p_aw_size_legal);

property kvips_p_ar_size_legal;
  @(posedge aclk) disable iff (!areset_n || !kvips_axi4_assertions_on)
    arvalid |-> ((1 << arsize) <= STRB_W);
endproperty
a_kvips_ar_size_legal: assert property (kvips_p_ar_size_legal);

// Burst legality checks (AMBA4 AXI4 basics)
property kvips_p_aw_burst_legal;
  @(posedge aclk) disable iff (!areset_n || !kvips_axi4_assertions_on || !kvips_axi4_burst_checks_on)
    awvalid |-> (awburst inside {2'b00,2'b01,2'b10});
endproperty
a_kvips_aw_burst_legal: assert property (kvips_p_aw_burst_legal);

property kvips_p_ar_burst_legal;
  @(posedge aclk) disable iff (!areset_n || !kvips_axi4_assertions_on || !kvips_axi4_burst_checks_on)
    arvalid |-> (arburst inside {2'b00,2'b01,2'b10});
endproperty
a_kvips_ar_burst_legal: assert property (kvips_p_ar_burst_legal);

property kvips_p_aw_len_legal;
  @(posedge aclk) disable iff (!areset_n || !kvips_axi4_assertions_on || !kvips_axi4_burst_checks_on)
    awvalid |-> ((awburst == 2'b01) ? (awlen <= 8'd255) : (awlen <= 8'd15));
endproperty
a_kvips_aw_len_legal: assert property (kvips_p_aw_len_legal);

property kvips_p_ar_len_legal;
  @(posedge aclk) disable iff (!areset_n || !kvips_axi4_assertions_on || !kvips_axi4_burst_checks_on)
    arvalid |-> ((arburst == 2'b01) ? (arlen <= 8'd255) : (arlen <= 8'd15));
endproperty
a_kvips_ar_len_legal: assert property (kvips_p_ar_len_legal);

property kvips_p_aw_wrap_len_legal;
  @(posedge aclk) disable iff (!areset_n || !kvips_axi4_assertions_on || !kvips_axi4_burst_checks_on)
    awvalid |-> ((awburst == 2'b10) ? kvips_wrap_len_legal(awlen) : 1'b1);
endproperty
a_kvips_aw_wrap_len_legal: assert property (kvips_p_aw_wrap_len_legal);

property kvips_p_ar_wrap_len_legal;
  @(posedge aclk) disable iff (!areset_n || !kvips_axi4_assertions_on || !kvips_axi4_burst_checks_on)
    arvalid |-> ((arburst == 2'b10) ? kvips_wrap_len_legal(arlen) : 1'b1);
endproperty
a_kvips_ar_wrap_len_legal: assert property (kvips_p_ar_wrap_len_legal);

property kvips_p_aw_wrap_addr_aligned;
  @(posedge aclk) disable iff (!areset_n || !kvips_axi4_assertions_on || !kvips_axi4_burst_checks_on)
    awvalid |-> ((awburst == 2'b10) ? kvips_wrap_addr_aligned(awaddr, awlen, awsize) : 1'b1);
endproperty
a_kvips_aw_wrap_addr_aligned: assert property (kvips_p_aw_wrap_addr_aligned);

property kvips_p_ar_wrap_addr_aligned;
  @(posedge aclk) disable iff (!areset_n || !kvips_axi4_assertions_on || !kvips_axi4_burst_checks_on)
    arvalid |-> ((arburst == 2'b10) ? kvips_wrap_addr_aligned(araddr, arlen, arsize) : 1'b1);
endproperty
a_kvips_ar_wrap_addr_aligned: assert property (kvips_p_ar_wrap_addr_aligned);

property kvips_p_aw_no_4kb_cross;
  @(posedge aclk) disable iff (!areset_n || !kvips_axi4_assertions_on || !kvips_axi4_burst_checks_on)
    awvalid |-> (!kvips_crosses_4kb(awaddr, awlen, awsize, awburst));
endproperty
a_kvips_aw_no_4kb_cross: assert property (kvips_p_aw_no_4kb_cross);

property kvips_p_ar_no_4kb_cross;
  @(posedge aclk) disable iff (!areset_n || !kvips_axi4_assertions_on || !kvips_axi4_burst_checks_on)
    arvalid |-> (!kvips_crosses_4kb(araddr, arlen, arsize, arburst));
endproperty
a_kvips_ar_no_4kb_cross: assert property (kvips_p_ar_no_4kb_cross);

// Exclusive access restrictions (AXI4, conservative checks)
property kvips_p_aw_excl_restrictions;
  @(posedge aclk) disable iff (!areset_n || !kvips_axi4_assertions_on || !kvips_axi4_excl_checks_on)
    (awvalid && awlock) |->
      (awburst == 2'b01) &&
      (awlen <= 8'd15) &&
      (kvips_total_bytes(awlen, awsize) <= 128) &&
      ((longint'(awaddr) % kvips_bytes_per_beat(awsize)) == 0) &&
      (!kvips_crosses_4kb(awaddr, awlen, awsize, awburst));
endproperty
a_kvips_aw_excl_restrictions: assert property (kvips_p_aw_excl_restrictions);

property kvips_p_ar_excl_restrictions;
  @(posedge aclk) disable iff (!areset_n || !kvips_axi4_assertions_on || !kvips_axi4_excl_checks_on)
    (arvalid && arlock) |->
      (arburst == 2'b01) &&
      (arlen <= 8'd15) &&
      (kvips_total_bytes(arlen, arsize) <= 128) &&
      ((longint'(araddr) % kvips_bytes_per_beat(arsize)) == 0) &&
      (!kvips_crosses_4kb(araddr, arlen, arsize, arburst));
endproperty
a_kvips_ar_excl_restrictions: assert property (kvips_p_ar_excl_restrictions);

// Optional X/Z checks
property kvips_p_known_aw;
  @(posedge aclk) disable iff (!areset_n || !kvips_axi4_assertions_on || !kvips_axi4_known_checks_on)
    awvalid |-> (!$isunknown({awid, awaddr, awlen, awsize, awburst}));
endproperty
a_kvips_known_aw: assert property (kvips_p_known_aw);

property kvips_p_known_w;
  @(posedge aclk) disable iff (!areset_n || !kvips_axi4_assertions_on || !kvips_axi4_known_checks_on)
    wvalid |-> (!$isunknown({wdata, wstrb, wlast}));
endproperty
a_kvips_known_w: assert property (kvips_p_known_w);

property kvips_p_known_ar;
  @(posedge aclk) disable iff (!areset_n || !kvips_axi4_assertions_on || !kvips_axi4_known_checks_on)
    arvalid |-> (!$isunknown({arid, araddr, arlen, arsize, arburst}));
endproperty
a_kvips_known_ar: assert property (kvips_p_known_ar);

property kvips_p_known_r;
  @(posedge aclk) disable iff (!areset_n || !kvips_axi4_assertions_on || !kvips_axi4_known_checks_on)
    rvalid |-> (!$isunknown({rid, rdata, rlast, rresp}));
endproperty
a_kvips_known_r: assert property (kvips_p_known_r);

property kvips_p_known_b;
  @(posedge aclk) disable iff (!areset_n || !kvips_axi4_assertions_on || !kvips_axi4_known_checks_on)
    bvalid |-> (!$isunknown({bid, bresp}));
endproperty
a_kvips_known_b: assert property (kvips_p_known_b);

// -----------------------------------------------------------------------------
// Stateful protocol checks (portable "compliance" starter set)
// -----------------------------------------------------------------------------

typedef struct packed {
  logic [ID_W-1:0] id;
  int unsigned     beats_left;
  bit              lock;
} kvips_wr_ctx_t;

kvips_wr_ctx_t kvips_wr_fifo[$];
bit kvips_wr_done_lock_q[logic [ID_W-1:0]][$];
int unsigned kvips_outs_w;

int unsigned kvips_rd_beats_q[logic [ID_W-1:0]][$];
bit kvips_rd_lock_q[logic [ID_W-1:0]][$];
int unsigned kvips_outs_r;

always_ff @(posedge aclk) begin
  if (!areset_n || !kvips_axi4_assertions_on) begin
    kvips_wr_fifo.delete();
    foreach (kvips_wr_done_lock_q[id]) kvips_wr_done_lock_q[id].delete();
    kvips_outs_w <= 0;

    foreach (kvips_rd_beats_q[id]) kvips_rd_beats_q[id].delete();
    foreach (kvips_rd_lock_q[id])  kvips_rd_lock_q[id].delete();
    kvips_outs_r <= 0;
  end else begin
    // -----------------
    // AW -> W tracking (W has no ID; must follow AW order)
    // -----------------
    if (awvalid && awready) begin
      kvips_wr_ctx_t ctx;
      ctx.id = awid;
      ctx.beats_left = int'(awlen) + 1;
      ctx.lock = awlock;
      kvips_wr_fifo.push_back(ctx);
      kvips_outs_w <= kvips_outs_w + 1;
    end

    if (wvalid && wready) begin
      if (kvips_wr_fifo.size() == 0) begin
        $error("KVIPS_AXI4_ASSERT: W beat seen with no outstanding AW");
      end else begin
        kvips_wr_ctx_t ctx;
        ctx = kvips_wr_fifo[0];
        if (ctx.beats_left == 0) begin
          $error("KVIPS_AXI4_ASSERT: W beat overflow (beats_left==0)");
        end else begin
          if ((ctx.beats_left == 1) && !wlast) begin
            $error("KVIPS_AXI4_ASSERT: Missing WLAST on final W beat");
          end
          if ((ctx.beats_left != 1) && wlast) begin
            $error("KVIPS_AXI4_ASSERT: Unexpected WLAST before final W beat");
          end
          ctx.beats_left--;
          kvips_wr_fifo[0] = ctx;
        end
        if (wlast) begin
          // Require the FIFO front to complete.
          if (kvips_wr_fifo[0].beats_left != 0) begin
            $error("KVIPS_AXI4_ASSERT: WLAST asserted but beats_left != 0 after decrement");
          end
          // Mark this write as "data complete" for BID matching.
          kvips_wr_done_lock_q[kvips_wr_fifo[0].id].push_back(kvips_wr_fifo[0].lock);
          void'(kvips_wr_fifo.pop_front());
        end
      end
    end

    // -----------------
    // B must only come after WLAST for the matching ID
    // -----------------
    if (bvalid && bready) begin
      if (!(kvips_wr_done_lock_q.exists(bid)) || (kvips_wr_done_lock_q[bid].size() == 0)) begin
        $error("KVIPS_AXI4_ASSERT: B seen with BID having no completed write data");
      end else begin
        bit lock_seen;
        lock_seen = kvips_wr_done_lock_q[bid].pop_front();
        if ((bresp == KVIPS_AXI4_RESP_EXOKAY) && !lock_seen) begin
          $error("KVIPS_AXI4_ASSERT: BRESP=EXOKAY observed for non-exclusive write");
        end
      end
      if (kvips_outs_w != 0) kvips_outs_w <= kvips_outs_w - 1;
    end

    // -----------------
    // AR -> R tracking (per-ID)
    // -----------------
    if (arvalid && arready) begin
      kvips_rd_beats_q[arid].push_back(int'(arlen) + 1);
      kvips_rd_lock_q[arid].push_back(arlock);
      kvips_outs_r <= kvips_outs_r + 1;
    end

    if (rvalid && rready) begin
      if (!(kvips_rd_beats_q.exists(rid)) || (kvips_rd_beats_q[rid].size() == 0)) begin
        $error("KVIPS_AXI4_ASSERT: R beat seen with no outstanding AR for RID");
      end else begin
        int unsigned beats_left;
        bit lock_seen;
        beats_left = kvips_rd_beats_q[rid][0];
        lock_seen  = kvips_rd_lock_q[rid][0];
        if ((beats_left == 1) && !rlast) begin
          $error("KVIPS_AXI4_ASSERT: Missing RLAST on final R beat");
        end
        if ((beats_left != 1) && rlast) begin
          $error("KVIPS_AXI4_ASSERT: Unexpected RLAST before final R beat");
        end
        if (kvips_axi4_excl_checks_on && (rresp == KVIPS_AXI4_RESP_EXOKAY) && !lock_seen) begin
          $error("KVIPS_AXI4_ASSERT: RRESP=EXOKAY observed for non-exclusive read");
        end
        if (beats_left == 0) begin
          $error("KVIPS_AXI4_ASSERT: R beat overflow (beats_left==0)");
        end else begin
          kvips_rd_beats_q[rid][0] = beats_left - 1;
        end
        if (rlast) begin
          void'(kvips_rd_beats_q[rid].pop_front());
          void'(kvips_rd_lock_q[rid].pop_front());
          if (kvips_outs_r != 0) kvips_outs_r <= kvips_outs_r - 1;
        end
      end
    end
  end
end

// Optional outstanding-limit checks (set via plusargs).
property kvips_p_outs_w_limit;
  @(posedge aclk) disable iff (!areset_n || !kvips_axi4_assertions_on)
    (kvips_axi4_max_outs_w == 0) or (kvips_outs_w <= kvips_axi4_max_outs_w);
endproperty
a_kvips_outs_w_limit: assert property (kvips_p_outs_w_limit);

property kvips_p_outs_r_limit;
  @(posedge aclk) disable iff (!areset_n || !kvips_axi4_assertions_on)
    (kvips_axi4_max_outs_r == 0) or (kvips_outs_r <= kvips_axi4_max_outs_r);
endproperty
a_kvips_outs_r_limit: assert property (kvips_p_outs_r_limit);
