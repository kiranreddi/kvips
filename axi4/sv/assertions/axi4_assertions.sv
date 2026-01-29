//------------------------------------------------------------------------------
// AXI4 Assertions (SVA)
//------------------------------------------------------------------------------
// Lightweight protocol assertions intended to catch common AXI4 violations:
// - VALID/payload stability while stalled (VALID && !READY)
// - Basic legality checks (SIZE vs data width)
// - Optional X/Z checks on key signals
//
// Runtime switches (plusargs):
// - Disable all:         +KVIPS_AXI4_ASSERT_OFF
// - Enable known checks: +KVIPS_AXI4_ASSERT_KNOWN
//------------------------------------------------------------------------------

`ifndef KVIPS_AXI4_ASSERTIONS_SV
`define KVIPS_AXI4_ASSERTIONS_SV

module axi4_assertions #(
  parameter int ADDR_W = 32,
  parameter int DATA_W = 64,
  parameter int ID_W   = 4,
  parameter int USER_W = 1
) (
  axi4_if #(
    .ADDR_W(ADDR_W),
    .DATA_W(DATA_W),
    .ID_W  (ID_W),
    .USER_W(USER_W)
  ).monitor_mp bus
);

  localparam int STRB_W = DATA_W/8;

  bit assertions_on;
  bit known_checks_on;

  initial begin
    assertions_on   = !$test$plusargs("KVIPS_AXI4_ASSERT_OFF");
    known_checks_on =  $test$plusargs("KVIPS_AXI4_ASSERT_KNOWN");
  end

  // -------------------------
  // VALID/payload stability
  // -------------------------

  property p_aw_hold;
    @(posedge bus.aclk) disable iff (!bus.areset_n || !assertions_on)
      (bus.mon_cb.awvalid && !bus.mon_cb.awready)
        |=> (bus.mon_cb.awvalid &&
             $stable({bus.mon_cb.awid, bus.mon_cb.awaddr, bus.mon_cb.awlen, bus.mon_cb.awsize,
                      bus.mon_cb.awburst, bus.mon_cb.awlock, bus.mon_cb.awcache, bus.mon_cb.awprot,
                      bus.mon_cb.awqos, bus.mon_cb.awregion, bus.mon_cb.awuser}));
  endproperty
  a_aw_hold: assert property (p_aw_hold);

  property p_w_hold;
    @(posedge bus.aclk) disable iff (!bus.areset_n || !assertions_on)
      (bus.mon_cb.wvalid && !bus.mon_cb.wready)
        |=> (bus.mon_cb.wvalid &&
             $stable({bus.mon_cb.wdata, bus.mon_cb.wstrb, bus.mon_cb.wlast, bus.mon_cb.wuser}));
  endproperty
  a_w_hold: assert property (p_w_hold);

  property p_b_hold;
    @(posedge bus.aclk) disable iff (!bus.areset_n || !assertions_on)
      (bus.mon_cb.bvalid && !bus.mon_cb.bready)
        |=> (bus.mon_cb.bvalid &&
             $stable({bus.mon_cb.bid, bus.mon_cb.bresp, bus.mon_cb.buser}));
  endproperty
  a_b_hold: assert property (p_b_hold);

  property p_ar_hold;
    @(posedge bus.aclk) disable iff (!bus.areset_n || !assertions_on)
      (bus.mon_cb.arvalid && !bus.mon_cb.arready)
        |=> (bus.mon_cb.arvalid &&
             $stable({bus.mon_cb.arid, bus.mon_cb.araddr, bus.mon_cb.arlen, bus.mon_cb.arsize,
                      bus.mon_cb.arburst, bus.mon_cb.arlock, bus.mon_cb.arcache, bus.mon_cb.arprot,
                      bus.mon_cb.arqos, bus.mon_cb.arregion, bus.mon_cb.aruser}));
  endproperty
  a_ar_hold: assert property (p_ar_hold);

  property p_r_hold;
    @(posedge bus.aclk) disable iff (!bus.areset_n || !assertions_on)
      (bus.mon_cb.rvalid && !bus.mon_cb.rready)
        |=> (bus.mon_cb.rvalid &&
             $stable({bus.mon_cb.rid, bus.mon_cb.rdata, bus.mon_cb.rresp, bus.mon_cb.rlast, bus.mon_cb.ruser}));
  endproperty
  a_r_hold: assert property (p_r_hold);

  // -------------------------
  // Basic legality checks
  // -------------------------

  property p_aw_size_legal;
    @(posedge bus.aclk) disable iff (!bus.areset_n || !assertions_on)
      (bus.mon_cb.awvalid) |-> ((1 << bus.mon_cb.awsize) <= STRB_W);
  endproperty
  a_aw_size_legal: assert property (p_aw_size_legal);

  property p_ar_size_legal;
    @(posedge bus.aclk) disable iff (!bus.areset_n || !assertions_on)
      (bus.mon_cb.arvalid) |-> ((1 << bus.mon_cb.arsize) <= STRB_W);
  endproperty
  a_ar_size_legal: assert property (p_ar_size_legal);

  // -------------------------
  // Optional X/Z checks
  // -------------------------

  property p_known_aw;
    @(posedge bus.aclk) disable iff (!bus.areset_n || !assertions_on || !known_checks_on)
      (bus.mon_cb.awvalid) |-> (!$isunknown({bus.mon_cb.awid, bus.mon_cb.awaddr, bus.mon_cb.awlen, bus.mon_cb.awsize, bus.mon_cb.awburst}));
  endproperty
  a_known_aw: assert property (p_known_aw);

  property p_known_w;
    @(posedge bus.aclk) disable iff (!bus.areset_n || !assertions_on || !known_checks_on)
      (bus.mon_cb.wvalid) |-> (!$isunknown({bus.mon_cb.wdata, bus.mon_cb.wstrb, bus.mon_cb.wlast}));
  endproperty
  a_known_w: assert property (p_known_w);

  property p_known_ar;
    @(posedge bus.aclk) disable iff (!bus.areset_n || !assertions_on || !known_checks_on)
      (bus.mon_cb.arvalid) |-> (!$isunknown({bus.mon_cb.arid, bus.mon_cb.araddr, bus.mon_cb.arlen, bus.mon_cb.arsize, bus.mon_cb.arburst}));
  endproperty
  a_known_ar: assert property (p_known_ar);

  property p_known_r;
    @(posedge bus.aclk) disable iff (!bus.areset_n || !assertions_on || !known_checks_on)
      (bus.mon_cb.rvalid) |-> (!$isunknown({bus.mon_cb.rid, bus.mon_cb.rdata, bus.mon_cb.rlast, bus.mon_cb.rresp}));
  endproperty
  a_known_r: assert property (p_known_r);

  property p_known_b;
    @(posedge bus.aclk) disable iff (!bus.areset_n || !assertions_on || !known_checks_on)
      (bus.mon_cb.bvalid) |-> (!$isunknown({bus.mon_cb.bid, bus.mon_cb.bresp}));
  endproperty
  a_known_b: assert property (p_known_b);

endmodule

`endif // KVIPS_AXI4_ASSERTIONS_SV
