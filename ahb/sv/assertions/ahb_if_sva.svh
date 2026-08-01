//------------------------------------------------------------------------------
// AHB Assertions (interface-bound)
//------------------------------------------------------------------------------
// Runtime switches:
// - Disable all:            +KVIPS_AHB_ASSERT_OFF
// - Disable X/known checks: +KVIPS_AHB_ASSERT_KNOWN_OFF
// - Disable strict rules:   +KVIPS_AHB_ASSERT_STRICT_OFF
//
// Mode selection:
// - +AHB_MODE=AHB_LITE|AHB_FULL (defaults to AHB_LITE if not specified)
//------------------------------------------------------------------------------
`ifndef KVIPS_AHB_IF_SVA_SVH
`define KVIPS_AHB_IF_SVA_SVH

  bit kvips_ahb_assert_en;
  bit kvips_ahb_known_en;
  bit kvips_ahb_strict_en;
  bit kvips_ahb_full_en;
  bit kvips_ahb_busy_en;
  bit kvips_ahb_prev_not_ready;

  initial begin
    string s;
    kvips_ahb_assert_en = !$test$plusargs("KVIPS_AHB_ASSERT_OFF");
    kvips_ahb_known_en  = !$test$plusargs("KVIPS_AHB_ASSERT_KNOWN_OFF");
    // Strict checks are opt-in; many real fabrics legitimately use BUSY or have
    // implementation-specific behavior that would otherwise flood logs.
    kvips_ahb_strict_en = $test$plusargs("KVIPS_AHB_ASSERT_STRICT_ON") &&
                          !$test$plusargs("KVIPS_AHB_ASSERT_STRICT_OFF");
    kvips_ahb_busy_en = $test$plusargs("KVIPS_AHB_BUSY_ON");

    kvips_ahb_full_en = 1'b0;
    if ($value$plusargs("AHB_MODE=%s", s)) begin
      if ((s == "AHB_FULL") || (s == "ahb_full") || (s == "FULL") || (s == "full")) kvips_ahb_full_en = 1'b1;
      if ((s == "AHB_LITE") || (s == "ahb_lite") || (s == "LITE") || (s == "lite")) kvips_ahb_full_en = 1'b0;
    end
  end

`ifdef VERILATOR
  `define AHB_CLK posedge HCLK
  wire kvips_ahb_xfer_valid = (HTRANS[1] == 1'b1); // NONSEQ/SEQ
`else
  `define AHB_CLK cb_mon
  wire kvips_ahb_xfer_valid = (cb_mon.HTRANS[1] == 1'b1); // NONSEQ/SEQ
`endif

  always @(posedge HCLK or negedge HRESETn) begin
    if (!HRESETn) kvips_ahb_prev_not_ready <= 1'b0;
    else          kvips_ahb_prev_not_ready <= !HREADY;
  end

  // Across extended wait states, master must hold address/control stable.
  property p_hold_ctrl_when_stalled;
    @(`AHB_CLK) disable iff (!HRESETn || !kvips_ahb_assert_en || !kvips_ahb_strict_en)
`ifdef VERILATOR
      (!HREADY && kvips_ahb_prev_not_ready) |-> ($stable(HADDR) && $stable(HTRANS) && $stable(HWRITE) && $stable(HSIZE) && $stable(HBURST) && $stable(HPROT) && $stable(HNONSEC) && $stable(HSEL));
`else
      (!cb_mon.HREADY && kvips_ahb_prev_not_ready) |-> ($stable(cb_mon.HADDR) && $stable(cb_mon.HTRANS) && $stable(cb_mon.HWRITE) && $stable(cb_mon.HSIZE) && $stable(cb_mon.HBURST) && $stable(cb_mon.HPROT) && $stable(cb_mon.HNONSEC) && $stable(cb_mon.HSEL));
`endif
  endproperty
  a_hold_ctrl_when_stalled: assert property (p_hold_ctrl_when_stalled);

  // If HREADY is low, write data must be stable (data phase held).
  property p_hold_wdata_when_stalled;
    @(`AHB_CLK) disable iff (!HRESETn || !kvips_ahb_assert_en || !kvips_ahb_strict_en)
`ifdef VERILATOR
      (!HREADY && kvips_ahb_prev_not_ready) |-> $stable(HWDATA);
`else
      (!cb_mon.HREADY && kvips_ahb_prev_not_ready) |-> $stable(cb_mon.HWDATA);
`endif
  endproperty
  a_hold_wdata_when_stalled: assert property (p_hold_wdata_when_stalled);

  // HTRANS BUSY is optional; in strict mode, disallow it unless explicitly enabled
  // (we treat BUSY as rarely used and default drivers avoid it).
  property p_no_busy_by_default;
    @(`AHB_CLK) disable iff (!HRESETn || !kvips_ahb_assert_en || !kvips_ahb_strict_en)
`ifdef VERILATOR
      (!kvips_ahb_busy_en) |-> (HTRANS != 2'b01);
`else
      (!kvips_ahb_busy_en) |-> (cb_mon.HTRANS != 2'b01);
`endif
  endproperty
  a_no_busy_by_default: assert property (p_no_busy_by_default);

  // Optional strict legality check for the address/control phase.  The
  // master driver performs the same check before issuing a sequence item;
  // keeping a monitor-side assertion catches illegal traffic from an external
  // DUT or a deliberately negative test as well.
  function automatic bit kvips_ahb_transfer_legal(
    input logic [ADDR_W-1:0] addr,
    input logic [2:0]        size
  );
    int unsigned bytes;
    bytes = 1 << int'(size);
    return (bytes <= (DATA_W / 8)) && ((int'(addr) % bytes) == 0);
  endfunction

  property p_transfer_alignment_width;
    @(`AHB_CLK) disable iff (!HRESETn || !kvips_ahb_assert_en || !kvips_ahb_strict_en)
`ifdef VERILATOR
      (kvips_ahb_xfer_valid && HSEL && HREADY) |-> kvips_ahb_transfer_legal(HADDR, HSIZE);
`else
      (kvips_ahb_xfer_valid && cb_mon.HSEL && cb_mon.HREADY) |-> kvips_ahb_transfer_legal(cb_mon.HADDR, cb_mon.HSIZE);
`endif
  endproperty
  a_transfer_alignment_width: assert property (p_transfer_alignment_width);

  // AHB-Lite response legality: for 2-bit HRESP, reject RETRY/SPLIT in LITE mode.
  generate
    if (HRESP_W == 2) begin : g_hresp2
      property p_lite_hresp_legal;
        @(`AHB_CLK) disable iff (!HRESETn || !kvips_ahb_assert_en)
`ifdef VERILATOR
          ((!kvips_ahb_full_en) && kvips_ahb_xfer_valid && HSEL && HREADY) |-> (HRESP inside {2'b00, 2'b01});
`else
          ((!kvips_ahb_full_en) && kvips_ahb_xfer_valid && cb_mon.HSEL && cb_mon.HREADY) |-> (cb_mon.HRESP inside {2'b00, 2'b01});
`endif
      endproperty
      a_lite_hresp_legal: assert property (p_lite_hresp_legal);
    end
  endgenerate

  // No X/Z on key control signals during active transfer (optional).
  property p_known_controls;
    @(`AHB_CLK) disable iff (!HRESETn || !kvips_ahb_assert_en || !kvips_ahb_known_en)
`ifdef VERILATOR
      (kvips_ahb_xfer_valid) |-> (!$isunknown(HADDR) && !$isunknown(HTRANS) && !$isunknown(HWRITE) && !$isunknown(HSIZE) && !$isunknown(HBURST) && !$isunknown(HPROT));
`else
      (kvips_ahb_xfer_valid) |-> (!$isunknown(cb_mon.HADDR) && !$isunknown(cb_mon.HTRANS) && !$isunknown(cb_mon.HWRITE) && !$isunknown(cb_mon.HSIZE) && !$isunknown(cb_mon.HBURST) && !$isunknown(cb_mon.HPROT));
`endif
  endproperty
  a_known_controls: assert property (p_known_controls);

`undef AHB_CLK

`endif // KVIPS_AHB_IF_SVA_SVH
