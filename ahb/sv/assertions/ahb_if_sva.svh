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

  initial begin
    string s;
    kvips_ahb_assert_en = !$test$plusargs("KVIPS_AHB_ASSERT_OFF");
    kvips_ahb_known_en  = !$test$plusargs("KVIPS_AHB_ASSERT_KNOWN_OFF");
    kvips_ahb_strict_en = !$test$plusargs("KVIPS_AHB_ASSERT_STRICT_OFF");

    kvips_ahb_full_en = 1'b0;
    if ($value$plusargs("AHB_MODE=%s", s)) begin
      if ((s == "AHB_FULL") || (s == "ahb_full") || (s == "FULL") || (s == "full")) kvips_ahb_full_en = 1'b1;
      if ((s == "AHB_LITE") || (s == "ahb_lite") || (s == "LITE") || (s == "lite")) kvips_ahb_full_en = 1'b0;
    end
  end

  wire kvips_ahb_xfer_valid = (HTRANS[1] == 1'b1); // NONSEQ/SEQ

  // If HREADY is low, master must hold address/control stable.
  property p_hold_ctrl_when_stalled;
    @(posedge HCLK) disable iff (!HRESETn || !kvips_ahb_assert_en)
      (!HREADY) |-> ($stable(HADDR) && $stable(HTRANS) && $stable(HWRITE) && $stable(HSIZE) && $stable(HBURST) && $stable(HPROT) && $stable(HSEL));
  endproperty
  a_hold_ctrl_when_stalled: assert property (p_hold_ctrl_when_stalled);

  // If HREADY is low, write data must be stable (data phase held).
  property p_hold_wdata_when_stalled;
    @(posedge HCLK) disable iff (!HRESETn || !kvips_ahb_assert_en || !kvips_ahb_strict_en)
      (!HREADY) |-> $stable(HWDATA);
  endproperty
  a_hold_wdata_when_stalled: assert property (p_hold_wdata_when_stalled);

  // HTRANS BUSY is optional; in strict mode, disallow it unless explicitly enabled
  // (we treat BUSY as rarely used and default drivers avoid it).
  property p_no_busy_by_default;
    @(posedge HCLK) disable iff (!HRESETn || !kvips_ahb_assert_en || !kvips_ahb_strict_en)
      1'b1 |-> (HTRANS != 2'b01);
  endproperty
  a_no_busy_by_default: assert property (p_no_busy_by_default);

  // AHB-Lite response legality: for 2-bit HRESP, reject RETRY/SPLIT in LITE mode.
  generate
    if (HRESP_W == 2) begin : g_hresp2
      property p_lite_hresp_legal;
        @(posedge HCLK) disable iff (!HRESETn || !kvips_ahb_assert_en)
          (!kvips_ahb_full_en) |-> (HRESP inside {2'b00, 2'b01});
      endproperty
      a_lite_hresp_legal: assert property (p_lite_hresp_legal);
    end
  endgenerate

  // No X/Z on key control signals during active transfer (optional).
  property p_known_controls;
    @(posedge HCLK) disable iff (!HRESETn || !kvips_ahb_assert_en || !kvips_ahb_known_en)
      (kvips_ahb_xfer_valid) |-> (!$isunknown(HADDR) && !$isunknown(HTRANS) && !$isunknown(HWRITE) && !$isunknown(HSIZE) && !$isunknown(HBURST) && !$isunknown(HPROT));
  endproperty
  a_known_controls: assert property (p_known_controls);

`endif // KVIPS_AHB_IF_SVA_SVH
