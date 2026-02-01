//------------------------------------------------------------------------------
// APB3/APB4 Assertions (interface-bound)
//------------------------------------------------------------------------------
// Runtime switches:
// - Disable all:            +KVIPS_APB_ASSERT_OFF
// - Disable X/known checks: +KVIPS_APB_ASSERT_KNOWN_OFF
// - Disable strict rules:   +KVIPS_APB_ASSERT_STRICT_OFF
//
// Protocol selection:
// - +APB_PROTOCOL=APB3|APB4 (defaults to APB4 if not specified)
//------------------------------------------------------------------------------
`ifndef KVIPS_APB_IF_SVA_SVH
`define KVIPS_APB_IF_SVA_SVH

  bit kvips_apb_assert_en;
  bit kvips_apb_known_en;
  bit kvips_apb_strict_en;
  bit kvips_apb_apb4_en;

  initial begin
    string s;
    kvips_apb_assert_en = !$test$plusargs("KVIPS_APB_ASSERT_OFF");
    kvips_apb_known_en  = !$test$plusargs("KVIPS_APB_ASSERT_KNOWN_OFF");
    kvips_apb_strict_en = !$test$plusargs("KVIPS_APB_ASSERT_STRICT_OFF");

    // Protocol selection for APB4-specific checks.
    // Default: APB4 enabled unless explicitly requested APB3.
    kvips_apb_apb4_en = 1'b1;
    if ($value$plusargs("APB_PROTOCOL=%s", s)) begin
      if ((s == "APB3") || (s == "apb3")) kvips_apb_apb4_en = 1'b0;
      if ((s == "APB4") || (s == "apb4")) kvips_apb_apb4_en = 1'b1;
    end
  end

  // Convenience (sampled via monitor clocking block to avoid race with #0 drives)
  wire kvips_xfer_setup  = (|cb_mon.PSEL) && !cb_mon.PENABLE;
  wire kvips_xfer_access = (|cb_mon.PSEL) &&  cb_mon.PENABLE;
  wire kvips_xfer_done   = (|cb_mon.PSEL) &&  cb_mon.PENABLE && cb_mon.PREADY;

  // PENABLE can only be asserted when PSEL is asserted.
  property p_penable_only_with_psel;
    @(cb_mon) disable iff (!PRESETn || !kvips_apb_assert_en)
      cb_mon.PENABLE |-> (|cb_mon.PSEL);
  endproperty
  a_penable_only_with_psel: assert property (p_penable_only_with_psel);

  // Setup phase precedes access: if we see access, there must have been setup
  // in the prior cycle. Only check on entry into ACCESS (wait-states keep
  // ACCESS asserted across cycles).
  property p_setup_precedes_access;
    @(cb_mon) disable iff (!PRESETn || !kvips_apb_assert_en)
      (kvips_xfer_access && !$past(kvips_xfer_access)) |-> $past(kvips_xfer_setup);
  endproperty
  a_setup_precedes_access: assert property (p_setup_precedes_access);

  // During access wait-states, address/control/data must remain stable.
  property p_stable_during_wait;
    @(cb_mon) disable iff (!PRESETn || !kvips_apb_assert_en || !kvips_apb_strict_en)
      (kvips_xfer_access && !cb_mon.PREADY) |->
        ($stable(cb_mon.PADDR) && $stable(cb_mon.PWRITE) && $stable(cb_mon.PWDATA) &&
         $stable(cb_mon.PSEL) && $stable(cb_mon.PPROT) && $stable(cb_mon.PSTRB));
  endproperty
  a_stable_during_wait: assert property (p_stable_during_wait);

  // No X/Z on key control signals during active transfer (optional).
  property p_known_controls;
    @(cb_mon) disable iff (!PRESETn || !kvips_apb_assert_en || !kvips_apb_known_en)
      (|cb_mon.PSEL) |-> (!$isunknown(cb_mon.PENABLE) && !$isunknown(cb_mon.PWRITE) && !$isunknown(cb_mon.PADDR) && !$isunknown(cb_mon.PSEL));
  endproperty
  a_known_controls: assert property (p_known_controls);

  // Strict: PSEL must not be X and must be onehot0 in typical single-target usage.
  property p_onehot_psel;
    @(cb_mon) disable iff (!PRESETn || !kvips_apb_assert_en || !kvips_apb_strict_en)
      1'b1 |-> $onehot0(cb_mon.PSEL);
  endproperty
  a_onehot_psel: assert property (p_onehot_psel);

  // APB4-specific: PSTRB/PPROT are meaningful; ensure stable across transfer.
  property p_pstrb_nonzero_on_write;
    @(cb_mon) disable iff (!PRESETn || !kvips_apb_assert_en || !kvips_apb_strict_en || !kvips_apb_apb4_en)
      (kvips_xfer_access && cb_mon.PWRITE) |-> (cb_mon.PSTRB != '0);
  endproperty
  a_pstrb_nonzero_on_write: assert property (p_pstrb_nonzero_on_write);

  property p_pprot_known_when_selected;
    @(cb_mon) disable iff (!PRESETn || !kvips_apb_assert_en || !kvips_apb_known_en || !kvips_apb_apb4_en)
      (|cb_mon.PSEL) |-> (!$isunknown(cb_mon.PPROT));
  endproperty
  a_pprot_known_when_selected: assert property (p_pprot_known_when_selected);

`endif // KVIPS_APB_IF_SVA_SVH
