//------------------------------------------------------------------------------
// AHB lint top (for Verilator lint-only runs)
//------------------------------------------------------------------------------

`include "ahb_if.sv"

module ahb_lint_top;
  logic HCLK;
  logic HRESETn;

  initial begin
    HCLK = 1'b0;
    HRESETn = 1'b1;
  end

  ahb_if #(
    .ADDR_W(32),
    .DATA_W(32),
    .HAS_HMASTLOCK(1'b0),
    .HRESP_W(2)
  ) ahb_lint_if (
    .HCLK(HCLK),
    .HRESETn(HRESETn)
  );

endmodule
