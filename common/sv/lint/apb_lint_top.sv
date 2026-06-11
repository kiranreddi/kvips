//------------------------------------------------------------------------------
// APB lint top (for Verilator lint-only runs)
//------------------------------------------------------------------------------

`include "apb_if.sv"

module apb_lint_top;
  logic PCLK;
  logic PRESETn;

  initial begin
    PCLK = 1'b0;
    PRESETn = 1'b1;
  end

  apb_if #(
    .ADDR_W(32),
    .DATA_W(32),
    .NSEL(1)
  ) apb_lint_if (
    .PCLK(PCLK),
    .PRESETn(PRESETn)
  );

endmodule
