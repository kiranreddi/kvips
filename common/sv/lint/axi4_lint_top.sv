//------------------------------------------------------------------------------
// AXI4 lint top (for Verilator lint-only runs)
//------------------------------------------------------------------------------

module axi4_lint_top;
  logic aclk;
  logic areset_n;

  axi4_if #(
    .ADDR_W(32),
    .DATA_W(64),
    .ID_W(4),
    .USER_W(1)
  ) axi4_lint_if (
    .aclk(aclk),
    .areset_n(areset_n)
  );

endmodule
