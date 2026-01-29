//------------------------------------------------------------------------------
// AXI4 Assertion Helper Macros
//------------------------------------------------------------------------------

`ifndef KVIPS_AXI4_ASSERTIONS_MACROS_SVH
`define KVIPS_AXI4_ASSERTIONS_MACROS_SVH

`define KVIPS_AXI4_INSTANTIATE_ASSERTIONS(INST, NAME, AW, DW, IW, UW) \
  axi4_assertions #( \
    .ADDR_W(AW), .DATA_W(DW), .ID_W(IW), .USER_W(UW) \
  ) NAME ( .bus(INST) );

`endif
