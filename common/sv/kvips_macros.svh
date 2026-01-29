//------------------------------------------------------------------------------
// KVIPS Common Macros
//------------------------------------------------------------------------------
// Small set of helper macros shared across VIPs.
//------------------------------------------------------------------------------

`ifndef KVIPS_MACROS_SVH
`define KVIPS_MACROS_SVH

`define KVIPS_PLUSARG_TRUE(ARG) ($test$plusargs(ARG))

`define KVIPS_GET_PLUSARG_INT(ARG, VAR, DEFAULT) \
  begin \
    VAR = DEFAULT; \
    void'($value$plusargs({ARG,"=%d"}, VAR)); \
  end

`endif // KVIPS_MACROS_SVH

