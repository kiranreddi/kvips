//------------------------------------------------------------------------------
// APB Types Package
//------------------------------------------------------------------------------
`ifndef KVIPS_APB_TYPES_PKG_SV
`define KVIPS_APB_TYPES_PKG_SV

package apb_types_pkg;

  typedef enum int unsigned {
    APB_PROTOCOL_APB3 = 3,
    APB_PROTOCOL_APB4 = 4
  } apb_protocol_e;

  typedef enum int unsigned {
    APB_RESP_OK  = 0,
    APB_RESP_ERR = 1
  } apb_resp_e;

endpackage

`endif // KVIPS_APB_TYPES_PKG_SV

