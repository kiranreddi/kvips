//------------------------------------------------------------------------------
// AHB Types Package
//------------------------------------------------------------------------------
`ifndef KVIPS_AHB_TYPES_PKG_SV
`define KVIPS_AHB_TYPES_PKG_SV

package ahb_types_pkg;

  typedef enum int unsigned {
    AHB_MODE_LITE = 0,
    AHB_MODE_FULL = 1
  } ahb_mode_e;

  typedef enum logic [1:0] {
    AHB_TRANS_IDLE   = 2'b00,
    AHB_TRANS_BUSY   = 2'b01,
    AHB_TRANS_NONSEQ = 2'b10,
    AHB_TRANS_SEQ    = 2'b11
  } ahb_trans_e;

  typedef enum logic [2:0] {
    AHB_SIZE_8    = 3'b000,
    AHB_SIZE_16   = 3'b001,
    AHB_SIZE_32   = 3'b010,
    AHB_SIZE_64   = 3'b011,
    AHB_SIZE_128  = 3'b100,
    AHB_SIZE_256  = 3'b101,
    AHB_SIZE_512  = 3'b110,
    AHB_SIZE_1024 = 3'b111
  } ahb_size_e;

  typedef enum logic [2:0] {
    AHB_BURST_SINGLE = 3'b000,
    AHB_BURST_INCR   = 3'b001,
    AHB_BURST_WRAP4  = 3'b010,
    AHB_BURST_INCR4  = 3'b011,
    AHB_BURST_WRAP8  = 3'b100,
    AHB_BURST_INCR8  = 3'b101,
    AHB_BURST_WRAP16 = 3'b110,
    AHB_BURST_INCR16 = 3'b111
  } ahb_burst_e;

  // HRESP encoding: AHB-Lite uses 1-bit (OKAY/ERROR). AHB full has 2-bit.
  typedef enum int unsigned {
    AHB_RESP_OKAY  = 0,
    AHB_RESP_ERROR = 1,
    AHB_RESP_RETRY = 2,
    AHB_RESP_SPLIT = 3
  } ahb_resp_e;

endpackage

`endif // KVIPS_AHB_TYPES_PKG_SV

