//------------------------------------------------------------------------------
// KVIPS cocotb bridge opcodes (shared by SV bridge + Python)
//------------------------------------------------------------------------------
`ifndef KVIPS_COCOTB_OPCODES_SVH
`define KVIPS_COCOTB_OPCODES_SVH

// Common
localparam logic [7:0] KVIPS_OP_NOP        = 8'h00;
localparam logic [7:0] KVIPS_OP_FINISH     = 8'hFF;
localparam logic [7:0] KVIPS_OP_PING       = 8'hFE;
localparam logic [7:0] KVIPS_OP_GET_STATS  = 8'hFD;

// Protocol IDs (monitor stream)
localparam logic [7:0] KVIPS_PROTO_APB     = 8'h01;
localparam logic [7:0] KVIPS_PROTO_AXI4    = 8'h02;
localparam logic [7:0] KVIPS_PROTO_AHB     = 8'h03;

// APB ops
localparam logic [7:0] KVIPS_APB_WRITE     = 8'h10;
localparam logic [7:0] KVIPS_APB_READ      = 8'h11;
localparam logic [7:0] KVIPS_APB_SEQ_SMOKE = 8'h12;
localparam logic [7:0] KVIPS_APB_SEQ_STRESS= 8'h13;
localparam logic [7:0] KVIPS_APB_SEQ_STROBE= 8'h14;

// AXI4 ops / sequences (0x20-0x2F, 0x40-0x4F — avoid AHB 0x30-0x3F)
localparam logic [7:0] KVIPS_AXI4_WRITE         = 8'h20;
localparam logic [7:0] KVIPS_AXI4_READ          = 8'h21;
localparam logic [7:0] KVIPS_AXI4_WRITE_BURST   = 8'h22;
localparam logic [7:0] KVIPS_AXI4_READ_BURST    = 8'h23;
localparam logic [7:0] KVIPS_AXI4_SEQ_WRB       = 8'h24; // write_readback
localparam logic [7:0] KVIPS_AXI4_SEQ_WBRST     = 8'h25; // write_burst
localparam logic [7:0] KVIPS_AXI4_SEQ_RBRST     = 8'h26; // read_burst
localparam logic [7:0] KVIPS_AXI4_SEQ_STRESS    = 8'h27; // stress (non-pipe WRB-style)
localparam logic [7:0] KVIPS_AXI4_SEQ_LANE      = 8'h28;
localparam logic [7:0] KVIPS_AXI4_SEQ_STROBE    = 8'h29;
localparam logic [7:0] KVIPS_AXI4_SEQ_CONCURRENT= 8'h2A;
localparam logic [7:0] KVIPS_AXI4_SEQ_UNALIGNED = 8'h2B;
localparam logic [7:0] KVIPS_AXI4_SEQ_CORNER    = 8'h2C;
localparam logic [7:0] KVIPS_AXI4_SEQ_INCR256   = 8'h2D;
localparam logic [7:0] KVIPS_AXI4_SEQ_PHASE_API = 8'h2E;
localparam logic [7:0] KVIPS_AXI4_SEQ_WR_EXPECT = 8'h2F;
localparam logic [7:0] KVIPS_AXI4_SEQ_RD_EXPECT = 8'h40;
localparam logic [7:0] KVIPS_AXI4_SEQ_SAME_ID   = 8'h41;
localparam logic [7:0] KVIPS_AXI4_SEQ_SIDEBAND  = 8'h42;
localparam logic [7:0] KVIPS_AXI4_SEQ_EXCL_BASIC= 8'h43; // needs excl slave → INVAL on RAM DUT
localparam logic [7:0] KVIPS_AXI4_SEQ_EXCL_FAIL = 8'h44;
localparam logic [7:0] KVIPS_AXI4_SEQ_EXCL_XID  = 8'h45;
localparam logic [7:0] KVIPS_AXI4_SEQ_EXCL_ILL  = 8'h46;
localparam logic [7:0] KVIPS_AXI4_SEQ_ERR_WR    = 8'h47; // OOR DECERR directed
localparam logic [7:0] KVIPS_AXI4_SEQ_ERR_RD    = 8'h48;
localparam logic [7:0] KVIPS_AXI4_SEQ_RESET     = 8'h49; // needs mid-run reset → INVAL
localparam logic [7:0] KVIPS_AXI4_SEQ_NP_RESET  = 8'h4A;
localparam logic [7:0] KVIPS_AXI4_SEQ_TIMEOUT   = 8'h4B; // needs AW stall → INVAL
localparam logic [7:0] KVIPS_AXI4_SEQ_PIPE_STRESS = 8'h4C; // alias non-pipe stress on RAM DUT

// AHB ops / sequences
localparam logic [7:0] KVIPS_AHB_WRITE          = 8'h30;
localparam logic [7:0] KVIPS_AHB_READ           = 8'h31;
localparam logic [7:0] KVIPS_AHB_SEQ_SMOKE      = 8'h32;
localparam logic [7:0] KVIPS_AHB_SEQ_SINGLE     = 8'h33;
localparam logic [7:0] KVIPS_AHB_SEQ_INCR       = 8'h34;
localparam logic [7:0] KVIPS_AHB_SEQ_WRAP       = 8'h35;
localparam logic [7:0] KVIPS_AHB_SEQ_B2B        = 8'h36;
localparam logic [7:0] KVIPS_AHB_SEQ_WAIT       = 8'h37;
localparam logic [7:0] KVIPS_AHB_SEQ_STRESS     = 8'h38;
localparam logic [7:0] KVIPS_AHB_SEQ_BUSY       = 8'h39;
localparam logic [7:0] KVIPS_AHB_SEQ_BOUNDARY   = 8'h3A;
localparam logic [7:0] KVIPS_AHB_SEQ_ENDIAN     = 8'h3B;
localparam logic [7:0] KVIPS_AHB_SEQ_SECURITY   = 8'h3C; // needs policy → INVAL on RAM DUT
localparam logic [7:0] KVIPS_AHB_SEQ_FULL_RESP  = 8'h3D;
localparam logic [7:0] KVIPS_AHB_SEQ_ERROR      = 8'h3E; // needs err slave → INVAL on RAM DUT

// Response status
localparam logic [31:0] KVIPS_RSP_OK     = 32'h0;
localparam logic [31:0] KVIPS_RSP_ERR    = 32'h1;
localparam logic [31:0] KVIPS_RSP_BUSY   = 32'h2;
localparam logic [31:0] KVIPS_RSP_INVAL  = 32'h3;

`endif
