//------------------------------------------------------------------------------
// AXI4 Interface
//------------------------------------------------------------------------------
// IEEE 1800 SystemVerilog interface encapsulating AXI4 (full) signals.
//
// Notes:
// - Parameterized widths for re-use across projects.
// - Provides role-specific modports for master/slave BFMs and a passive monitor.
//------------------------------------------------------------------------------

`ifndef KVIPS_AXI4_IF_SV
`define KVIPS_AXI4_IF_SV

interface axi4_if #(
  parameter int ADDR_W = 32,
  parameter int DATA_W = 64,
  parameter int ID_W   = 4,
  parameter int USER_W = 1
) (
  input  logic aclk,
  input  logic areset_n
);

  localparam int STRB_W = DATA_W / 8;

  // -------------------------
  // Write address channel (AW)
  // -------------------------
  logic [ID_W-1:0]        awid;
  logic [ADDR_W-1:0]      awaddr;
  logic [7:0]             awlen;
  logic [2:0]             awsize;
  logic [1:0]             awburst;
  logic                   awlock;
  logic [3:0]             awcache;
  logic [2:0]             awprot;
  logic [3:0]             awqos;
  logic [3:0]             awregion;
  logic [USER_W-1:0]      awuser;
  logic                   awvalid;
  logic                   awready;

  // -------------------------
  // Write data channel (W)
  // -------------------------
  logic [DATA_W-1:0]      wdata;
  logic [STRB_W-1:0]      wstrb;
  logic                   wlast;
  logic [USER_W-1:0]      wuser;
  logic                   wvalid;
  logic                   wready;

  // -------------------------
  // Write response channel (B)
  // -------------------------
  logic [ID_W-1:0]        bid;
  logic [1:0]             bresp;
  logic [USER_W-1:0]      buser;
  logic                   bvalid;
  logic                   bready;

  // -------------------------
  // Read address channel (AR)
  // -------------------------
  logic [ID_W-1:0]        arid;
  logic [ADDR_W-1:0]      araddr;
  logic [7:0]             arlen;
  logic [2:0]             arsize;
  logic [1:0]             arburst;
  logic                   arlock;
  logic [3:0]             arcache;
  logic [2:0]             arprot;
  logic [3:0]             arqos;
  logic [3:0]             arregion;
  logic [USER_W-1:0]      aruser;
  logic                   arvalid;
  logic                   arready;

  // -------------------------
  // Read data channel (R)
  // -------------------------
  logic [ID_W-1:0]        rid;
  logic [DATA_W-1:0]      rdata;
  logic [1:0]             rresp;
  logic                   rlast;
  logic [USER_W-1:0]      ruser;
  logic                   rvalid;
  logic                   rready;

  // -------------------------
  // Clocking blocks (BFM friendly)
  // -------------------------
  clocking m_cb @(posedge aclk);
    default input #1step output #0;
    output awid, awaddr, awlen, awsize, awburst, awlock, awcache, awprot, awqos, awregion, awuser, awvalid;
    input  awready;
    output wdata, wstrb, wlast, wuser, wvalid;
    input  wready;
    input  bid, bresp, buser, bvalid;
    output bready;
    output arid, araddr, arlen, arsize, arburst, arlock, arcache, arprot, arqos, arregion, aruser, arvalid;
    input  arready;
    input  rid, rdata, rresp, rlast, ruser, rvalid;
    output rready;
  endclocking

  clocking s_cb @(posedge aclk);
    default input #1step output #0;
    input  awid, awaddr, awlen, awsize, awburst, awlock, awcache, awprot, awqos, awregion, awuser, awvalid;
    output awready;
    input  wdata, wstrb, wlast, wuser, wvalid;
    output wready;
    output bid, bresp, buser, bvalid;
    input  bready;
    input  arid, araddr, arlen, arsize, arburst, arlock, arcache, arprot, arqos, arregion, aruser, arvalid;
    output arready;
    output rid, rdata, rresp, rlast, ruser, rvalid;
    input  rready;
  endclocking

  clocking mon_cb @(posedge aclk);
    default input #1step;
    input awid, awaddr, awlen, awsize, awburst, awlock, awcache, awprot, awqos, awregion, awuser, awvalid, awready;
    input wdata, wstrb, wlast, wuser, wvalid, wready;
    input bid, bresp, buser, bvalid, bready;
    input arid, araddr, arlen, arsize, arburst, arlock, arcache, arprot, arqos, arregion, aruser, arvalid, arready;
    input rid, rdata, rresp, rlast, ruser, rvalid, rready;
  endclocking

  // -------------------------
  // Modports
  // -------------------------
  modport master_mp (
    input  aclk, areset_n,
    clocking m_cb
  );

  modport slave_mp (
    input  aclk, areset_n,
    clocking s_cb
  );

  modport monitor_mp (
    input  aclk, areset_n,
    clocking mon_cb
  );

  // -------------------------
  // Assertions (included here for widest simulator compatibility)
  // -------------------------
`ifndef KVIPS_AXI4_NO_ASSERTIONS
  `include "axi4_if_sva.svh"
`endif

endinterface

`endif // KVIPS_AXI4_IF_SV
