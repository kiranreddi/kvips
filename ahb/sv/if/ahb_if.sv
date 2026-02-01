//------------------------------------------------------------------------------
// AHB Interface (AHB-Lite / AHB Full superset)
//------------------------------------------------------------------------------
// Notes:
// - This interface is a superset to support AHB-Lite and AHB Full with a single
//   compilation unit. Mode is selected at runtime via +AHB_MODE=AHB_LITE|AHB_FULL.
// - The canonical AHB pipeline rule applies: address/control in cycle N, data
//   phase in cycle N+1, with HREADY gating acceptance and completion.
//------------------------------------------------------------------------------
`timescale 1ns/1ps

`ifndef KVIPS_AHB_IF_SV
`define KVIPS_AHB_IF_SV

interface ahb_if #(
  int ADDR_W = 32,
  int DATA_W = 32,
  bit HAS_HSEL      = 1'b1,
  bit HAS_HREADYOUT = 1'b1,
  bit HAS_HMASTLOCK = 1'b0,
  bit HAS_HMASTER   = 1'b0,
  int HMASTER_W     = 4,
  int HRESP_W       = 2
) (
  input  logic HCLK,
  input  logic HRESETn
);

  // Address/control
  logic [ADDR_W-1:0] HADDR;
  logic [1:0]        HTRANS;
  logic              HWRITE;
  logic [2:0]        HSIZE;
  logic [2:0]        HBURST;
  logic [3:0]        HPROT;
  logic              HMASTLOCK;
  logic [HMASTER_W-1:0] HMASTER;

  // Optional decode select (commonly provided by interconnect)
  logic              HSEL;

  // Data
  logic [DATA_W-1:0] HWDATA;
  logic [DATA_W-1:0] HRDATA;

  // Handshake/response
  logic              HREADY;     // global ready seen by master
  logic              HREADYOUT;  // slave-ready (single slave: HREADY=HREADYOUT)
  logic [HRESP_W-1:0] HRESP;

  // Clocking blocks (posedge HCLK)
  clocking cb_m @(posedge HCLK);
    default input #1step output #0;
    output HADDR, HTRANS, HWRITE, HSIZE, HBURST, HPROT, HWDATA, HSEL, HMASTLOCK, HMASTER;
    input  HREADY, HREADYOUT, HRESP, HRDATA;
  endclocking

  clocking cb_s @(posedge HCLK);
    default input #1step output #0;
    input  HADDR, HTRANS, HWRITE, HSIZE, HBURST, HPROT, HWDATA, HSEL, HMASTLOCK, HMASTER, HREADY;
    output HREADYOUT, HRESP, HRDATA;
  endclocking

  clocking cb_mon @(posedge HCLK);
    default input #1step output #0;
    input HADDR, HTRANS, HWRITE, HSIZE, HBURST, HPROT, HWDATA, HSEL, HMASTLOCK, HMASTER, HREADY, HREADYOUT, HRESP, HRDATA;
  endclocking

  modport master (clocking cb_m, input HCLK, input HRESETn);
  modport slave  (clocking cb_s, input HCLK, input HRESETn);
  modport mon    (clocking cb_mon, input HCLK, input HRESETn);

  // Reasonable defaults for optional signals when not used
  generate
    if (!HAS_HSEL) begin : g_no_hsel
      always_comb HSEL = 1'b1;
    end
    if (!HAS_HREADYOUT) begin : g_no_hreadyout
      always_comb HREADYOUT = 1'b1;
    end
    if (!HAS_HMASTLOCK) begin : g_no_hmastlock
      always_comb HMASTLOCK = 1'b0;
    end
    if (!HAS_HMASTER) begin : g_no_hmaster
      always_comb HMASTER = '0;
    end
  endgenerate

  // Optional assertions (bound into the interface for portability)
  `include "ahb_if_sva.svh"

endinterface

`endif // KVIPS_AHB_IF_SV
