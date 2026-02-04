//------------------------------------------------------------------------------
// APB3/APB4 Interface
//------------------------------------------------------------------------------
// Notes:
// - Includes APB4 signals (PPROT/PSTRB) unconditionally for single-image builds.
// - Protocol mode is selected at runtime via +APB_PROTOCOL=APB3|APB4 and/or cfg.
//------------------------------------------------------------------------------
`timescale 1ns/1ps

`ifndef KVIPS_APB_IF_SV
`define KVIPS_APB_IF_SV

interface apb_if #(
  int ADDR_W = 32,
  int DATA_W = 32,
  int NSEL   = 1
) (
  input  logic PCLK,
  input  logic PRESETn
);

  localparam int STRB_W = (DATA_W/8);

  logic [ADDR_W-1:0] PADDR;
  logic [NSEL-1:0]   PSEL;
  logic              PENABLE;
  logic              PWRITE;
  logic [DATA_W-1:0] PWDATA;
  logic [DATA_W-1:0] PRDATA;
  logic              PREADY;
  logic              PSLVERR;

  // APB4 extras (still present in APB3 mode; ignored/forced by VIP)
  logic [2:0]        PPROT;
  logic [STRB_W-1:0] PSTRB;

  // Clocking blocks (all sampled on posedge PCLK)
`ifndef VERILATOR
  clocking cb_m @(posedge PCLK);
    // Sample-only clocking block (drivers write via vif.*).
    default input #1step;
    input PADDR, PSEL, PENABLE, PWRITE, PWDATA, PRDATA, PREADY, PSLVERR, PPROT, PSTRB;
  endclocking

  clocking cb_s @(posedge PCLK);
    default input #1step;
    input PADDR, PSEL, PENABLE, PWRITE, PWDATA, PRDATA, PREADY, PSLVERR, PPROT, PSTRB;
  endclocking

  clocking cb_mon @(posedge PCLK);
    default input #1step;
    input PADDR, PSEL, PENABLE, PWRITE, PWDATA, PRDATA, PREADY, PSLVERR, PPROT, PSTRB;
  endclocking
`endif

`ifndef VERILATOR
  modport master (clocking cb_m, input PCLK, input PRESETn);
  modport slave  (clocking cb_s, input PCLK, input PRESETn);
  modport mon    (clocking cb_mon, input PCLK, input PRESETn);
`endif

  // Optional assertions (bound into the interface for portability)
`ifndef VERILATOR
  `include "apb_if_sva.svh"
`endif

endinterface

`endif // KVIPS_APB_IF_SV
