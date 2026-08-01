//------------------------------------------------------------------------------
// KVIPS cocotb DPI package — imports C DPI symbols into SV
//------------------------------------------------------------------------------
`timescale 1ns/1ps

package kvips_cocotb_dpi_pkg;

  import "DPI-C" function void kvips_dpi_mon_push(
    input int proto,
    input int write,
    input longint addr,
    input longint data,
    input int resp,
    input int strb,
    input int len,
    input int id
  );

  import "DPI-C" function void kvips_dpi_rsp_push(
    input int status,
    input longint d0,
    input longint d1,
    input longint d2,
    input longint d3
  );

  import "DPI-C" function void kvips_dpi_log(input string msg);
  import "DPI-C" function void kvips_dpi_reset();

endpackage
