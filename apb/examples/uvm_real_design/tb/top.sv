`timescale 1ns/1ps

module tb_top;
  import uvm_pkg::*;
  import tb_pkg::*;

  localparam int ADDR_W = 16;
  localparam int DATA_W = 32;
  localparam int NSEL   = 1;

  logic PCLK;
  logic PRESETn;

  apb_if #(ADDR_W, DATA_W, NSEL) apb (.*);

  apb_ram_slave #(.ADDR_W(ADDR_W), .DATA_W(DATA_W), .NSEL(NSEL), .WAIT_STATES(1)) dut (
    .PCLK(PCLK), .PRESETn(PRESETn),
    .PADDR(apb.PADDR), .PSEL(apb.PSEL), .PENABLE(apb.PENABLE), .PWRITE(apb.PWRITE),
    .PWDATA(apb.PWDATA), .PRDATA(apb.PRDATA), .PREADY(apb.PREADY), .PSLVERR(apb.PSLVERR),
    .PPROT(apb.PPROT), .PSTRB(apb.PSTRB)
  );

  initial begin
    PCLK = 0;
    forever #5ns PCLK = ~PCLK;
  end

  initial begin
    PRESETn = 1'b0;
    repeat (5) @(posedge PCLK);
    PRESETn = 1'b1;
  end

  initial begin
    `include "kvips_wave_dump.svh"
    `KVIPS_MAYBE_ENABLE_WAVES("kvips_apb_real_design")
  end

  initial begin
    uvm_config_db#(virtual interface apb_if #(ADDR_W, DATA_W, NSEL))::set(null, "*", "vif", apb);
    run_test();
  end
endmodule
