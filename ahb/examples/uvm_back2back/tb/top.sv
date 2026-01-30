`timescale 1ns/1ps

module top;
  import uvm_pkg::*;
  import tb_pkg::*;

  logic HCLK;
  logic HRESETn;

  initial begin
    HCLK = 1'b0;
    forever #5 HCLK = ~HCLK;
  end

  initial begin
    HRESETn = 1'b0;
    repeat (10) @(posedge HCLK);
    HRESETn = 1'b1;
  end

  // Single-bus back-to-back: one master + one slave
  ahb_if #(32, 32) ahb_if0 (.HCLK(HCLK), .HRESETn(HRESETn));

  // For a single-slave example, HREADY is just the slave's HREADYOUT.
  always_comb ahb_if0.HREADY = ahb_if0.HREADYOUT;

  initial begin
    uvm_config_db#(virtual ahb_if)::set(null, "*", "vif", ahb_if0);
    run_test();
  end
endmodule

