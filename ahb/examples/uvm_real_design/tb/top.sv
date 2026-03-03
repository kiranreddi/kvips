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

  localparam int ADDR_W  = 16;
  localparam int DATA_W  = 32;
  localparam int HRESP_W = 2;

  ahb_if #(.ADDR_W(ADDR_W), .DATA_W(DATA_W), .HRESP_W(HRESP_W)) ahb_if0 (.HCLK(HCLK), .HRESETn(HRESETn));

  ahb_ram_slave #(.ADDR_W(ADDR_W), .DATA_W(DATA_W), .HRESP_W(HRESP_W), .WAIT_STATES(1)) dut (
    .HCLK(HCLK), .HRESETn(HRESETn),
    .HADDR(ahb_if0.HADDR), .HTRANS(ahb_if0.HTRANS), .HWRITE(ahb_if0.HWRITE), .HSIZE(ahb_if0.HSIZE), .HBURST(ahb_if0.HBURST), .HPROT(ahb_if0.HPROT),
    .HSEL(ahb_if0.HSEL), .HWDATA(ahb_if0.HWDATA), .HREADY(ahb_if0.HREADY), .HREADYOUT(ahb_if0.HREADYOUT), .HRESP(ahb_if0.HRESP), .HRDATA(ahb_if0.HRDATA)
  );

  assign ahb_if0.HSEL = 1'b1;
`ifdef VERILATOR
  always_ff @(posedge HCLK or negedge HRESETn) begin
    if (!HRESETn) ahb_if0.HREADY <= 1'b1;
    else          ahb_if0.HREADY <= ahb_if0.HREADYOUT;
  end
`else
  assign ahb_if0.HREADY = ahb_if0.HREADYOUT;
`endif

  initial begin
    `include "kvips_wave_dump.svh"
    `KVIPS_MAYBE_ENABLE_WAVES("kvips_ahb_real_design")
  end

`ifdef VERILATOR
  // Keep simulation running long enough under Verilator UVM/no-DPI flow.
  initial begin
    wait (HRESETn === 1'b1);
    repeat (5000) @(posedge HCLK);
    $finish;
  end
`endif

  initial begin
    uvm_config_db#(virtual interface ahb_if #(.ADDR_W(ADDR_W), .DATA_W(DATA_W), .HRESP_W(HRESP_W)))::set(null, "*", "vif", ahb_if0);
`ifdef VERILATOR
    uvm_root::get().set_finish_on_completion(1'b0);
`endif
    run_test();
  end
endmodule
