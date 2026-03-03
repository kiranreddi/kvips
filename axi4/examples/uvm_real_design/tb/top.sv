`timescale 1ns/1ps

module top;
  import uvm_pkg::*;
  import tb_pkg::*;

  localparam int ADDR_W = 32;
  localparam int DATA_W = 64;
  localparam int ID_W   = 4;
  localparam int USER_W = 1;

  logic aclk;
  logic areset_n;

  axi4_if #(ADDR_W, DATA_W, ID_W, USER_W) axi (.*);

  axi4_ram_slave #(
    .ADDR_W(ADDR_W), .DATA_W(DATA_W), .ID_W(ID_W), .USER_W(USER_W)
  ) dut (
    .aclk(aclk), .areset_n(areset_n),
    .awid(axi.awid), .awaddr(axi.awaddr), .awlen(axi.awlen), .awsize(axi.awsize), .awburst(axi.awburst), .awuser(axi.awuser), .awvalid(axi.awvalid), .awready(axi.awready),
    .wdata(axi.wdata), .wstrb(axi.wstrb), .wlast(axi.wlast), .wvalid(axi.wvalid), .wready(axi.wready),
    .bid(axi.bid), .bresp(axi.bresp), .buser(axi.buser), .bvalid(axi.bvalid), .bready(axi.bready),
    .arid(axi.arid), .araddr(axi.araddr), .arlen(axi.arlen), .arsize(axi.arsize), .arburst(axi.arburst), .aruser(axi.aruser), .arvalid(axi.arvalid), .arready(axi.arready),
    .rid(axi.rid), .rdata(axi.rdata), .rresp(axi.rresp), .rlast(axi.rlast), .ruser(axi.ruser), .rvalid(axi.rvalid), .rready(axi.rready)
  );

  initial begin
    aclk = 0;
    forever #5 aclk = ~aclk;
  end

  initial begin
    areset_n = 0;
    repeat (10) @(posedge aclk);
    areset_n = 1;
  end

  initial begin
    `include "kvips_wave_dump.svh"
    `KVIPS_MAYBE_ENABLE_WAVES("kvips_axi4_real_design")
  end

  initial begin
    uvm_config_db#(virtual interface axi4_if #(ADDR_W, DATA_W, ID_W, USER_W))::set(null, "*", "vif", axi);
    run_test();
  end
endmodule
