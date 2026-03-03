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
`ifdef VERILATOR
    areset_n = 1'b1;
`else
    areset_n = 0;
    repeat (10) @(posedge aclk);
    areset_n = 1;
`endif
  end

  initial begin
    `include "kvips_wave_dump.svh"
    `KVIPS_MAYBE_ENABLE_WAVES("kvips_axi4_real_design")
  end

`ifdef VERILATOR
  // Keep run phase alive long enough under Verilator UVM/no-DPI flow.
  initial begin
    uvm_phase run_phase_h;
    uvm_objection run_obj_h;
    run_phase_h = uvm_run_phase::get();
    run_obj_h = (run_phase_h == null) ? null : run_phase_h.get_objection();
    if (run_obj_h != null) begin
      run_obj_h.raise_objection(null, "kvips_verilator_runtime_hold");
      wait (areset_n === 1'b1);
      repeat (2000) @(posedge aclk);
      run_obj_h.drop_objection(null, "kvips_verilator_runtime_hold");
    end
  end
`endif

  initial begin
    uvm_config_db#(virtual interface axi4_if #(ADDR_W, DATA_W, ID_W, USER_W))::set(null, "*", "vif", axi);
    run_test();
  end
endmodule
