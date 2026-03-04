`timescale 1ns/1ps

module top;
  import uvm_pkg::*;
  import axi4_uvm_pkg::*;
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

`ifdef VERILATOR
  // Keep simulation running long enough under Verilator UVM/no-DPI flow.
  initial begin
    bit en;
    longint unsigned wr_txns, wr_err, rd_txns, rd_uninit, rd_mis;
    axi4_scoreboard#(ADDR_W, DATA_W, ID_W, USER_W) sb_h;
    wait (areset_n === 1'b1);
    repeat (20000) @(posedge aclk);
    if ($cast(sb_h, uvm_root::get().find("uvm_test_top.sb"))) begin
      sb_h.get_summary(en, wr_txns, wr_err, rd_txns, rd_uninit, rd_mis);
      uvm_report_info("AXI4_SCB",
        $sformatf("AXI4 SB summary: enable=%0d wr_txns=%0d wr_err=%0d rd_txns=%0d rd_mismatch_beats=%0d rd_uninit_warn_beats=%0d",
          en, wr_txns, wr_err, rd_txns, rd_mis, rd_uninit),
        UVM_NONE);
      if (en && ((wr_txns + rd_txns) == 0))
        uvm_report_error("AXI4_SCB", "AXI4 scoreboard observed zero transactions");
    end
    $finish;
  end
`endif

  initial begin
    uvm_config_db#(virtual interface axi4_if #(ADDR_W, DATA_W, ID_W, USER_W))::set(null, "*", "vif", axi);
`ifdef VERILATOR
    uvm_root::get().set_finish_on_completion(1'b0);
`endif
    run_test();
  end
endmodule
