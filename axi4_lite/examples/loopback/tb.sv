`timescale 1ns/1ps

module tb;
  localparam int ADDR_W = 32;
  localparam int DATA_W = 32;
  localparam int STRB_W = DATA_W / 8;

  logic aclk = 1'b0;
  logic areset_n = 1'b0;
  integer errors = 0;

  always #5 aclk = ~aclk;

  axi4_lite_if #(ADDR_W, DATA_W) axi(.aclk(aclk), .areset_n(areset_n));
  axi4_lite_loopback #(64) dut(.axi(axi));

  task automatic wait_cycles(input integer count);
    repeat (count) @(posedge aclk);
  endtask

  task automatic send_aw(input logic [ADDR_W-1:0] addr);
    @(negedge aclk);
    axi.awaddr  = addr;
    axi.awvalid = 1'b1;
    do @(posedge aclk); while (!axi.awready);
    @(negedge aclk);
    axi.awvalid = 1'b0;
  endtask

  task automatic send_w(input logic [DATA_W-1:0] data,
                        input logic [STRB_W-1:0] strb);
    @(negedge aclk);
    axi.wdata  = data;
    axi.wstrb  = strb;
    axi.wvalid = 1'b1;
    do @(posedge aclk); while (!axi.wready);
    @(negedge aclk);
    axi.wvalid = 1'b0;
  endtask

  task automatic get_b(output logic [1:0] resp);
    @(negedge aclk);
    axi.bready = 1'b1;
    do @(posedge aclk); while (!axi.bvalid);
    resp = axi.bresp;
    @(negedge aclk);
    axi.bready = 1'b0;
  endtask

  task automatic write_w_before_aw(input logic [ADDR_W-1:0] addr,
                                   input logic [DATA_W-1:0] data,
                                   input logic [STRB_W-1:0] strb,
                                   output logic [1:0] resp);
    fork
      send_w(data, strb);
      begin
        wait_cycles(1);
        send_aw(addr);
      end
      get_b(resp);
    join
  endtask

  task automatic write_aw_before_w(input logic [ADDR_W-1:0] addr,
                                   input logic [DATA_W-1:0] data,
                                   input logic [STRB_W-1:0] strb,
                                   output logic [1:0] resp);
    fork
      send_aw(addr);
      begin
        wait_cycles(1);
        send_w(data, strb);
      end
      get_b(resp);
    join
  endtask

  task automatic read_word(input logic [ADDR_W-1:0] addr,
                           output logic [DATA_W-1:0] data,
                           output logic [1:0] resp);
    @(negedge aclk);
    axi.araddr  = addr;
    axi.arvalid = 1'b1;
    axi.rready  = 1'b1;
    do @(posedge aclk); while (!axi.arready);
    @(negedge aclk);
    axi.arvalid = 1'b0;
    do @(posedge aclk); while (!axi.rvalid);
    data = axi.rdata;
    resp = axi.rresp;
    @(negedge aclk);
    axi.rready = 1'b0;
  endtask

  task automatic check(input bit condition, input string message);
    if (!condition) begin
      errors = errors + 1;
      $error("AXI4-LITE CHECK FAILED: %s", message);
    end
  endtask

  logic [1:0] bresp;
  logic [1:0] rresp;
  logic [DATA_W-1:0] rdata;
  initial begin
    axi.awaddr = '0; axi.awvalid = 1'b0;
    axi.wdata = '0; axi.wstrb = '0; axi.wvalid = 1'b0;
    axi.bready = 1'b0; axi.araddr = '0; axi.arvalid = 1'b0;
    axi.rready = 1'b0;
    wait_cycles(3);
    @(negedge aclk);
    areset_n = 1'b1;
    wait_cycles(2);

    // Exercise both legal independent write-channel orderings.
    write_w_before_aw(32'h0000_0000, 32'h1122_3344, 4'b1111, bresp);
    check(bresp == 2'b00, "W-before-AW write response");
    write_aw_before_w(32'h0000_0004, 32'haabb_ccdd, 4'b1111, bresp);
    check(bresp == 2'b00, "AW-before-W write response");

    read_word(32'h0000_0000, rdata, rresp);
    check(rresp == 2'b00 && rdata == 32'h1122_3344, "first readback");
    read_word(32'h0000_0004, rdata, rresp);
    check(rresp == 2'b00 && rdata == 32'haabb_ccdd, "second readback");

    // Byte strobes update only selected lanes.
    write_aw_before_w(32'h0000_0000, 32'hxxxx_xx55, 4'b0001, bresp);
    check(bresp == 2'b00, "partial write response");
    read_word(32'h0000_0000, rdata, rresp);
    check(rresp == 2'b00 && rdata == 32'h1122_3355, "byte strobe preservation");

    // Hold BREADY low and prove BVALID is retained, then complete the write.
    send_aw(32'h0000_0008);
    send_w(32'h5566_7788, 4'b1111);
    @(negedge aclk);
    axi.bready = 1'b0;
    do @(posedge aclk); while (!axi.bvalid);
    repeat (3) begin
      @(posedge aclk);
      check(axi.bvalid, "BVALID held during response backpressure");
    end
    @(negedge aclk);
    axi.bready = 1'b1;
    @(posedge aclk);
    bresp = axi.bresp;
    @(negedge aclk);
    axi.bready = 1'b0;
    check(bresp == 2'b00, "backpressured write response");

    // Addresses outside the modeled aperture return DECERR.
    write_aw_before_w(32'h0000_1000, 32'hdead_beef, 4'b1111, bresp);
    check(bresp == 2'b11, "unmapped write DECERR");
    read_word(32'h0000_1000, rdata, rresp);
    check(rresp == 2'b11 && rdata == '0, "unmapped read DECERR");

    if (errors == 0)
      $display("AXI4-LITE LOOPBACK PASS");
    else
      $fatal(1, "AXI4-LITE LOOPBACK FAIL: %0d errors", errors);
    $finish;
  end
endmodule
