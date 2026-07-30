//------------------------------------------------------------------------------
// Small AXI4-Lite memory responder used by the portable loopback example.
//------------------------------------------------------------------------------
module axi4_lite_loopback #(
  parameter int DEPTH  = 64
) (
  axi4_lite_if axi
);
  localparam int ADDR_W = $bits(axi.awaddr);
  localparam int DATA_W = $bits(axi.wdata);
  localparam int STRB_W = DATA_W / 8;
  localparam logic [1:0] RESP_OKAY  = 2'b00;
  localparam logic [1:0] RESP_DECERR = 2'b11;

  logic [DATA_W-1:0] mem [0:DEPTH-1];
  logic [ADDR_W-1:0] awaddr_q;
  logic [DATA_W-1:0] wdata_q;
  logic [STRB_W-1:0] wstrb_q;
  logic              aw_pending_q;
  logic              w_pending_q;
  integer            i;

  function automatic bit mapped(input logic [ADDR_W-1:0] addr);
    mapped = (addr < (DEPTH * STRB_W));
  endfunction

  // The responder accepts AW and W independently, as required by AXI4-Lite.
  // A response is held until READY, so the example also exercises response
  // backpressure and payload stability.
  assign axi.awready = axi.areset_n && !aw_pending_q && !axi.bvalid;
  assign axi.wready  = axi.areset_n && !w_pending_q  && !axi.bvalid;
  assign axi.arready = axi.areset_n && !axi.rvalid;

  always_ff @(posedge axi.aclk or negedge axi.areset_n) begin
    if (!axi.areset_n) begin
      awaddr_q    <= '0;
      wdata_q     <= '0;
      wstrb_q     <= '0;
      aw_pending_q <= 1'b0;
      w_pending_q  <= 1'b0;
      axi.bvalid  <= 1'b0;
      axi.bresp   <= RESP_OKAY;
      axi.rvalid  <= 1'b0;
      axi.rdata   <= '0;
      axi.rresp   <= RESP_OKAY;
      for (i = 0; i < DEPTH; i = i + 1)
        mem[i] <= '0;
    end else begin
      if (axi.awvalid && axi.awready) begin
        awaddr_q     <= axi.awaddr;
        aw_pending_q <= 1'b1;
      end
      if (axi.wvalid && axi.wready) begin
        wdata_q      <= axi.wdata;
        wstrb_q      <= axi.wstrb;
        w_pending_q  <= 1'b1;
      end

      if (aw_pending_q && w_pending_q && !axi.bvalid) begin
        if (mapped(awaddr_q)) begin
          for (i = 0; i < STRB_W; i = i + 1)
            if (wstrb_q[i])
              mem[awaddr_q / STRB_W][8*i +: 8] <= wdata_q[8*i +: 8];
          axi.bresp <= RESP_OKAY;
        end else begin
          axi.bresp <= RESP_DECERR;
        end
        axi.bvalid    <= 1'b1;
        aw_pending_q  <= 1'b0;
        w_pending_q   <= 1'b0;
      end

      if (axi.bvalid && axi.bready)
        axi.bvalid <= 1'b0;

      if (axi.arvalid && axi.arready) begin
        if (mapped(axi.araddr)) begin
          axi.rdata <= mem[axi.araddr / STRB_W];
          axi.rresp <= RESP_OKAY;
        end else begin
          axi.rdata <= '0;
          axi.rresp <= RESP_DECERR;
        end
        axi.rvalid <= 1'b1;
      end
      if (axi.rvalid && axi.rready)
        axi.rvalid <= 1'b0;
    end
  end
endmodule
