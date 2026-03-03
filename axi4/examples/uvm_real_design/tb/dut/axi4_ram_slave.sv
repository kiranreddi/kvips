`timescale 1ns/1ps

module axi4_ram_slave #(
  parameter int ADDR_W = 32,
  parameter int DATA_W = 64,
  parameter int ID_W   = 4,
  parameter int USER_W = 1,
  parameter int MEM_BYTES = 64*1024
) (
  input  logic                  aclk,
  input  logic                  areset_n,
  input  logic [ID_W-1:0]       awid,
  input  logic [ADDR_W-1:0]     awaddr,
  input  logic [7:0]            awlen,
  input  logic [2:0]            awsize,
  input  logic [1:0]            awburst,
  input  logic [USER_W-1:0]     awuser,
  input  logic                  awvalid,
  output logic                  awready,
  input  logic [DATA_W-1:0]     wdata,
  input  logic [DATA_W/8-1:0]   wstrb,
  input  logic                  wlast,
  input  logic                  wvalid,
  output logic                  wready,
  output logic [ID_W-1:0]       bid,
  output logic [1:0]            bresp,
  output logic [USER_W-1:0]     buser,
  output logic                  bvalid,
  input  logic                  bready,
  input  logic [ID_W-1:0]       arid,
  input  logic [ADDR_W-1:0]     araddr,
  input  logic [7:0]            arlen,
  input  logic [2:0]            arsize,
  input  logic [1:0]            arburst,
  input  logic [USER_W-1:0]     aruser,
  input  logic                  arvalid,
  output logic                  arready,
  output logic [ID_W-1:0]       rid,
  output logic [DATA_W-1:0]     rdata,
  output logic [1:0]            rresp,
  output logic                  rlast,
  output logic [USER_W-1:0]     ruser,
  output logic                  rvalid,
  input  logic                  rready
);
  localparam int STRB_W = DATA_W/8;
  localparam int WORD_BYTES = (DATA_W/8);
  localparam int ADDR_LSB = (WORD_BYTES <= 1) ? 0 : $clog2(WORD_BYTES);
  localparam int MEM_WORDS = MEM_BYTES / WORD_BYTES;

  logic [DATA_W-1:0] mem [0:MEM_WORDS-1];

  logic [ID_W-1:0]   wr_id;
  logic [USER_W-1:0] wr_user;
  logic [ADDR_W-1:0] wr_addr;
  logic [7:0]        wr_len;
  logic [7:0]        wr_beat;
  logic [2:0]        wr_size;
  logic [1:0]        wr_burst;
  logic              wr_active;

  logic [ID_W-1:0]   rd_id;
  logic [USER_W-1:0] rd_user;
  logic [ADDR_W-1:0] rd_addr;
  logic [7:0]        rd_len;
  logic [7:0]        rd_beat;
  logic [2:0]        rd_size;
  logic [1:0]        rd_burst;
  logic              rd_active;

  function automatic [ADDR_W-1:0] next_addr(
    input [ADDR_W-1:0] addr,
    input [2:0] size,
    input [1:0] burst
  );
    automatic logic [ADDR_W-1:0] step;
    begin
      step = (1 << size);
      if (burst == 2'b00) next_addr = addr; // FIXED
      else next_addr = addr + step;         // INCR/WRAP treated as INCR
    end
  endfunction

  function automatic int unsigned word_index(input logic [ADDR_W-1:0] addr);
    automatic int unsigned idx;
    begin
      idx = addr[ADDR_LSB +: $clog2(MEM_WORDS)];
      word_index = idx;
    end
  endfunction

  always_ff @(posedge aclk or negedge areset_n) begin
    if (!areset_n) begin
      awready   <= 1'b1;
      wready    <= 1'b0;
      bvalid    <= 1'b0;
      bresp     <= 2'b00;
      wr_active <= 1'b0;
      wr_beat   <= '0;

      arready   <= 1'b1;
      rvalid    <= 1'b0;
      rresp     <= 2'b00;
      rlast     <= 1'b0;
      rd_active <= 1'b0;
      rd_beat   <= '0;
    end else begin
      if (awready && awvalid) begin
        wr_active <= 1'b1;
        wr_id     <= awid;
        wr_user   <= awuser;
        wr_addr   <= awaddr;
        wr_len    <= awlen;
        wr_size   <= awsize;
        wr_burst  <= awburst;
        wr_beat   <= '0;
        awready   <= 1'b0;
        wready    <= 1'b1;
      end

      if (wready && wvalid) begin
        int unsigned idx;
        idx = word_index(wr_addr);
        if (idx < MEM_WORDS) begin
          for (int b = 0; b < STRB_W; b++) begin
            if (wstrb[b]) mem[idx][8*b +: 8] <= wdata[8*b +: 8];
          end
        end

        if (wlast || (wr_beat == wr_len)) begin
          wready    <= 1'b0;
          bvalid    <= 1'b1;
          bid       <= wr_id;
          buser     <= wr_user;
          bresp     <= 2'b00;
          wr_active <= 1'b0;
        end else begin
          wr_beat <= wr_beat + 1;
          wr_addr <= next_addr(wr_addr, wr_size, wr_burst);
        end
      end

      if (bvalid && bready) begin
        bvalid  <= 1'b0;
        awready <= 1'b1;
      end

      if (arready && arvalid) begin
        rd_active <= 1'b1;
        rd_id     <= arid;
        rd_user   <= aruser;
        rd_addr   <= araddr;
        rd_len    <= arlen;
        rd_size   <= arsize;
        rd_burst  <= arburst;
        rd_beat   <= '0;
        arready   <= 1'b0;
      end

      if (rd_active && (!rvalid || (rvalid && rready))) begin
        int unsigned ridx;
        ridx = word_index(rd_addr);
        rid    <= rd_id;
        ruser  <= rd_user;
        rresp  <= 2'b00;
        rdata  <= (ridx < MEM_WORDS) ? mem[ridx] : '0;
        rlast  <= (rd_beat == rd_len);
        rvalid <= 1'b1;

        if (rd_beat == rd_len) begin
          if (rready) begin
            rd_active <= 1'b0;
            rvalid    <= 1'b0;
            arready   <= 1'b1;
          end
        end else if (rready) begin
          rd_beat <= rd_beat + 1;
          rd_addr <= next_addr(rd_addr, rd_size, rd_burst);
        end
      end
    end
  end
endmodule
