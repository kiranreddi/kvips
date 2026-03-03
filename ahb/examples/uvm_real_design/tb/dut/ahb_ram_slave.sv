`timescale 1ns/1ps

module ahb_ram_slave #(
  parameter int ADDR_W = 16,
  parameter int DATA_W = 32,
  parameter int HRESP_W = 2,
  parameter int MEM_BYTES = 64*1024,
  parameter int WAIT_STATES = 0
) (
  input  logic                 HCLK,
  input  logic                 HRESETn,
  input  logic [ADDR_W-1:0]    HADDR,
  input  logic [1:0]           HTRANS,
  input  logic                 HWRITE,
  input  logic [2:0]           HSIZE,
  input  logic [2:0]           HBURST,
  input  logic [3:0]           HPROT,
  input  logic                 HSEL,
  input  logic [DATA_W-1:0]    HWDATA,
  input  logic                 HREADY,
  output logic                 HREADYOUT,
  output logic [HRESP_W-1:0]   HRESP,
  output logic [DATA_W-1:0]    HRDATA
);
  localparam int STRB_W = DATA_W/8;
  localparam int WORD_BYTES = DATA_W/8;
  localparam int ADDR_LSB = (WORD_BYTES <= 1) ? 0 : $clog2(WORD_BYTES);
  localparam int MEM_WORDS = MEM_BYTES/WORD_BYTES;

  logic [DATA_W-1:0] mem [0:MEM_WORDS-1];

  logic                 wr_pending;
  logic [ADDR_W-1:0]    wr_addr_q;
  logic [2:0]           wr_size_q;

  logic                 rd_pending;
  logic [ADDR_W-1:0]    rd_addr_q;

  logic [7:0] wait_cnt;

  function automatic int unsigned word_index(input logic [ADDR_W-1:0] addr);
    word_index = addr[ADDR_LSB +: $clog2(MEM_WORDS)];
  endfunction

  function automatic [STRB_W-1:0] size_mask(input logic [2:0] size, input logic [ADDR_LSB-1:0] offs);
    automatic logic [STRB_W-1:0] m;
    begin
      m = '0;
      case (size)
        3'b000: m[offs +: 1] = 1'b1;
        3'b001: m[offs +: 2] = 2'b11;
        default: m = '1;
      endcase
      size_mask = m;
    end
  endfunction

  always_ff @(posedge HCLK or negedge HRESETn) begin
    if (!HRESETn) begin
      HREADYOUT <= 1'b1;
      HRESP     <= '0;
      HRDATA    <= '0;
      wr_pending <= 1'b0;
      rd_pending <= 1'b0;
      wait_cnt <= '0;
    end else begin
      HRESP <= '0;
      HREADYOUT <= 1'b1;

      if (wait_cnt != 0) begin
        wait_cnt <= wait_cnt - 1'b1;
        HREADYOUT <= 1'b0;
      end

      if (wr_pending && HREADYOUT) begin
        int unsigned idx;
        logic [STRB_W-1:0] m;
        idx = word_index(wr_addr_q);
        m = size_mask(wr_size_q, wr_addr_q[ADDR_LSB-1:0]);
        if (idx < MEM_WORDS) begin
          for (int b = 0; b < STRB_W; b++) begin
            if (m[b]) mem[idx][8*b +: 8] <= HWDATA[8*b +: 8];
          end
        end
        wr_pending <= 1'b0;
      end

      if (rd_pending && HREADYOUT) begin
        int unsigned ridx;
        ridx = word_index(rd_addr_q);
        HRDATA <= (ridx < MEM_WORDS) ? mem[ridx] : '0;
        rd_pending <= 1'b0;
      end

      if (HSEL && HREADY && HTRANS[1]) begin
        if (WAIT_STATES != 0)
          wait_cnt <= WAIT_STATES;
        if (HWRITE) begin
          wr_pending <= 1'b1;
          wr_addr_q  <= HADDR;
          wr_size_q  <= HSIZE;
        end else begin
          rd_pending <= 1'b1;
          rd_addr_q  <= HADDR;
        end
      end
    end
  end
endmodule
