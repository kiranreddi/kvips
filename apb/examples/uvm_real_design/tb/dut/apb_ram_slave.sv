`timescale 1ns/1ps

module apb_ram_slave #(
  parameter int ADDR_W = 16,
  parameter int DATA_W = 32,
  parameter int NSEL   = 1,
  parameter int MEM_BYTES = 64*1024,
  parameter int WAIT_STATES = 0
) (
  input  logic               PCLK,
  input  logic               PRESETn,
  input  logic [ADDR_W-1:0]  PADDR,
  input  logic [NSEL-1:0]    PSEL,
  input  logic               PENABLE,
  input  logic               PWRITE,
  input  logic [DATA_W-1:0]  PWDATA,
  output logic [DATA_W-1:0]  PRDATA,
  output logic               PREADY,
  output logic               PSLVERR,
  input  logic [2:0]         PPROT,
  input  logic [DATA_W/8-1:0] PSTRB
);
  localparam int STRB_W = DATA_W/8;
  localparam int WORD_BYTES = DATA_W/8;
  localparam int ADDR_LSB = (WORD_BYTES <= 1) ? 0 : $clog2(WORD_BYTES);
  localparam int MEM_WORDS = MEM_BYTES/WORD_BYTES;

  logic [DATA_W-1:0] mem [0:MEM_WORDS-1];
  logic [$clog2(WAIT_STATES+1)-1:0] wait_cnt;
  logic access_req;

  function automatic int unsigned word_index(input logic [ADDR_W-1:0] addr);
    word_index = addr[ADDR_LSB +: $clog2(MEM_WORDS)];
  endfunction

  always_ff @(posedge PCLK or negedge PRESETn) begin
    if (!PRESETn) begin
      PREADY  <= 1'b0;
      PSLVERR <= 1'b0;
      PRDATA  <= '0;
      wait_cnt <= '0;
      access_req <= 1'b0;
    end else begin
      PREADY  <= 1'b0;
      PSLVERR <= 1'b0;

      if (PSEL[0] && PENABLE) begin
        if (!access_req) begin
          access_req <= 1'b1;
          wait_cnt <= WAIT_STATES;
        end

        if (wait_cnt != 0) begin
          wait_cnt <= wait_cnt - 1'b1;
        end else begin
          int unsigned idx;
          idx = word_index(PADDR);
          PREADY <= 1'b1;
          if (idx >= MEM_WORDS) begin
            PSLVERR <= 1'b1;
            PRDATA <= '0;
          end else if (PWRITE) begin
            for (int b = 0; b < STRB_W; b++) begin
              if (PSTRB[b]) mem[idx][8*b +: 8] <= PWDATA[8*b +: 8];
            end
          end else begin
            PRDATA <= mem[idx];
          end
          access_req <= 1'b0;
        end
      end else begin
        access_req <= 1'b0;
      end
    end
  end
endmodule
