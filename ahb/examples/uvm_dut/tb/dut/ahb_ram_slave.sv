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
`ifdef VERILATOR
  logic [DATA_W-1:0]    wr_data_q;
  logic [2:0]           wr_burst_q;
`endif

  logic                 rd_pending;
  logic [ADDR_W-1:0]    rd_addr_q;
  logic [2:0]           rd_size_q;

  logic [7:0] wait_cnt;
`ifndef VERILATOR
  logic [DATA_W-1:0] rd_word_comb;
  logic [STRB_W-1:0] rd_mask_comb;
`endif

  function automatic int unsigned word_index(input logic [ADDR_W-1:0] addr);
    word_index = addr[ADDR_LSB +: $clog2(MEM_WORDS)];
  endfunction

  function automatic logic [DATA_W-1:0] read_value(
    input logic [ADDR_W-1:0] addr,
    input logic [2:0]        size,
    input bit                forward_valid,
    input logic [ADDR_W-1:0] forward_addr,
    input logic [2:0]        forward_size,
    input logic [DATA_W-1:0] forward_data
  );
    logic [DATA_W-1:0] value;
    logic [STRB_W-1:0] mask;
    logic [STRB_W-1:0] forward_mask;
    int unsigned idx;
    int unsigned forward_idx;

    value = '0;
    idx = word_index(addr);
    if (idx < MEM_WORDS) begin
      mask = size_mask(size, addr[ADDR_LSB-1:0]);
      for (int b = 0; b < STRB_W; b++) begin
        if (mask[b]) value[8*b +: 8] = mem[idx][8*b +: 8];
      end
    end

    // A write data phase can retire on the same edge as a newly accepted
    // read control. Forward those bytes so read-after-write remains ordered
    // even though the memory array itself updates with a nonblocking write.
    forward_idx = word_index(forward_addr);
    if (forward_valid && (idx == forward_idx)) begin
      forward_mask = size_mask(forward_size, forward_addr[ADDR_LSB-1:0]);
      for (int b = 0; b < STRB_W; b++) begin
        if (forward_mask[b]) value[8*b +: 8] = forward_data[8*b +: 8];
      end
    end
    return value;
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

`ifndef VERILATOR
  // Clocking-block simulators sample a combinational read response while the
  // registered pending address remains in the data phase.  Keep this path
  // separate from the raw-interface registered response used by Verilator.
  always_comb begin
    HRDATA = '0;
    rd_word_comb = '0;
    rd_mask_comb = '0;
    if (rd_pending && (word_index(rd_addr_q) < MEM_WORDS)) begin
      rd_word_comb = mem[word_index(rd_addr_q)];
      rd_mask_comb = size_mask(rd_size_q, rd_addr_q[ADDR_LSB-1:0]);
      for (int b = 0; b < STRB_W; b++) begin
        if (rd_mask_comb[b]) HRDATA[8*b +: 8] = rd_word_comb[8*b +: 8];
      end
    end
  end
`endif

  always_ff @(posedge HCLK or negedge HRESETn) begin
    if (!HRESETn) begin
      HREADYOUT <= 1'b1;
      HRESP     <= '0;
`ifdef VERILATOR
      HRDATA    <= '0;
`endif
      wr_pending <= 1'b0;
`ifdef VERILATOR
      wr_data_q <= '0;
      wr_burst_q <= 3'b000;
`endif
      rd_pending <= 1'b0;
      rd_size_q <= '0;
      wait_cnt <= '0;
      for (int i = 0; i < MEM_WORDS; i++) begin
        mem[i] <= '0;
      end
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
            if (m[b]) begin
`ifdef VERILATOR
              // The raw master presents a single-transfer write datum with
              // the control phase. Capture it before the next item's datum
              // can replace HWDATA; burst data remains phase-aligned below.
              if (wr_burst_q == 3'b000)
                mem[idx][8*b +: 8] <= wr_data_q[8*b +: 8];
              else
                mem[idx][8*b +: 8] <= HWDATA[8*b +: 8];
`else
              mem[idx][8*b +: 8] <= HWDATA[8*b +: 8];
`endif
            end
          end
        end
        wr_pending <= 1'b0;
      end

      if (rd_pending && HREADYOUT) begin
        rd_pending <= 1'b0;
      end

      // A transfer is accepted on the rising edge when the incoming global
      // HREADY is high. WAIT_STATES affects the ready value produced for the
      // following cycle; it must not suppress a legally presented control
      // phase while the previous ready value was high.
      if (HSEL && HREADY && HTRANS[1]) begin
        if (WAIT_STATES != 0)
          wait_cnt <= WAIT_STATES;
        if (HWRITE) begin
          wr_pending <= 1'b1;
          wr_addr_q  <= HADDR;
          wr_size_q  <= HSIZE;
`ifdef VERILATOR
          wr_data_q  <= HWDATA;
          wr_burst_q <= HBURST;
`endif
        end else begin
          rd_pending <= 1'b1;
          rd_addr_q  <= HADDR;
          rd_size_q  <= HSIZE;
`ifdef VERILATOR
          HRDATA <= read_value(
            HADDR, HSIZE,
            wr_pending && HREADYOUT,
            wr_addr_q, wr_size_q, HWDATA);
`endif
        end
      end
    end
  end
endmodule
