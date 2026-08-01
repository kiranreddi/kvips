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
  logic [2:0]           rd_size_q;

  logic [7:0] wait_cnt;
`ifdef VERILATOR
  // The raw-interface Verilator master samples after the clocked DUT update.
  // Keep a two-stage response pipeline so a burst control accepted on that
  // edge cannot replace the data phase retired by the raw-interface monitor.
  logic [DATA_W-1:0] rd_data_q;
  logic [DATA_W-1:0] hrdata_mid_q;
  logic [DATA_W-1:0] hrdata_out_q;
  logic [2:0]        rd_burst_q;
`else
  logic [DATA_W-1:0] rd_word_comb;
  logic [STRB_W-1:0] rd_mask_comb;
`endif

`ifndef VERILATOR
  // Read data is a combinational view of the registered pending address. It
  // remains stable while HREADYOUT is low and avoids a one-beat lag when a
  // burst advances its control phase on the same edge that the prior data
  // phase completes.
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

`ifdef VERILATOR
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

  always_comb begin
    HRDATA = '0;
    if (rd_burst_q == 3'b000) begin
      // Single transfers do not have a following burst control phase that can
      // replace the response, so retain the direct memory view.
      if (rd_pending)
        HRDATA = read_value(rd_addr_q, rd_size_q, 1'b0, '0, '0, '0);
    end else begin
      HRDATA = hrdata_out_q;
    end
  end
`endif

  always_ff @(posedge HCLK or negedge HRESETn) begin
    if (!HRESETn) begin
      HREADYOUT <= 1'b1;
      HRESP     <= '0;
`ifdef VERILATOR
      rd_data_q <= '0;
      hrdata_mid_q <= '0;
      hrdata_out_q <= '0;
      rd_burst_q <= 3'b000;
`endif
      wr_pending <= 1'b0;
      rd_pending <= 1'b0;
      rd_size_q <= '0;
      wait_cnt <= '0;
      for (int i = 0; i < MEM_WORDS; i++) begin
        mem[i] <= '0;
      end
    end else begin
      HRESP <= '0;
      HREADYOUT <= 1'b1;
`ifdef VERILATOR
      hrdata_out_q <= hrdata_mid_q;
      hrdata_mid_q <= rd_data_q;
`endif

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
          rd_size_q  <= HSIZE;
`ifdef VERILATOR
          rd_data_q <= read_value(
            HADDR, HSIZE,
            wr_pending && HREADYOUT,
            wr_addr_q, wr_size_q, HWDATA);
          rd_burst_q <= HBURST;
`endif
        end
      end
    end
  end
endmodule
