`timescale 1ns/1ps

module axi4_ram_slave #(
  parameter int ADDR_W = 32,
  parameter int DATA_W = 64,
  parameter int ID_W   = 4,
  parameter int USER_W = 1,
  parameter int MEM_BYTES = 64*1024,
  parameter logic [ADDR_W-1:0] MEM_BASE = '0
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
  // A byte-addressed array makes the DUT behavior explicit for narrow
  // transfers and partial WSTRB updates.  The verification scoreboard uses
  // the same AMBA byte-lane convention.
  logic [7:0] mem [0:MEM_BYTES-1];

  logic [ID_W-1:0]   wr_id;
  logic [USER_W-1:0] wr_user;
  logic [ADDR_W-1:0] wr_start_addr;
  logic [ADDR_W-1:0] wr_addr;
  logic [7:0]        wr_len;
  logic [7:0]        wr_beat;
  logic [2:0]        wr_size;
  logic [1:0]        wr_burst;
  logic              wr_active;

  logic [ID_W-1:0]   rd_id;
  logic [USER_W-1:0] rd_user;
  logic [ADDR_W-1:0] rd_start_addr;
  logic [ADDR_W-1:0] rd_addr;
  logic [7:0]        rd_len;
  logic [7:0]        rd_beat;
  logic [2:0]        rd_size;
  logic [1:0]        rd_burst;
  logic              rd_active;

  function automatic [ADDR_W-1:0] beat_addr(
    input [ADDR_W-1:0] start_addr,
    input [2:0]        size,
    input [7:0]        len,
    input [1:0]        burst,
    input int unsigned beat
  );
    longint unsigned step;
    longint unsigned total;
    longint unsigned wrap_base;
    longint unsigned offset;
    longint unsigned start_u;
    begin
      step = longint'(1) << size;
      start_u = longint'(start_addr);
      case (burst)
        2'b00: beat_addr = start_addr; // FIXED
        2'b01: beat_addr = start_u + longint'(beat) * step; // INCR
        2'b10: begin // WRAP
          total = (longint'(len) + 1) * step;
          if (total == 0) beat_addr = start_addr;
          else begin
            wrap_base = (start_u / total) * total;
            offset = (start_u - wrap_base + longint'(beat) * step) % total;
            beat_addr = wrap_base + offset;
          end
        end
        default: beat_addr = start_addr;
      endcase
    end
  endfunction

  function automatic bit byte_in_range(input logic [ADDR_W-1:0] addr);
    longint unsigned a;
    begin
      a = longint'(addr);
      byte_in_range = (a >= longint'(MEM_BASE)) &&
                      ((a - longint'(MEM_BASE)) < longint'(MEM_BYTES));
    end
  endfunction

  function automatic int unsigned mem_index(input logic [ADDR_W-1:0] addr);
    mem_index = int'(longint'(addr) - longint'(MEM_BASE));
  endfunction

  always_ff @(posedge aclk or negedge areset_n) begin
    if (!areset_n) begin
      for (int m = 0; m < MEM_BYTES; m++) mem[m] <= 8'h00;
      awready   <= 1'b1;
      wready    <= 1'b0;
      bvalid    <= 1'b0;
      bresp     <= 2'b00;
      bid       <= '0;
      buser     <= '0;
      wr_active <= 1'b0;
      wr_beat   <= '0;

      arready   <= 1'b1;
      rvalid    <= 1'b0;
      rresp     <= 2'b00;
      rid       <= '0;
      ruser     <= '0;
      rdata     <= '0;
      rlast     <= 1'b0;
      rd_active <= 1'b0;
      rd_beat   <= '0;
    end else begin
      if (awready && awvalid) begin
        wr_active <= 1'b1;
        wr_id     <= awid;
        wr_user   <= awuser;
        wr_start_addr <= awaddr;
        wr_addr   <= awaddr;
        wr_len    <= awlen;
        wr_size   <= awsize;
        wr_burst  <= awburst;
        wr_beat   <= '0;
        awready   <= 1'b0;
        wready    <= 1'b1;
      end

      if (wready && wvalid) begin
        logic [ADDR_W-1:0] lane_base;
        bit beat_ok;
        lane_base = (wr_addr / WORD_BYTES) * WORD_BYTES;
        beat_ok = 1'b1;
        for (int b = 0; b < STRB_W; b++) begin
          logic [ADDR_W-1:0] byte_addr;
          byte_addr = lane_base + b;
          if (wstrb[b]) begin
            if (byte_in_range(byte_addr)) mem[mem_index(byte_addr)] <= wdata[8*b +: 8];
            else beat_ok = 1'b0;
          end
        end

        if (wlast || (wr_beat == wr_len)) begin
          wready    <= 1'b0;
          bvalid    <= 1'b1;
          bid       <= wr_id;
          buser     <= wr_user;
          bresp     <= beat_ok ? 2'b00 : 2'b11; // DECERR for an unmapped byte
          wr_active <= 1'b0;
        end else begin
          wr_beat <= wr_beat + 1;
          wr_addr <= beat_addr(wr_start_addr, wr_size, wr_len, wr_burst, wr_beat + 1);
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
        rd_start_addr <= araddr;
        rd_addr   <= araddr;
        rd_len    <= arlen;
        rd_size   <= arsize;
        rd_burst  <= arburst;
        rd_beat   <= '0;
        arready   <= 1'b0;
      end

      // Hold RVALID/RDATA while the master applies backpressure.  On a
      // handshake, retire the final beat or present exactly the next beat;
      // this avoids dropping RLAST when RREADY is already high.
      if (rd_active && (!rvalid || rready)) begin
        logic [ADDR_W-1:0] use_addr;
        logic [ADDR_W-1:0] lane_base;
        logic [DATA_W-1:0] read_value;
        bit beat_ok;
        int unsigned use_beat;

        if (rvalid && rlast) begin
          rd_active <= 1'b0;
          rvalid    <= 1'b0;
          arready   <= 1'b1;
        end else if (rvalid) begin
          // Insert a legal one-cycle bubble between beats.  Besides making
          // the simple DUT easier to inspect, this avoids a simulator race
          // between a clocking-block master and an always_ff response update.
          rd_beat <= rd_beat + 1;
          rd_addr <= beat_addr(rd_start_addr, rd_size, rd_len, rd_burst, rd_beat + 1);
          rvalid  <= 1'b0;
        end else begin
          use_beat = rd_beat;
          use_addr = rd_addr;
          lane_base = (use_addr / WORD_BYTES) * WORD_BYTES;
          beat_ok = 1'b1;
          read_value = '0;
          rid    <= rd_id;
          ruser  <= rd_user;
          rresp  <= 2'b00;
          for (int b = 0; b < STRB_W; b++) begin
            logic [ADDR_W-1:0] byte_addr;
            byte_addr = lane_base + b;
            if (byte_in_range(byte_addr)) read_value[8*b +: 8] = mem[mem_index(byte_addr)];
            else beat_ok = 1'b0;
          end
          rdata <= read_value;
          if (!beat_ok) rresp <= 2'b11; // DECERR for an unmapped read beat
          rlast  <= (use_beat == rd_len);
          rvalid <= 1'b1;
        end
      end
    end
  end
endmodule
