`timescale 1ns/1ps

// Small synthesizable APB4 slave used by the DUT integration example.
// The byte-addressed array makes PSTRB behavior observable at the pins.
module apb_ram_slave #(
  parameter int ADDR_W      = 16,
  parameter int DATA_W      = 32,
  parameter int NSEL        = 1,
  parameter int MEM_BASE    = 0,
  parameter int MEM_BYTES   = 4096,
  parameter int WAIT_STATES = 2
) (
  input  logic                PCLK,
  input  logic                PRESETn,
  input  logic [ADDR_W-1:0]   PADDR,
  input  logic [NSEL-1:0]     PSEL,
  input  logic                PENABLE,
  input  logic                PWRITE,
  input  logic [DATA_W-1:0]   PWDATA,
  output logic [DATA_W-1:0]   PRDATA,
  output logic                PREADY,
  output logic                PSLVERR,
  input  logic [2:0]          PPROT,
  input  logic [DATA_W/8-1:0] PSTRB
);
  localparam int STRB_W = DATA_W / 8;
  localparam int WAIT_W = (WAIT_STATES < 1) ? 1 : $clog2(WAIT_STATES + 1);

  logic [7:0] mem [0:MEM_BYTES-1];

  logic                  pending;
  logic [ADDR_W-1:0]     pending_addr;
  logic                  pending_write;
  logic [DATA_W-1:0]     pending_wdata;
  logic [STRB_W-1:0]     pending_strb;
  logic [2:0]            pending_prot;
  logic [WAIT_W-1:0]     wait_count;

  function automatic bit byte_in_range(input logic [ADDR_W-1:0] address);
    longint unsigned a_u;
    longint unsigned base_u;
    longint unsigned offset;
    begin
      a_u = longint'(address);
      base_u = longint'(MEM_BASE);
      if (a_u < base_u) return 1'b0;
      offset = a_u - base_u;
      return (offset < MEM_BYTES);
    end
  endfunction

  function automatic int unsigned mem_index(input logic [ADDR_W-1:0] address);
    longint unsigned a_u;
    begin
      a_u = longint'(address);
      mem_index = int'(a_u - longint'(MEM_BASE));
    end
  endfunction

  function automatic bit transfer_in_range(
    input logic [ADDR_W-1:0] address,
    input logic [STRB_W-1:0] strb
  );
    begin
      transfer_in_range = 1'b1;
      for (int unsigned b = 0; b < STRB_W; b++) begin
        if (strb[b] && !byte_in_range(address + b)) transfer_in_range = 1'b0;
      end
    end
  endfunction

  function automatic logic [DATA_W-1:0] read_bytes(
    input logic [ADDR_W-1:0] address
  );
    logic [DATA_W-1:0] value;
    begin
      value = '0;
      for (int unsigned b = 0; b < STRB_W; b++) begin
        if (byte_in_range(address + b)) value[8*b +: 8] = mem[mem_index(address + b)];
      end
      return value;
    end
  endfunction

  always_ff @(posedge PCLK or negedge PRESETn) begin
    if (!PRESETn) begin
      PREADY       <= 1'b0;
      PSLVERR      <= 1'b0;
      PRDATA       <= '0;
      pending      <= 1'b0;
      pending_addr <= '0;
      pending_write <= 1'b0;
      pending_wdata <= '0;
      pending_strb  <= '0;
      pending_prot  <= '0;
      wait_count    <= '0;
      for (int unsigned m = 0; m < MEM_BYTES; m++) mem[m] <= 8'h00;
    end else begin
      // Keep PREADY high outside a transfer. During ACCESS it is driven low
      // only for the configured wait cycles, then remains high through the
      // completion/idle boundary so clocking-block sampling cannot create a
      // false wait-state transition.
      PREADY  <= 1'b1;
      PSLVERR <= 1'b0;

      if ((|PSEL) && !PENABLE) begin
        // APB SETUP: capture all controls before ACCESS begins.
        PREADY        <= 1'b0;
        pending       <= 1'b1;
        pending_addr  <= PADDR;
        pending_write <= PWRITE;
        pending_wdata <= PWDATA;
        pending_strb  <= PSTRB;
        pending_prot  <= PPROT;
        wait_count    <= WAIT_STATES;
        PRDATA        <= '0;
      end else if ((|PSEL) && PENABLE) begin
        if (!pending) begin
          // The completion pulse may be observed one clock before the master
          // leaves ACCESS. Do not recapture that same transfer as a new one.
          wait_count <= '0;
          PRDATA     <= '0;
        end else if (wait_count != 0) begin
          PREADY     <= 1'b0;
          wait_count <= wait_count - 1'b1;
        end else begin
          PREADY <= 1'b1;
          if (!transfer_in_range(pending_addr, pending_strb)) begin
            PSLVERR <= 1'b1;
            PRDATA  <= '0;
          end else if (pending_write) begin
            for (int unsigned b = 0; b < STRB_W; b++) begin
              if (pending_strb[b]) begin
                mem[mem_index(pending_addr + b)] <= pending_wdata[8*b +: 8];
              end
            end
            PRDATA <= '0;
          end else begin
            PRDATA <= read_bytes(pending_addr);
          end
          pending <= 1'b0;
        end
      end else begin
        pending   <= 1'b0;
        wait_count <= '0;
        PRDATA    <= '0;
      end
    end
  end
endmodule
