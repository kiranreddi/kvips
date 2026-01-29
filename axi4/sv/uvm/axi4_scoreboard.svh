//------------------------------------------------------------------------------
// AXI4 Scoreboard
//------------------------------------------------------------------------------
// Validates read data against expected contents derived from observed writes.
//
// Default behavior:
// - Tracks a simple byte-addressed memory image from completed write transactions
// - On completed read transactions, reconstructs expected data and compares beat-wise
//
// Runtime switches (plusargs):
// - Disable scoreboard: +KVIPS_AXI4_SB_OFF
// - Warn on reads of unwritten bytes: +KVIPS_AXI4_SB_WARN_UNINIT
//------------------------------------------------------------------------------

`ifndef KVIPS_AXI4_SCOREBOARD_SVH
`define KVIPS_AXI4_SCOREBOARD_SVH

class axi4_scoreboard #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends uvm_subscriber #(axi4_item#(ADDR_W, DATA_W, ID_W, USER_W));

  localparam int STRB_W = DATA_W/8;

  bit enable = 1'b1;
  bit warn_uninit = 1'b0;

  // Byte-addressed expected memory image.
  byte unsigned exp_mem[longint unsigned];
  bit           exp_mem_valid[longint unsigned];

  `uvm_component_param_utils(axi4_scoreboard#(ADDR_W, DATA_W, ID_W, USER_W))

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if ($test$plusargs("KVIPS_AXI4_SB_OFF")) enable = 1'b0;
    if ($test$plusargs("KVIPS_AXI4_SB_WARN_UNINIT")) warn_uninit = 1'b1;
  endfunction

  function automatic longint unsigned to_addr_u(logic [ADDR_W-1:0] a);
    return longint'(a);
  endfunction

  function automatic void apply_write_beat(
    longint unsigned base_addr,
    logic [DATA_W-1:0] data,
    logic [STRB_W-1:0] strb
  );
    longint unsigned aligned;
    aligned = (base_addr / STRB_W) * STRB_W;
    for (int unsigned b = 0; b < STRB_W; b++) begin
      if (strb[b]) begin
        exp_mem[aligned + b] = data[8*b +: 8];
        exp_mem_valid[aligned + b] = 1'b1;
      end
    end
  endfunction

  function automatic logic [DATA_W-1:0] build_expected_beat(longint unsigned base_addr, output bit any_uninit);
    logic [DATA_W-1:0] exp;
    longint unsigned aligned;
    any_uninit = 1'b0;
    exp = '0;
    aligned = (base_addr / STRB_W) * STRB_W;
    for (int unsigned b = 0; b < STRB_W; b++) begin
      if (exp_mem_valid.exists(aligned + b) && exp_mem_valid[aligned + b]) begin
        exp[8*b +: 8] = exp_mem[aligned + b];
      end else begin
        // Matches default slave mem init (0). Optionally warn for visibility.
        any_uninit = 1'b1;
        exp[8*b +: 8] = 8'h00;
      end
    end
    return exp;
  endfunction

  virtual function void write(axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) t);
    if (!enable) return;
    if (t == null) return;

    t.allocate_payload();

    if (t.is_write) begin
      int unsigned beats;
      beats = t.num_beats();

      // Do not model memory updates for transactions that did not complete
      // successfully (error response), or for failed exclusive writes (LOCK=1
      // but BRESP != EXOKAY in our slave model).
      if ((t.bresp == AXI4_RESP_SLVERR) || (t.bresp == AXI4_RESP_DECERR)) return;
      if (t.lock && (t.bresp != AXI4_RESP_EXOKAY)) return;

      for (int unsigned i = 0; i < beats; i++) begin
        longint unsigned base = axi4_beat_addr(to_addr_u(t.addr), int'(t.size), int'(t.len), t.burst, i);
        logic [STRB_W-1:0] strb = (t.strb.size() == beats) ? t.strb[i] : '1;
        apply_write_beat(base, t.data[i], strb);
      end
    end else begin
      int unsigned beats = t.num_beats();
      for (int unsigned i = 0; i < beats; i++) begin
        bit any_uninit;
        longint unsigned base;
        logic [DATA_W-1:0] exp;

        if ((t.rresp.size() == beats) && ((t.rresp[i] == AXI4_RESP_SLVERR) || (t.rresp[i] == AXI4_RESP_DECERR))) begin
          continue;
        end

        base = axi4_beat_addr(to_addr_u(t.addr), int'(t.size), int'(t.len), t.burst, i);
        exp  = build_expected_beat(base, any_uninit);
        if (any_uninit && warn_uninit) begin
          `uvm_warning(get_type_name(), $sformatf("Read touches unwritten bytes at addr=0x%0h (treated as 0)", base))
        end
        if (t.data[i] !== exp) begin
          `uvm_error(get_type_name(),
            $sformatf("READ MISMATCH addr=0x%0h beat=%0d exp=0x%0h got=0x%0h", base, i, exp, t.data[i]))
        end
      end
    end
  endfunction

endclass

`endif // KVIPS_AXI4_SCOREBOARD_SVH
