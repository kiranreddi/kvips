//------------------------------------------------------------------------------
// AXI4 Transaction
//------------------------------------------------------------------------------
// Sequence item representing a single AXI4 read or write burst.
//------------------------------------------------------------------------------

`ifndef KVIPS_AXI4_TRANSACTION_SVH
`define KVIPS_AXI4_TRANSACTION_SVH

class axi4_item #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends uvm_sequence_item;

  localparam int STRB_W = DATA_W/8;

  rand bit                 is_write;
  // AXI4: AxLOCK is 1-bit. When set, the transfer is an exclusive access.
  rand bit                 lock;
  rand logic [ID_W-1:0]     id;
  rand logic [ADDR_W-1:0]   addr;
  rand logic [7:0]          len;     // AXI: beats-1
  rand logic [2:0]          size;    // AXI: bytes/beat = 2**size
  rand axi4_burst_e         burst;

  // AXI4 sideband attributes (address phase)
  rand logic [3:0]          cache;
  rand logic [2:0]          prot;
  rand logic [3:0]          qos;
  rand logic [3:0]          region;

  // Per-transaction timing controls (optional overrides; -1 means "use cfg randomization").
  int aw_delay_cycles = -1;
  int ar_delay_cycles = -1;
  int w_beat_gap_cycles = -1;

  rand logic [DATA_W-1:0]   data[];  // one entry per beat
  rand logic [STRB_W-1:0]   strb[];  // one entry per beat (writes)

  axi4_resp_e               bresp;
  axi4_resp_e               rresp[];
  // Set by a pipelined master when reset flushes an in-flight request.  This
  // is a UVM-side completion marker; AXI has no response encoding for reset.
  bit                        reset_aborted = 1'b0;

  rand logic [USER_W-1:0]   user;

  // Constraint escape hatches (for negative testing / corner stimulus)
  rand bit allow_4kb_cross;
  rand bit allow_wrap_misalign;

  // AXI4 burst legality (AMBA4):
  // - INCR supports 1..256 beats (LEN 0..255)
  // - FIXED/WRAP support 1..16 beats (LEN 0..15)
  // - WRAP length must be 2/4/8/16 beats (LEN 1/3/7/15)
  constraint c_len_axi4 {
    if (burst == AXI4_BURST_INCR) len inside {[0:255]};
    else                         len inside {[0:15]};
    if (burst == AXI4_BURST_WRAP) len inside {1,3,7,15};
  }
  constraint c_burst_default { burst == AXI4_BURST_INCR; }
  constraint c_lock_default { lock == 1'b0; }
  constraint c_size_legal { (1<<size) <= STRB_W; }
  constraint c_sideband_defaults {
    // Default all sideband attributes to 0, but allow sequences/tests to
    // override (e.g. for functional coverage closure).
    soft cache  == '0;
    soft prot   == '0;
    soft qos    == '0;
    soft region == '0;
  }
  constraint c_allow_defaults {
    allow_4kb_cross     == 1'b0;
    allow_wrap_misalign == 1'b0;
  }

  // Prevent generating bursts that cross a 4KB boundary (AMBA AXI4 rule).
  // FIXED does not increment address and is exempt.
  constraint c_no_4kb_cross {
    if (!allow_4kb_cross) {
      // AXI4 also caps the total transaction size at 4KB.  Keep this
      // separate from address-crossing so FIXED bursts are not exempt from
      // the size limit merely because their address does not advance.
      axi4_total_bytes(int'(size), int'(len)) <= 4096;
      if (burst != AXI4_BURST_FIXED) !axi4_crosses_4kb({1'b0, addr}, int'(size), int'(len));
    }
  }

  // Enforce WRAP start-address alignment to the wrap container.
  constraint c_wrap_align {
    if (!allow_wrap_misalign && (burst == AXI4_BURST_WRAP)) axi4_wrap_addr_aligned({1'b0, addr}, int'(size), int'(len));
  }

  function new(string name = "axi4_item");
    super.new(name);
    lock = 1'b0;
    cache  = '0;
    prot   = '0;
    qos    = '0;
    region = '0;
    aw_delay_cycles = -1;
    ar_delay_cycles = -1;
    w_beat_gap_cycles = -1;
    allow_4kb_cross     = 1'b0;
    allow_wrap_misalign = 1'b0;
  endfunction

  function automatic int unsigned num_beats();
    return int'(len) + 1;
  endfunction

  function automatic void allocate_payload();
    int unsigned beats = num_beats();
    if (data.size() != beats) data = new[beats];
    if (rresp.size() != beats) rresp = new[beats];
    if (is_write) begin
      if (strb.size() != beats) strb = new[beats];
    end else begin
      strb = new[0];
    end
  endfunction

  function void post_randomize();
    allocate_payload();
  endfunction

`ifdef VERILATOR
  /* verilator lint_off WIDTHEXPAND */
  /* verilator lint_off WIDTHTRUNC */
`endif
  `uvm_object_param_utils_begin(axi4_item#(ADDR_W, DATA_W, ID_W, USER_W))
    `uvm_field_int(is_write, UVM_DEFAULT)
    `uvm_field_int(lock,     UVM_DEFAULT)
    `uvm_field_int(id,       UVM_DEFAULT)
    `uvm_field_int(addr,     UVM_DEFAULT)
    `uvm_field_int(len,      UVM_DEFAULT)
    `uvm_field_int(size,     UVM_DEFAULT)
    `uvm_field_enum(axi4_burst_e, burst, UVM_DEFAULT)
    `uvm_field_int(cache,    UVM_DEFAULT)
    `uvm_field_int(prot,     UVM_DEFAULT)
    `uvm_field_int(qos,      UVM_DEFAULT)
    `uvm_field_int(region,   UVM_DEFAULT)
    `uvm_field_int(aw_delay_cycles, UVM_DEFAULT)
    `uvm_field_int(ar_delay_cycles, UVM_DEFAULT)
    `uvm_field_int(w_beat_gap_cycles, UVM_DEFAULT)
    `uvm_field_array_int(data, UVM_DEFAULT)
    `uvm_field_array_int(strb, UVM_DEFAULT)
    `uvm_field_enum(axi4_resp_e, bresp, UVM_DEFAULT)
    `uvm_field_array_enum(axi4_resp_e, rresp, UVM_DEFAULT)
    `uvm_field_int(reset_aborted, UVM_DEFAULT)
    `uvm_field_int(user, UVM_DEFAULT)
    `uvm_field_int(allow_4kb_cross, UVM_DEFAULT)
    `uvm_field_int(allow_wrap_misalign, UVM_DEFAULT)
  `uvm_object_utils_end
`ifdef VERILATOR
  /* verilator lint_on WIDTHTRUNC */
  /* verilator lint_on WIDTHEXPAND */
`endif

endclass

// Public phase-level helpers.  They adapt to the reusable transaction item
// instead of exposing driver-private implementation state.
class axi4_addr_phase_item #(
  int ADDR_W = 32, int DATA_W = 64, int ID_W = 4, int USER_W = 1
) extends uvm_sequence_item;
  rand bit                is_write;
  rand logic [ID_W-1:0]   id;
  rand logic [ADDR_W-1:0] addr;
  rand logic [7:0]        len;
  rand logic [2:0]        size;
  rand axi4_burst_e       burst;
  rand bit                lock;
  rand logic [3:0]        cache;
  rand logic [2:0]        prot;
  rand logic [3:0]        qos;
  rand logic [3:0]        region;
  rand logic [USER_W-1:0] user;
  `uvm_object_param_utils(axi4_addr_phase_item#(ADDR_W, DATA_W, ID_W, USER_W))
  function new(string name = "axi4_addr_phase_item"); super.new(name); endfunction
  function void apply_to(axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) txn);
    txn.is_write = is_write; txn.id = id; txn.addr = addr; txn.len = len;
    txn.size = size; txn.burst = burst; txn.lock = lock; txn.cache = cache;
    txn.prot = prot; txn.qos = qos; txn.region = region; txn.user = user;
    txn.allocate_payload();
  endfunction
endclass

class axi4_wdata_beat_item #(
  int ADDR_W = 32, int DATA_W = 64, int ID_W = 4, int USER_W = 1
) extends uvm_sequence_item;
  localparam int STRB_W = DATA_W/8;
  rand int unsigned          beat_index;
  rand logic [DATA_W-1:0]    data;
  rand logic [STRB_W-1:0]    strb;
  `uvm_object_param_utils(axi4_wdata_beat_item#(ADDR_W, DATA_W, ID_W, USER_W))
  function new(string name = "axi4_wdata_beat_item"); super.new(name); strb = '1; endfunction
  function void apply_to(axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) txn);
    txn.allocate_payload();
    if (!txn.is_write || (beat_index >= txn.num_beats())) begin
      `uvm_error("AXI4_PHASE", "Invalid write-data beat application")
      return;
    end
    txn.data[beat_index] = data;
    txn.strb[beat_index] = strb;
  endfunction
endclass

class axi4_rdata_beat_item #(
  int ADDR_W = 32, int DATA_W = 64, int ID_W = 4, int USER_W = 1
) extends uvm_sequence_item;
  rand int unsigned          beat_index;
  rand logic [DATA_W-1:0]    data;
  rand axi4_resp_e           resp;
  rand bit                   last;
  `uvm_object_param_utils(axi4_rdata_beat_item#(ADDR_W, DATA_W, ID_W, USER_W))
  function new(string name = "axi4_rdata_beat_item"); super.new(name); resp = AXI4_RESP_OKAY; endfunction
  function void apply_to(axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) txn);
    txn.allocate_payload();
    if (txn.is_write || (beat_index >= txn.num_beats())) begin
      `uvm_error("AXI4_PHASE", "Invalid read-data beat application")
      return;
    end
    txn.data[beat_index] = data;
    txn.rresp[beat_index] = resp;
  endfunction
endclass

class axi4_resp_phase_item #(
  int ADDR_W = 32, int DATA_W = 64, int ID_W = 4, int USER_W = 1
) extends uvm_sequence_item;
  rand bit                is_write;
  rand logic [ID_W-1:0]   id;
  rand axi4_resp_e        resp;
  rand logic [USER_W-1:0] user;
  rand bit                last;
  `uvm_object_param_utils(axi4_resp_phase_item#(ADDR_W, DATA_W, ID_W, USER_W))
  function new(string name = "axi4_resp_phase_item"); super.new(name); resp = AXI4_RESP_OKAY; last = 1'b1; endfunction
  function void apply_to(axi4_item#(ADDR_W, DATA_W, ID_W, USER_W) txn, int unsigned beat_index = 0);
    txn.user = user;
    if (is_write) txn.bresp = resp;
    else begin
      txn.allocate_payload();
      if (beat_index >= txn.num_beats()) `uvm_error("AXI4_PHASE", "Invalid read-response beat application")
      else txn.rresp[beat_index] = resp;
    end
  endfunction
endclass

`endif // KVIPS_AXI4_TRANSACTION_SVH
