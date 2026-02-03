//------------------------------------------------------------------------------
// APB Sequences
//------------------------------------------------------------------------------
`ifndef KVIPS_APB_SEQUENCES_SVH
`define KVIPS_APB_SEQUENCES_SVH

class apb_base_seq #(
  int ADDR_W = 32,
  int DATA_W = 32
) extends uvm_sequence #(apb_item#(ADDR_W, DATA_W));

  localparam string RID = "APB_SEQ";
  localparam int STRB_W = (DATA_W/8);

  apb_cfg#(ADDR_W, DATA_W, 1) cfg; // NSEL not required for item-level tasks

  function new(string name = "apb_base_seq");
    super.new(name);
  endfunction

  task automatic apb_write(input logic [ADDR_W-1:0] addr, input logic [DATA_W-1:0] data,
                           input logic [STRB_W-1:0] strb = '1, input logic [2:0] prot = 3'b000);
    apb_item#(ADDR_W, DATA_W) tr;
`ifdef VERILATOR
    /* verilator lint_off WIDTHEXPAND */
    /* verilator lint_off WIDTHTRUNC */
    /* verilator lint_off CASTCONST */
`endif
    `uvm_create(tr)
    tr.write = 1'b1;
    tr.addr  = addr;
    tr.wdata = data;
    tr.strb  = strb;
    tr.prot  = prot;
    `uvm_send(tr)
`ifdef VERILATOR
    /* verilator lint_on CASTCONST */
    /* verilator lint_on WIDTHTRUNC */
    /* verilator lint_on WIDTHEXPAND */
`endif
  endtask

  task automatic apb_read(input logic [ADDR_W-1:0] addr, output logic [DATA_W-1:0] data,
                          input logic [2:0] prot = 3'b000);
    apb_item#(ADDR_W, DATA_W) tr;
`ifdef VERILATOR
    /* verilator lint_off WIDTHEXPAND */
    /* verilator lint_off WIDTHTRUNC */
    /* verilator lint_off CASTCONST */
`endif
    `uvm_create(tr)
    tr.write = 1'b0;
    tr.addr  = addr;
    tr.prot  = prot;
    `uvm_send(tr)
    data = tr.rdata;
`ifdef VERILATOR
    /* verilator lint_on CASTCONST */
    /* verilator lint_on WIDTHTRUNC */
    /* verilator lint_on WIDTHEXPAND */
`endif
  endtask

  `uvm_object_param_utils(apb_base_seq#(ADDR_W, DATA_W))
endclass

// Simple deterministic write+readback sweep.
class apb_smoke_rw_seq #(
  int ADDR_W = 32,
  int DATA_W = 32
) extends apb_base_seq#(ADDR_W, DATA_W);
  localparam int STRB_W = (DATA_W/8);
  typedef logic [ADDR_W-1:0] addr_t;
  typedef logic [DATA_W-1:0] data_t;

  rand int unsigned num_txns = 10;
  rand logic [ADDR_W-1:0] base_addr = '0;

  function new(string name = "apb_smoke_rw_seq");
    super.new(name);
  endfunction

  task body();
    for (int unsigned i = 0; i < num_txns; i++) begin
      logic [ADDR_W-1:0] a;
      logic [DATA_W-1:0] w;
      logic [DATA_W-1:0] r;
      a = base_addr + addr_t'(i * STRB_W);
      w = data_t'($urandom());
      apb_write(a, w, '1, 3'b000);
      apb_read(a, r, 3'b000);
      if (r !== w) `uvm_error("APB_SCB", $sformatf("SMOKE mismatch addr=0x%0h exp=0x%0h got=0x%0h", a, w, r))
    end
  endtask

  `uvm_object_param_utils(apb_smoke_rw_seq#(ADDR_W, DATA_W))
endclass

// Random traffic sequence (read/write mix).
class apb_random_stress_seq #(
  int ADDR_W = 32,
  int DATA_W = 32
) extends apb_base_seq#(ADDR_W, DATA_W);
  localparam int STRB_W = (DATA_W/8);
  typedef logic [ADDR_W-1:0] addr_t;
  typedef logic [DATA_W-1:0] data_t;
  typedef logic [STRB_W-1:0] strb_t;
  typedef logic [2:0] prot_t;

  rand int unsigned num_txns = 1000;
  rand logic [ADDR_W-1:0] base_addr = '0;
  rand int unsigned span_bytes = 4096;
  rand int unsigned wr_pct = 50; // 0..100
  rand bit enable_apb4 = 1'b1;
  rand bit allow_zero_strobes = 1'b0;

  function new(string name = "apb_random_stress_seq");
    super.new(name);
  endfunction

  function automatic logic [STRB_W-1:0] rand_strb();
    logic [STRB_W-1:0] s;
    s = '1;
    if (!enable_apb4) return s;
    s = strb_t'($urandom());
    if (!allow_zero_strobes && (s == '0)) s = '1;
    return s;
  endfunction

  task body();
    for (int unsigned t = 0; t < num_txns; t++) begin
      logic [ADDR_W-1:0] a;
      logic [DATA_W-1:0] w;
      logic [DATA_W-1:0] r;
      bit do_wr;
      int unsigned off;
      off = $urandom_range(0, (span_bytes > STRB_W) ? (span_bytes-STRB_W) : 0);
      off = (off / STRB_W) * STRB_W;
      a = base_addr + addr_t'(off);
      do_wr = ($urandom_range(0, 99) < wr_pct);
      if (do_wr) begin
        w = data_t'($urandom());
        apb_write(a, w, rand_strb(), prot_t'($urandom_range(0, 7)));
      end else begin
        apb_read(a, r, prot_t'($urandom_range(0, 7)));
      end
    end
  endtask

  `uvm_object_param_utils(apb_random_stress_seq#(ADDR_W, DATA_W))
endclass

// APB4 masked write (PSTRB) directed check.
// - Writes a known word, then applies a masked update, then reads back and checks.
class apb_apb4_strobe_mask_seq #(
  int ADDR_W = 32,
  int DATA_W = 32
) extends apb_base_seq#(ADDR_W, DATA_W);
  localparam int STRB_W = (DATA_W/8);

  rand logic [ADDR_W-1:0] addr = '0;
  rand logic [DATA_W-1:0] full_data = '0;
  rand logic [DATA_W-1:0] mask_data = '0;
  rand logic [STRB_W-1:0] strb = '1;
  rand logic [2:0] prot = 3'b000;

  function new(string name = "apb_apb4_strobe_mask_seq");
    super.new(name);
  endfunction

  function automatic logic [DATA_W-1:0] apply_strb(
    logic [DATA_W-1:0] old_d,
    logic [DATA_W-1:0] new_d,
    logic [STRB_W-1:0] s
  );
    logic [DATA_W-1:0] out;
    out = old_d;
    for (int unsigned b = 0; b < STRB_W; b++) begin
      if (s[b]) out[8*b +: 8] = new_d[8*b +: 8];
    end
    return out;
  endfunction

  task body();
    logic [DATA_W-1:0] r;
    logic [DATA_W-1:0] exp;

    if (strb == '0) strb = '1;

    apb_write(addr, full_data, '1, prot);
    apb_write(addr, mask_data, strb, prot);
    apb_read(addr, r, prot);

    exp = apply_strb(full_data, mask_data, strb);
    if (r !== exp) begin
      `uvm_error("APB_SCB",
        $sformatf("APB4 strobe mask mismatch addr=0x%0h full=0x%0h mask=0x%0h strb=0x%0h exp=0x%0h got=0x%0h",
          addr, full_data, mask_data, strb, exp, r))
    end
  endtask

  `uvm_object_param_utils(apb_apb4_strobe_mask_seq#(ADDR_W, DATA_W))
endclass

`endif // KVIPS_APB_SEQUENCES_SVH
