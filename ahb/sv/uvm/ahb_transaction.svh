//------------------------------------------------------------------------------
// AHB Transaction Item
//------------------------------------------------------------------------------
`ifndef KVIPS_AHB_TRANSACTION_SVH
`define KVIPS_AHB_TRANSACTION_SVH

class ahb_item #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2
) extends uvm_sequence_item;

  rand bit                write;
  rand logic [ADDR_W-1:0] addr;
  rand ahb_size_e         size;
  rand ahb_burst_e        burst;
  rand logic [3:0]        prot;
  rand bit                nonsec;
  rand bit                lock;
  // HMASTER is carried as metadata even in the single-master example.  This
  // lets a fabric/interconnect integration preserve master ownership without
  // changing the transaction API.
  logic [3:0]             master_id = '0;

  // For HBURST=INCR, len is randomized (bounded by cfg.max_incr_len).
  rand int unsigned       len;

  // Data payloads (burst-aware). For SINGLE, arrays are size 1.
  rand logic [DATA_W-1:0] wdata[];
  logic [DATA_W-1:0]      rdata[];
  int unsigned            wait_cycles[]; // observed (monitor)
  logic [HRESP_W-1:0]     resp[];        // observed per-beat (monitor)

  // Derived / metadata
  int unsigned beats;
  time start_t;
  time end_t;

  function new(string name = "ahb_item");
    super.new(name);
  endfunction

  function int unsigned burst_len(ahb_burst_e b, int unsigned incr_len);
    case (b)
      AHB_BURST_SINGLE: return 1;
      AHB_BURST_INCR4:  return 4;
      AHB_BURST_WRAP4:  return 4;
      AHB_BURST_INCR8:  return 8;
      AHB_BURST_WRAP8:  return 8;
      AHB_BURST_INCR16: return 16;
      AHB_BURST_WRAP16: return 16;
      default:          return (incr_len == 0) ? 1 : incr_len;
    endcase
  endfunction

  function void post_randomize();
    beats = (burst == AHB_BURST_INCR) ? len : burst_len(burst, len);
    if (beats == 0) beats = 1;

    if (wdata.size() != beats) wdata = new[beats];
    if (rdata.size() != beats) rdata = new[beats];
    if (wait_cycles.size() != beats) wait_cycles = new[beats];
    if (resp.size() != beats) resp = new[beats];
  endfunction

  constraint c_len_default {
    len inside {[1:16]};
  }

  constraint c_burst_len_fixed {
    if (burst == AHB_BURST_SINGLE) len == 1;
    if (burst inside {AHB_BURST_INCR4, AHB_BURST_WRAP4}) len == 4;
    if (burst inside {AHB_BURST_INCR8, AHB_BURST_WRAP8}) len == 8;
    if (burst inside {AHB_BURST_INCR16, AHB_BURST_WRAP16}) len == 16;
  }

  function string convert2string();
    return $sformatf("AHB item: %s addr=0x%0h size=%0d burst=%0d beats=%0d nonsec=%0d master=%0d resp0=0x%0h wdata0=0x%0h rdata0=0x%0h",
                     write ? "WRITE" : "READ", addr, size, burst, beats,
                     nonsec, master_id,
                     (resp.size() == 0) ? 'x : resp[0],
                     (wdata.size() == 0) ? 'x : wdata[0],
                     (rdata.size() == 0) ? 'x : rdata[0]);
  endfunction

`ifdef VERILATOR
  /* verilator lint_off WIDTHEXPAND */
  /* verilator lint_off WIDTHTRUNC */
`endif
  `uvm_object_param_utils_begin(ahb_item#(ADDR_W, DATA_W, HRESP_W))
    `uvm_field_int(write, UVM_DEFAULT)
    `uvm_field_int(addr, UVM_DEFAULT)
    `uvm_field_enum(ahb_size_e, size, UVM_DEFAULT)
    `uvm_field_enum(ahb_burst_e, burst, UVM_DEFAULT)
    `uvm_field_int(prot, UVM_DEFAULT)
    `uvm_field_int(nonsec, UVM_DEFAULT)
    `uvm_field_int(lock, UVM_DEFAULT)
    `uvm_field_int(master_id, UVM_DEFAULT)
    `uvm_field_int(len, UVM_DEFAULT)
    `uvm_field_array_int(wdata, UVM_DEFAULT)
    `uvm_field_array_int(rdata, UVM_DEFAULT | UVM_NOCOMPARE)
    `uvm_field_array_int(wait_cycles, UVM_DEFAULT | UVM_NOCOMPARE)
    `uvm_field_array_int(resp, UVM_DEFAULT | UVM_NOCOMPARE)
  `uvm_object_utils_end
`ifdef VERILATOR
  /* verilator lint_on WIDTHTRUNC */
  /* verilator lint_on WIDTHEXPAND */
`endif
endclass

`endif // KVIPS_AHB_TRANSACTION_SVH
