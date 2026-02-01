//------------------------------------------------------------------------------
// AHB Sequences
//------------------------------------------------------------------------------
`ifndef KVIPS_AHB_SEQUENCES_SVH
`define KVIPS_AHB_SEQUENCES_SVH

class ahb_base_seq #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2
) extends uvm_sequence #(ahb_item#(ADDR_W, DATA_W, HRESP_W));

  rand int unsigned num_txns = 100;
  rand int unsigned wr_pct   = 50;
  rand logic [ADDR_W-1:0] base_addr = '0;
  rand int unsigned span_bytes = 1024;

  `uvm_object_param_utils(ahb_base_seq#(ADDR_W, DATA_W, HRESP_W))

  function new(string name = "ahb_base_seq");
    super.new(name);
  endfunction

  function ahb_burst_e rand_burst();
    int unsigned r = $urandom_range(0, 99);
    if (r < 40) return AHB_BURST_SINGLE;
    if (r < 70) return AHB_BURST_INCR4;
    if (r < 85) return AHB_BURST_INCR8;
    if (r < 93) return AHB_BURST_INCR16;
    if (r < 96) return AHB_BURST_WRAP4;
    if (r < 98) return AHB_BURST_WRAP8;
    return AHB_BURST_WRAP16;
  endfunction

  function ahb_size_e rand_size();
    int unsigned r;
    int unsigned max_sz;
    r = $urandom_range(0, 99);
    max_sz = $clog2(DATA_W/8);
    if (max_sz == 0) return AHB_SIZE_8;
    if (max_sz == 1) return (r < 50) ? AHB_SIZE_8 : AHB_SIZE_16;
    if (max_sz == 2) begin
      if (r < 30) return AHB_SIZE_8;
      if (r < 55) return AHB_SIZE_16;
      return AHB_SIZE_32;
    end
    // DATA_W >= 64
    if (r < 30) return AHB_SIZE_8;
    if (r < 55) return AHB_SIZE_16;
    if (r < 90) return AHB_SIZE_32;
    return AHB_SIZE_64;
  endfunction

  task body();
    `uvm_fatal("AHB_SEQ", "ahb_base_seq.body() must be overridden")
  endtask
endclass

class ahb_smoke_seq #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2
) extends ahb_base_seq#(ADDR_W, DATA_W, HRESP_W);

  `uvm_object_param_utils(ahb_smoke_seq#(ADDR_W, DATA_W, HRESP_W))
  function new(string name="ahb_smoke_seq"); super.new(name); num_txns = 10; wr_pct = 50; endfunction

  task body();
    for (int unsigned i = 0; i < num_txns; i++) begin
      ahb_item#(ADDR_W, DATA_W, HRESP_W) tr;
      tr = ahb_item#(ADDR_W, DATA_W, HRESP_W)::type_id::create($sformatf("tr_%0d", i));
      start_item(tr);
      tr.write = ($urandom_range(0, 99) < wr_pct);
      tr.size  = rand_size();
      tr.burst = AHB_BURST_SINGLE;
      tr.addr  = base_addr + $urandom_range(0, span_bytes-1);
      tr.prot  = 4'h0;
      tr.lock  = 0;
      tr.len   = 1;
      if (tr.write) begin
        tr.wdata = new[1];
        tr.wdata[0] = $urandom();
      end
      finish_item(tr);
    end
  endtask
endclass

class ahb_single_rw_seq #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2
) extends ahb_base_seq#(ADDR_W, DATA_W, HRESP_W);

  `uvm_object_param_utils(ahb_single_rw_seq#(ADDR_W, DATA_W, HRESP_W))
  function new(string name="ahb_single_rw_seq"); super.new(name); num_txns = 20; endfunction

  task body();
    for (int unsigned i = 0; i < num_txns; i++) begin
      ahb_item#(ADDR_W, DATA_W, HRESP_W) tr;
      tr = ahb_item#(ADDR_W, DATA_W, HRESP_W)::type_id::create($sformatf("tr_%0d", i));
      start_item(tr);
      tr.burst = AHB_BURST_SINGLE;
      tr.size  = rand_size();
      tr.write = ($urandom_range(0, 99) < wr_pct);
      tr.addr  = base_addr + $urandom_range(0, span_bytes-1);
      tr.prot  = $urandom();
      tr.lock  = 0;
      tr.len   = 1;
      if (tr.write) begin
        tr.wdata = new[1];
        tr.wdata[0] = $urandom();
      end
      finish_item(tr);
    end
  endtask
endclass

class ahb_wait_state_seq #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2
) extends ahb_single_rw_seq#(ADDR_W, DATA_W, HRESP_W);
  `uvm_object_param_utils(ahb_wait_state_seq#(ADDR_W, DATA_W, HRESP_W))
  function new(string name="ahb_wait_state_seq"); super.new(name); num_txns = 200; wr_pct = 50; endfunction
endclass

class ahb_incr_burst_seq #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2
) extends ahb_base_seq#(ADDR_W, DATA_W, HRESP_W);

  `uvm_object_param_utils(ahb_incr_burst_seq#(ADDR_W, DATA_W, HRESP_W))
  function new(string name="ahb_incr_burst_seq"); super.new(name); num_txns = 50; endfunction

  task body();
    for (int unsigned i = 0; i < num_txns; i++) begin
      ahb_item#(ADDR_W, DATA_W, HRESP_W) tr;
      int unsigned beats;
      tr = ahb_item#(ADDR_W, DATA_W, HRESP_W)::type_id::create($sformatf("tr_%0d", i));
      start_item(tr);
      tr.write = ($urandom_range(0, 99) < wr_pct);
      tr.size  = AHB_SIZE_32;
      tr.burst = (i % 3 == 0) ? AHB_BURST_INCR16 : ((i % 3 == 1) ? AHB_BURST_INCR8 : AHB_BURST_INCR4);
      tr.addr  = base_addr + ($urandom_range(0, span_bytes-1) & ~32'h3);
      tr.prot  = $urandom();
      tr.lock  = 0;
      tr.len   = (tr.burst == AHB_BURST_INCR4) ? 4 : (tr.burst == AHB_BURST_INCR8) ? 8 : 16;
      beats = tr.len;
      if (tr.write) begin
        tr.wdata = new[beats];
        foreach (tr.wdata[j]) tr.wdata[j] = $urandom();
      end
      finish_item(tr);
    end
  endtask
endclass

class ahb_wrap_burst_seq #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2
) extends ahb_base_seq#(ADDR_W, DATA_W, HRESP_W);

  `uvm_object_param_utils(ahb_wrap_burst_seq#(ADDR_W, DATA_W, HRESP_W))
  function new(string name="ahb_wrap_burst_seq"); super.new(name); num_txns = 50; endfunction

  task body();
    for (int unsigned i = 0; i < num_txns; i++) begin
      ahb_item#(ADDR_W, DATA_W, HRESP_W) tr;
      int unsigned beats;
      tr = ahb_item#(ADDR_W, DATA_W, HRESP_W)::type_id::create($sformatf("tr_%0d", i));
      start_item(tr);
      tr.write = ($urandom_range(0, 99) < wr_pct);
      tr.size  = AHB_SIZE_32;
      tr.burst = (i % 3 == 0) ? AHB_BURST_WRAP16 : ((i % 3 == 1) ? AHB_BURST_WRAP8 : AHB_BURST_WRAP4);
      tr.prot  = $urandom();
      tr.lock  = 0;
      tr.len   = (tr.burst == AHB_BURST_WRAP4) ? 4 : (tr.burst == AHB_BURST_WRAP8) ? 8 : 16;
      beats = tr.len;
      // Choose start address inside the wrap boundary.
      tr.addr = base_addr + ($urandom_range(0, span_bytes-1) & ~32'h3);
      if (tr.write) begin
        tr.wdata = new[beats];
        foreach (tr.wdata[j]) tr.wdata[j] = $urandom();
      end
      finish_item(tr);
    end
  endtask
endclass

class ahb_back_to_back_seq #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2
) extends ahb_base_seq#(ADDR_W, DATA_W, HRESP_W);
  `uvm_object_param_utils(ahb_back_to_back_seq#(ADDR_W, DATA_W, HRESP_W))
  function new(string name="ahb_back_to_back_seq"); super.new(name); num_txns = 500; wr_pct = 50; endfunction
  task body();
    for (int unsigned i = 0; i < num_txns; i++) begin
      ahb_item#(ADDR_W, DATA_W, HRESP_W) tr;
      int unsigned beats;
      tr = ahb_item#(ADDR_W, DATA_W, HRESP_W)::type_id::create($sformatf("tr_%0d", i));
      start_item(tr);
      tr.write = ($urandom_range(0, 99) < wr_pct);
      tr.size  = rand_size();
      tr.burst = rand_burst();
      tr.addr  = base_addr + $urandom_range(0, span_bytes-1);
      tr.prot  = $urandom();
      tr.lock  = 0;
      tr.len   = (tr.burst == AHB_BURST_INCR) ? $urandom_range(1, 16) : ((tr.burst inside {AHB_BURST_INCR4,AHB_BURST_WRAP4}) ? 4 :
                (tr.burst inside {AHB_BURST_INCR8,AHB_BURST_WRAP8}) ? 8 :
                (tr.burst inside {AHB_BURST_INCR16,AHB_BURST_WRAP16}) ? 16 : 1);
      beats = tr.len;
      if (tr.write) begin
        tr.wdata = new[beats];
        foreach (tr.wdata[j]) tr.wdata[j] = $urandom();
      end
      finish_item(tr);
    end
  endtask
endclass

class ahb_error_seq #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2
) extends ahb_single_rw_seq#(ADDR_W, DATA_W, HRESP_W);
  `uvm_object_param_utils(ahb_error_seq#(ADDR_W, DATA_W, HRESP_W))
  function new(string name="ahb_error_seq"); super.new(name); num_txns = 200; wr_pct = 50; endfunction
endclass

class ahb_random_stress_seq #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2
) extends ahb_base_seq#(ADDR_W, DATA_W, HRESP_W);

  `uvm_object_param_utils(ahb_random_stress_seq#(ADDR_W, DATA_W, HRESP_W))
  function new(string name="ahb_random_stress_seq"); super.new(name); endfunction

  task body();
    for (int unsigned i = 0; i < num_txns; i++) begin
      ahb_item#(ADDR_W, DATA_W, HRESP_W) tr;
      int unsigned beats;
      tr = ahb_item#(ADDR_W, DATA_W, HRESP_W)::type_id::create($sformatf("tr_%0d", i));
      start_item(tr);
      tr.write = ($urandom_range(0, 99) < wr_pct);
      tr.size  = rand_size();
      tr.burst = rand_burst();
      tr.addr  = base_addr + $urandom_range(0, span_bytes-1);
      tr.prot  = $urandom();
      tr.lock  = ($urandom_range(0, 99) < 2);
      tr.len   = (tr.burst == AHB_BURST_INCR) ? $urandom_range(1, 16) : ((tr.burst inside {AHB_BURST_INCR4,AHB_BURST_WRAP4}) ? 4 :
                (tr.burst inside {AHB_BURST_INCR8,AHB_BURST_WRAP8}) ? 8 :
                (tr.burst inside {AHB_BURST_INCR16,AHB_BURST_WRAP16}) ? 16 : 1);
      beats = tr.len;
      if (tr.write) begin
        tr.wdata = new[beats];
        foreach (tr.wdata[j]) tr.wdata[j] = $urandom();
      end
      finish_item(tr);
    end
  endtask
endclass

`endif // KVIPS_AHB_SEQUENCES_SVH
