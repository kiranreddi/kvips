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

  typedef logic [ADDR_W-1:0] addr_t;
  typedef logic [3:0] prot_t;

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

  function addr_t legal_addr(ahb_size_e size, ahb_burst_e burst, int unsigned beats);
    int unsigned bytes;
    int unsigned span;
    int unsigned limit;
    int unsigned off;
    bytes = 1 << int'(size);
    span = bytes * beats;
    limit = (span < 1024) ? (1024 - span) : 0;
    if (span == 0) span = bytes;
    off = (span_bytes > limit) ? $urandom_range(0, limit) : $urandom_range(0, span_bytes);
    off = (off / bytes) * bytes;
    if (burst inside {AHB_BURST_WRAP4, AHB_BURST_WRAP8, AHB_BURST_WRAP16})
      off = (off / span) * span;
    return addr_t'(int'(base_addr) + off);
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
      tr.addr  = legal_addr(tr.size, tr.burst, 1);
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
      tr.addr  = legal_addr(tr.size, tr.burst, 1);
      tr.prot  = prot_t'($urandom());
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
      tr.prot  = prot_t'($urandom());
      tr.lock  = 0;
      tr.len   = (tr.burst == AHB_BURST_INCR4) ? 4 : (tr.burst == AHB_BURST_INCR8) ? 8 : 16;
      tr.addr  = legal_addr(tr.size, tr.burst, tr.len);
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
      tr.prot  = prot_t'($urandom());
      tr.lock  = 0;
      tr.len   = (tr.burst == AHB_BURST_WRAP4) ? 4 : (tr.burst == AHB_BURST_WRAP8) ? 8 : 16;
      beats = tr.len;
      // A wrap start must be aligned to the complete wrap span.
      tr.addr = legal_addr(tr.size, tr.burst, tr.len);
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
      tr.prot  = prot_t'($urandom());
      tr.lock  = 0;
      tr.len   = (tr.burst == AHB_BURST_INCR) ? $urandom_range(1, 16) : ((tr.burst inside {AHB_BURST_INCR4,AHB_BURST_WRAP4}) ? 4 :
                (tr.burst inside {AHB_BURST_INCR8,AHB_BURST_WRAP8}) ? 8 :
                (tr.burst inside {AHB_BURST_INCR16,AHB_BURST_WRAP16}) ? 16 : 1);
      tr.addr  = legal_addr(tr.size, tr.burst, tr.len);
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
      tr.prot  = prot_t'($urandom());
      tr.lock  = ($urandom_range(0, 99) < 2);
      tr.len   = (tr.burst == AHB_BURST_INCR) ? $urandom_range(1, 16) : ((tr.burst inside {AHB_BURST_INCR4,AHB_BURST_WRAP4}) ? 4 :
                (tr.burst inside {AHB_BURST_INCR8,AHB_BURST_WRAP8}) ? 8 :
                (tr.burst inside {AHB_BURST_INCR16,AHB_BURST_WRAP16}) ? 16 : 1);
      tr.addr  = legal_addr(tr.size, tr.burst, tr.len);
      beats = tr.len;
      if (tr.write) begin
        tr.wdata = new[beats];
        foreach (tr.wdata[j]) tr.wdata[j] = $urandom();
      end
      finish_item(tr);
    end
  endtask
endclass

class ahb_busy_seq #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2
) extends ahb_base_seq#(ADDR_W, DATA_W, HRESP_W);
  `uvm_object_param_utils(ahb_busy_seq#(ADDR_W, DATA_W, HRESP_W))
  function new(string name="ahb_busy_seq"); super.new(name); endfunction

  task body();
    ahb_item#(ADDR_W, DATA_W, HRESP_W) wr;
    ahb_item#(ADDR_W, DATA_W, HRESP_W) rd;
    wr = ahb_item#(ADDR_W, DATA_W, HRESP_W)::type_id::create("busy_wr");
    start_item(wr);
    wr.write = 1'b1;
    wr.size = AHB_SIZE_32;
    wr.burst = AHB_BURST_INCR16;
    wr.len = 16;
    wr.addr = legal_addr(wr.size, wr.burst, wr.len);
    wr.prot = '0;
    wr.lock = 1'b0;
    wr.nonsec = 1'b1;
    wr.wdata = new[16];
    foreach (wr.wdata[i]) wr.wdata[i] = 32'hb000_0000 + i;
    finish_item(wr);

    rd = ahb_item#(ADDR_W, DATA_W, HRESP_W)::type_id::create("busy_rd");
    start_item(rd);
    rd.write = 1'b0;
    rd.size = AHB_SIZE_32;
    rd.burst = AHB_BURST_INCR16;
    rd.len = 16;
    rd.addr = wr.addr;
    rd.prot = '0;
    rd.lock = 1'b0;
    rd.nonsec = 1'b1;
    finish_item(rd);
  endtask
endclass

class ahb_boundary_seq #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2
) extends ahb_base_seq#(ADDR_W, DATA_W, HRESP_W);
  `uvm_object_param_utils(ahb_boundary_seq#(ADDR_W, DATA_W, HRESP_W))
  function new(string name="ahb_boundary_seq"); super.new(name); endfunction

  task body();
    ahb_item#(ADDR_W, DATA_W, HRESP_W) tr;
    tr = ahb_item#(ADDR_W, DATA_W, HRESP_W)::type_id::create("boundary_wr");
    start_item(tr);
    tr.write = 1'b1;
    tr.size = AHB_SIZE_32;
    tr.burst = AHB_BURST_INCR4;
    tr.len = 4;
    tr.addr = addr_t'(32'h0000_03f0);
    tr.prot = '0;
    tr.lock = 1'b0;
    tr.wdata = new[4];
    foreach (tr.wdata[i]) tr.wdata[i] = 32'hc000_0000 + i;
    finish_item(tr);
  endtask
endclass

class ahb_full_response_seq #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2
) extends ahb_base_seq#(ADDR_W, DATA_W, HRESP_W);
  ahb_resp_e expected_resp = AHB_RESP_OKAY;
  `uvm_object_param_utils(ahb_full_response_seq#(ADDR_W, DATA_W, HRESP_W))
  function new(string name="ahb_full_response_seq"); super.new(name); endfunction

  task body();
    ahb_item#(ADDR_W, DATA_W, HRESP_W) tr;
    logic [HRESP_W-1:0] expected_signal;
    tr = ahb_item#(ADDR_W, DATA_W, HRESP_W)::type_id::create("full_response");
    start_item(tr);
    tr.write = 1'b0;
    tr.size = AHB_SIZE_32;
    tr.burst = AHB_BURST_SINGLE;
    tr.len = 1;
    tr.addr = addr_t'(32'h0000_0200);
    tr.prot = '0;
    tr.lock = 1'b0;
    finish_item(tr);
    expected_signal = '0;
    if (HRESP_W == 1)
      expected_signal = (expected_resp == AHB_RESP_OKAY) ? 1'b0 : 1'b1;
    else
      expected_signal = expected_resp;
    if ((tr.resp.size() == 0) || (tr.resp[0] !== expected_signal)) begin
      `uvm_error("AHB_SEQ", $sformatf("Expected Full response %0d, got %0h",
        expected_resp, (tr.resp.size() == 0) ? 'x : tr.resp[0]))
    end
  endtask
endclass

`endif // KVIPS_AHB_SEQUENCES_SVH
