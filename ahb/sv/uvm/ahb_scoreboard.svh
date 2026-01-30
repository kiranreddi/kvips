//------------------------------------------------------------------------------
// AHB Scoreboard (monitor-based expected memory)
//------------------------------------------------------------------------------
`ifndef KVIPS_AHB_SCOREBOARD_SVH
`define KVIPS_AHB_SCOREBOARD_SVH

class ahb_scoreboard #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2
) extends uvm_subscriber #(ahb_item#(ADDR_W, DATA_W, HRESP_W));

  localparam string RID = "AHB_SCB";

  bit enable = 1'b1;
  bit warn_uninit = 1'b0;

  // Byte-addressed expected model.
  byte unsigned exp_mem[longint unsigned];
  bit           exp_valid[longint unsigned];

  longint unsigned sum_wr;
  longint unsigned sum_rd;
  longint unsigned sum_err;
  longint unsigned sum_mismatch;

  `uvm_component_param_utils(ahb_scoreboard#(ADDR_W, DATA_W, HRESP_W))

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function int unsigned data_bus_bytes();
    return (DATA_W/8);
  endfunction

  function int unsigned size_bytes(ahb_size_e size);
    return (1 << size);
  endfunction

  function bit is_error_resp(ahb_item#(ADDR_W, DATA_W, HRESP_W) t);
    if (t.resp.size() == 0) return 0;
    if (HRESP_W == 1) return t.resp[0][0];
    return (t.resp[0] == 2'b01);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if ($test$plusargs("KVIPS_AHB_SB_OFF")) enable = 1'b0;
    if ($test$plusargs("KVIPS_AHB_SB_WARN_UNINIT")) warn_uninit = 1'b1;
    void'(uvm_config_db#(bit)::get(this, "", "enable", enable));
    void'(uvm_config_db#(bit)::get(this, "", "warn_uninit", warn_uninit));
    sum_wr = 0;
    sum_rd = 0;
    sum_err = 0;
    sum_mismatch = 0;
  endfunction

  function void exp_write(logic [ADDR_W-1:0] addr, ahb_size_e size, logic [DATA_W-1:0] wdata);
    int unsigned sb = size_bytes(size);
    int unsigned lane = addr % data_bus_bytes();
    for (int unsigned i = 0; i < sb; i++) begin
      int unsigned byte_lane = lane + i;
      if (byte_lane < data_bus_bytes()) begin
        exp_mem[longint'(addr + i)] = wdata[(8*byte_lane) +: 8];
        exp_valid[longint'(addr + i)] = 1'b1;
      end
    end
  endfunction

  function logic [DATA_W-1:0] exp_read(logic [ADDR_W-1:0] addr, ahb_size_e size, output bit init_ok);
    logic [DATA_W-1:0] r;
    int unsigned sb = size_bytes(size);
    int unsigned lane = addr % data_bus_bytes();
    init_ok = 1'b1;
    r = '0;
    for (int unsigned i = 0; i < sb; i++) begin
      int unsigned byte_lane = lane + i;
      if (byte_lane < data_bus_bytes()) begin
        if (!exp_valid.exists(longint'(addr + i)) || !exp_valid[longint'(addr + i)]) init_ok = 1'b0;
        r[(8*byte_lane) +: 8] = exp_mem.exists(longint'(addr + i)) ? exp_mem[longint'(addr + i)] : 8'h00;
      end
    end
    return r;
  endfunction

  virtual function void write(ahb_item#(ADDR_W, DATA_W, HRESP_W) t);
    bit init_ok;
    logic [DATA_W-1:0] exp_d;
    if (t == null) return;

    if (is_error_resp(t)) sum_err++;
    if (t.write) sum_wr++; else sum_rd++;
    if (!enable) return;

    if (t.write) begin
      exp_write(t.addr, t.size, (t.wdata.size() != 0) ? t.wdata[0] : '0);
    end else begin
      if (is_error_resp(t)) return;
      exp_d = exp_read(t.addr, t.size, init_ok);
      if (!init_ok && warn_uninit) begin
        `uvm_warning(RID, $sformatf("Read from unwritten addr=0x%0h (treated as 0)", t.addr))
      end
      if ((t.rdata.size() != 0) && (t.rdata[0] !== exp_d)) begin
        sum_mismatch++;
        `uvm_error(RID, $sformatf("READ MISMATCH addr=0x%0h exp=0x%0h got=0x%0h", t.addr, exp_d, t.rdata[0]))
      end
    end
  endfunction

  function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info(RID,
      $sformatf("AHB SB summary: enable=%0d wr=%0d rd=%0d err=%0d mismatch=%0d",
        enable, sum_wr, sum_rd, sum_err, sum_mismatch),
      UVM_LOW)
  endfunction

endclass

`endif // KVIPS_AHB_SCOREBOARD_SVH

