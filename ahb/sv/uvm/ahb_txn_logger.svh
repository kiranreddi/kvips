//------------------------------------------------------------------------------
// AHB Transaction Logger (monitor subscriber)
//------------------------------------------------------------------------------
`ifndef KVIPS_AHB_TXN_LOGGER_SVH
`define KVIPS_AHB_TXN_LOGGER_SVH

class ahb_txn_logger #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2
) extends uvm_subscriber #(ahb_item#(ADDR_W, DATA_W, HRESP_W));

  localparam string RID = "AHB_LOG";

  bit enable = 1'b1;

  longint unsigned sum_wr;
  longint unsigned sum_rd;
  longint unsigned sum_err;
  longint unsigned sum_stall;

  `uvm_component_param_utils(ahb_txn_logger#(ADDR_W, DATA_W, HRESP_W))

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if ($test$plusargs("KVIPS_AHB_LOG_OFF")) enable = 1'b0;
    void'(uvm_config_db#(bit)::get(this, "", "enable", enable));
    sum_wr = 0;
    sum_rd = 0;
    sum_err = 0;
    sum_stall = 0;
  endfunction

  virtual function void write(ahb_item#(ADDR_W, DATA_W, HRESP_W) t);
    if (t == null) return;
    if (t.write) sum_wr++; else sum_rd++;
    if (t.wait_cycles.size() != 0) sum_stall += t.wait_cycles[0];
    if ((HRESP_W == 1) && (t.resp.size() != 0) && t.resp[0][0]) sum_err++;
    if ((HRESP_W == 2) && (t.resp.size() != 0) && (t.resp[0] == 2'b01)) sum_err++;

    if (!enable) return;
    `uvm_info(RID,
      $sformatf("%s addr=0x%0h size=%0d burst=%0d resp=0x%0h stall=%0d wdata=0x%0h rdata=0x%0h",
        t.write ? "WR" : "RD",
        t.addr, t.size, t.burst,
        (t.resp.size() != 0) ? t.resp[0] : '0,
        (t.wait_cycles.size() != 0) ? t.wait_cycles[0] : 0,
        (t.wdata.size() != 0) ? t.wdata[0] : '0,
        (t.rdata.size() != 0) ? t.rdata[0] : '0),
      UVM_MEDIUM)
  endfunction

  function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info(RID,
      $sformatf("AHB log summary: wr=%0d rd=%0d err=%0d stall_cycles=%0d",
        sum_wr, sum_rd, sum_err, sum_stall),
      UVM_LOW)
  endfunction

endclass

`endif // KVIPS_AHB_TXN_LOGGER_SVH

