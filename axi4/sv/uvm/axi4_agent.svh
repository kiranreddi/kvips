//------------------------------------------------------------------------------
// AXI4 Agent
//------------------------------------------------------------------------------

`ifndef KVIPS_AXI4_AGENT_SVH
`define KVIPS_AXI4_AGENT_SVH

class axi4_agent #(
  int ADDR_W = 32,
  int DATA_W = 64,
  int ID_W   = 4,
  int USER_W = 1
) extends uvm_agent;

  localparam string RID = "AXI4_AGENT";

  axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W) cfg;

  axi4_sequencer#(ADDR_W, DATA_W, ID_W, USER_W)   sequencer;
  axi4_master_driver#(ADDR_W, DATA_W, ID_W, USER_W) m_drv;
  axi4_slave_driver#(ADDR_W, DATA_W, ID_W, USER_W)  s_drv;
  axi4_monitor#(ADDR_W, DATA_W, ID_W, USER_W)      monitor;

  `uvm_component_param_utils(axi4_agent#(ADDR_W, DATA_W, ID_W, USER_W))

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W))::get(this, "", "cfg", cfg)) begin
      `uvm_fatal(RID, "Missing cfg in config DB (key: cfg)")
    end

    monitor = axi4_monitor#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("monitor", this);
    uvm_config_db#(axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W))::set(this, "monitor", "cfg", cfg);

    if (cfg.is_master) begin
      sequencer = axi4_sequencer#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("sequencer", this);
      m_drv     = axi4_master_driver#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("m_drv", this);
      uvm_config_db#(axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W))::set(this, "m_drv", "cfg", cfg);
    end
    if (cfg.is_slave) begin
      s_drv = axi4_slave_driver#(ADDR_W, DATA_W, ID_W, USER_W)::type_id::create("s_drv", this);
      uvm_config_db#(axi4_agent_cfg#(ADDR_W, DATA_W, ID_W, USER_W))::set(this, "s_drv", "cfg", cfg);
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.is_master) begin
      m_drv.seq_item_port.connect(sequencer.seq_item_export);
    end
  endfunction

endclass

`endif // KVIPS_AXI4_AGENT_SVH
