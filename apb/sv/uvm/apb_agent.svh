//------------------------------------------------------------------------------
// APB Agent
//------------------------------------------------------------------------------
`ifndef KVIPS_APB_AGENT_SVH
`define KVIPS_APB_AGENT_SVH

class apb_agent #(
  int ADDR_W = 32,
  int DATA_W = 32,
  int NSEL   = 1
) extends uvm_agent;

  localparam string RID = "APB_AGENT";

  apb_agent_cfg#(ADDR_W, DATA_W, NSEL) a_cfg;

  apb_sequencer#(ADDR_W, DATA_W)                sequencer;
  apb_master_driver#(ADDR_W, DATA_W, NSEL)      m_drv;
  apb_slave_driver#(ADDR_W, DATA_W, NSEL)       s_drv;
  apb_monitor#(ADDR_W, DATA_W, NSEL)            monitor;

  `uvm_component_param_utils(apb_agent#(ADDR_W, DATA_W, NSEL))

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(apb_agent_cfg#(ADDR_W, DATA_W, NSEL))::get(this, "", "cfg", a_cfg)) begin
      `uvm_fatal(RID, "Missing agent cfg in config DB (key: cfg)")
    end
    if (a_cfg.cfg == null) `uvm_fatal(RID, "a_cfg.cfg is null")

    monitor = apb_monitor#(ADDR_W, DATA_W, NSEL)::type_id::create("monitor", this);
    uvm_config_db#(apb_cfg#(ADDR_W, DATA_W, NSEL))::set(this, "monitor", "cfg", a_cfg.cfg);

    if ((a_cfg.is_active == UVM_ACTIVE) && a_cfg.is_master) begin
      sequencer = apb_sequencer#(ADDR_W, DATA_W)::type_id::create("sequencer", this);
      m_drv     = apb_master_driver#(ADDR_W, DATA_W, NSEL)::type_id::create("m_drv", this);
      uvm_config_db#(apb_cfg#(ADDR_W, DATA_W, NSEL))::set(this, "m_drv", "cfg", a_cfg.cfg);
    end

    if ((a_cfg.is_active == UVM_ACTIVE) && a_cfg.is_slave) begin
      s_drv = apb_slave_driver#(ADDR_W, DATA_W, NSEL)::type_id::create("s_drv", this);
      uvm_config_db#(apb_cfg#(ADDR_W, DATA_W, NSEL))::set(this, "s_drv", "cfg", a_cfg.cfg);
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if ((a_cfg.is_active == UVM_ACTIVE) && a_cfg.is_master) begin
      m_drv.seq_item_port.connect(sequencer.seq_item_export);
    end
  endfunction

endclass

`endif // KVIPS_APB_AGENT_SVH

