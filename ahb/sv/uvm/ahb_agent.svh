//------------------------------------------------------------------------------
// AHB Agent
//------------------------------------------------------------------------------
`ifndef KVIPS_AHB_AGENT_SVH
`define KVIPS_AHB_AGENT_SVH

class ahb_agent #(
  int ADDR_W  = 32,
  int DATA_W  = 32,
  int HRESP_W = 2,
  bit HAS_HMASTLOCK = 1'b0
) extends uvm_agent;

  localparam string RID = "AHB_AGENT";

  ahb_agent_cfg#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK) a_cfg;

  ahb_sequencer#(ADDR_W, DATA_W, HRESP_W)     sequencer;
  ahb_master_driver#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK) m_drv;
  ahb_slave_driver#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK)  s_drv;
  ahb_monitor#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK)       monitor;

  `uvm_component_param_utils(ahb_agent#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK))

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(ahb_agent_cfg#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK))::get(this, "", "cfg", a_cfg)) begin
      `uvm_fatal(RID, "Missing agent cfg in config DB (key: cfg)")
    end
    if (a_cfg.cfg == null) `uvm_fatal(RID, "a_cfg.cfg is null")
    a_cfg.cfg.apply_plusargs();

    monitor = ahb_monitor#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK)::type_id::create("monitor", this);
    uvm_config_db#(ahb_cfg#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK))::set(this, "monitor", "cfg", a_cfg.cfg);

    if ((a_cfg.is_active == UVM_ACTIVE) && a_cfg.is_master) begin
      sequencer = ahb_sequencer#(ADDR_W, DATA_W, HRESP_W)::type_id::create("sequencer", this);
      m_drv     = ahb_master_driver#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK)::type_id::create("m_drv", this);
      uvm_config_db#(ahb_cfg#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK))::set(this, "m_drv", "cfg", a_cfg.cfg);
    end

    if ((a_cfg.is_active == UVM_ACTIVE) && a_cfg.is_slave) begin
      s_drv = ahb_slave_driver#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK)::type_id::create("s_drv", this);
      uvm_config_db#(ahb_cfg#(ADDR_W, DATA_W, HRESP_W, HAS_HMASTLOCK))::set(this, "s_drv", "cfg", a_cfg.cfg);
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if ((a_cfg.is_active == UVM_ACTIVE) && a_cfg.is_master) begin
      m_drv.seq_item_port.connect(sequencer.seq_item_export);
    end
  endfunction

endclass

`endif // KVIPS_AHB_AGENT_SVH
