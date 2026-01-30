# Integration guide (AHB VIP)

## 1) Instantiate the interface

```systemverilog
logic HCLK, HRESETn;
ahb_if #(32, 32) ahb_if0(.HCLK(HCLK), .HRESETn(HRESETn));
```

Single-slave systems often use `HREADY = HREADYOUT`:

```systemverilog
always_comb ahb_if0.HREADY = ahb_if0.HREADYOUT;
```

If your DUT provides both `HREADY` and `HREADYOUT` separately, connect them as defined by your fabric.

## 2) Connect to a DUT (two common patterns)

### A) DUT is an AHB slave (VIP master drives it)

- VIP master drives: `HADDR/HTRANS/HWRITE/HSIZE/HBURST/HPROT/HWDATA/HSEL`
- DUT drives: `HREADY/HRESP/HRDATA` (or `HREADYOUT` if it is the selected slave)

Configure the agent as master, ACTIVE:

```systemverilog
ahb_cfg#(32,32) m_cfg = ahb_cfg#(32,32)::type_id::create("m_cfg");
m_cfg.vif = ahb_if0;

ahb_agent_cfg#(32,32) m_agent_cfg = ahb_agent_cfg#(32,32)::type_id::create("m_agent_cfg");
m_agent_cfg.set_role_master();
m_agent_cfg.is_active = UVM_ACTIVE;
m_agent_cfg.cfg = m_cfg;
```

### B) DUT is an AHB master (VIP slave responds)

- DUT drives address/control and write data
- VIP slave responds with `HREADYOUT/HRESP/HRDATA` and captures writes

Configure the agent as slave, ACTIVE:

```systemverilog
ahb_cfg#(32,32) s_cfg = ahb_cfg#(32,32)::type_id::create("s_cfg");
s_cfg.vif = ahb_if0;
s_cfg.allow_wait_states = 1;
s_cfg.min_wait = 0;
s_cfg.max_wait = 8;

ahb_agent_cfg#(32,32) s_agent_cfg = ahb_agent_cfg#(32,32)::type_id::create("s_agent_cfg");
s_agent_cfg.set_role_slave();
s_agent_cfg.is_active = UVM_ACTIVE;
s_agent_cfg.cfg = s_cfg;
```

## 3) Runtime switches (plusargs)

Protocol mode:
- `+AHB_MODE=AHB_LITE` (default)
- `+AHB_MODE=AHB_FULL`

Assertions:
- Disable all assertions: `+KVIPS_AHB_ASSERT_OFF`
- Disable known/X checks: `+KVIPS_AHB_ASSERT_KNOWN_OFF`
- Disable strict checks: `+KVIPS_AHB_ASSERT_STRICT_OFF`

Scoreboard:
- Disable scoreboard: `+KVIPS_AHB_SB_OFF`
- Warn on reads of unwritten locations: `+KVIPS_AHB_SB_WARN_UNINIT`

Logger:
- Disable logger prints: `+KVIPS_AHB_LOG_OFF`

## 4) Multi-agent environments

`ahb_env` supports an array of agents (via `ahb_env_cfg.agent_cfgs[]`). In a typical single-bus setup, use one master agent + one slave agent sharing the same `vif`.

