# AHB VIP directory structure

```
kvips/ahb/
├── README.md
├── docs/
│   ├── assertions.md
│   ├── directory_structure.md
│   ├── integration_guide.md
│   ├── supported_features.md
│   ├── tasks.md
│   ├── testplan.md
│   └── user_guide.md
├── examples/
│   ├── Makefile
│   └── uvm_back2back/
│       ├── README.md
│       ├── sim/
│       │   ├── filelist.f
│       │   ├── run_questa.sh
│       │   ├── run_vcs.sh
│       │   ├── run_xcelium.sh
│       │   ├── tests_questa.list
│       │   └── (optional regress/fsdbreport helpers)
│       └── tb/
│           ├── tb_pkg.sv
│           └── top.sv
└── sv/
    ├── assertions/
    │   └── ahb_if_sva.svh
    ├── if/
    │   └── ahb_if.sv
    ├── pkg/
    │   ├── ahb_types_pkg.sv
    │   └── ahb_uvm_pkg.sv
    └── uvm/
        ├── ahb_agent.svh
        ├── ahb_cfg.svh
        ├── ahb_env.svh
        ├── ahb_master_driver.svh
        ├── ahb_monitor.svh
        ├── ahb_scoreboard.svh
        ├── ahb_sequencer.svh
        ├── ahb_sequences.svh
        ├── ahb_slave_driver.svh
        ├── ahb_transaction.svh
        └── ahb_txn_logger.svh
```

