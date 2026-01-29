# Directory Structure

This VIP follows the same structure conventions as `kvips/axi4/`.

```
apb/
├── docs/
│   ├── directory_structure.md
│   ├── integration_guide.md
│   ├── supported_features.md
│   ├── assertions.md
│   ├── testplan.md
│   └── user_guide.md
├── examples/
│   └── uvm_back2back/
│       ├── tb/
│       └── sim/
└── sv/
    ├── if/
    ├── pkg/
    ├── uvm/
    └── assertions/
```

## Notes
- `sv/if/apb_if.sv` always contains APB4 signals (`PPROT`, `PSTRB`) to support a single compiled image.
- Protocol mode is selected at runtime using `+APB_PROTOCOL=APB3|APB4`.

