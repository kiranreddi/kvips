---
layout: default
title: APB VIP
permalink: /docs/apb-vip/
---

# APB VIP (APB3/APB4)

KVIPS APB VIP is a vendor-neutral SystemVerilog/UVM VIP supporting both APB3 and APB4 in a **single compiled image** with a runtime protocol switch:
- `+APB_PROTOCOL=APB3`
- `+APB_PROTOCOL=APB4` (default)

## Quick start

Example tests are in `kvips/apb/examples/uvm_back2back/`.

From `kvips/apb/examples/`:
- `make list-tests`
- `make questa TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB4'`
- `make vcs   TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB4'`
- `make xcelium TEST=apb_b2b_smoke_test PLUSARGS='+APB_PROTOCOL=APB4'`

## Documentation

- Integration: `kvips/apb/docs/integration_guide.md`
- Supported features: `kvips/apb/docs/supported_features.md`
- Assertions: `kvips/apb/docs/assertions.md`
- Testplan: `kvips/apb/docs/testplan.md`
- Structure: `kvips/apb/docs/directory_structure.md`
- User guide: `kvips/apb/docs/user_guide.md`

