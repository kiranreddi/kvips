# PCIe VIP Test Plan (Current + Roadmap)

This document tracks the runnable tests that exist today and the longer-term roadmap tests (planned).

## 1. Runnable Tests (Today)

Implemented in `kvips/pcie/examples/uvm_back2back/tb/tb_pkg.sv`:

| Test | Purpose | Notes |
|------|---------|------|
| `pcie_b2b_smoke_test` | Compile/elab/run sanity | No protocol traffic generated |
| `pcie_b2b_mem_test` | Creates a `pcie_transaction` object | Does not yet drive a TLP through a modeled link |

## 2. Roadmap (Planned)

Once the VIP has a modeled topology (RC↔EP link model), sequences, and checking, expand to:
- Link bring-up tests (LTSSM coverage)
- Memory/config/io transaction tests (TLP generation + completion checking)
- Flow control, replay/ACK/NAK, error injection, and performance tests

The detailed long-term plan is tracked in `kvips/pcie/docs/COMPREHENSIVE_PCIE_VIP_PLAN.md`.
