# PCIe VIP Assertions (SVA) — Current Status

The PCIe VIP contains standalone SVA modules under `kvips/pcie/sv/assertions/`:

- `pcie_phy_assertions.sv`
- `pcie_dll_assertions.sv`
- `pcie_tl_assertions.sv`

## What Exists Today

- The files provide a **template** set of assertion structures and example properties.
- They are **not currently bound/instantiated** by `examples/uvm_back2back`.

## Runtime Control

There is no standardized plusarg-based assertion enable/disable plumbing in the current example TB. If you instantiate these modules, you can use the provided `assert_enable` input in each module to gate checks.

## Next Steps (Planned)

- Bind assertions to `pcie_pipe_if`/`pcie_serial_if` (or to a higher-level “layer model” once one exists).
- Define a consistent plusarg/config scheme (similar to AXI/APB/AHB in KVIPS) for:
  - `assertions_enable`
  - `strict_checks`
  - per-layer enable
  - X-propagation policy during reset
