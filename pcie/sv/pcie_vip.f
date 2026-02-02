// PCIe VIP Compilation File List
// Copyright (c) KVIPS Project
// SPDX-License-Identifier: Apache-2.0
//
// Usage: 
//   vlog -f pcie_vip.f
//   vcs -f pcie_vip.f
//   xrun -f pcie_vip.f

// Include paths
+incdir+${PCIE_VIP_HOME}/sv/if
+incdir+${PCIE_VIP_HOME}/sv/pkg
+incdir+${PCIE_VIP_HOME}/sv/uvm
+incdir+${PCIE_VIP_HOME}/sv/assertions

// Interfaces (must be compiled first)
${PCIE_VIP_HOME}/sv/if/pcie_pipe_if.sv
${PCIE_VIP_HOME}/sv/if/pcie_serial_if.sv

// Packages
${PCIE_VIP_HOME}/sv/pkg/pcie_types_pkg.sv
${PCIE_VIP_HOME}/sv/pkg/pcie_uvm_pkg.sv

// UVM Components
${PCIE_VIP_HOME}/sv/uvm/pcie_cfg.sv
${PCIE_VIP_HOME}/sv/uvm/pcie_transaction.sv
${PCIE_VIP_HOME}/sv/uvm/pcie_driver.sv
${PCIE_VIP_HOME}/sv/uvm/pcie_monitor.sv
${PCIE_VIP_HOME}/sv/uvm/pcie_sequencer.sv
${PCIE_VIP_HOME}/sv/uvm/pcie_scoreboard.sv
${PCIE_VIP_HOME}/sv/uvm/pcie_agent.sv

// Assertions
${PCIE_VIP_HOME}/sv/assertions/pcie_phy_assertions.sv
${PCIE_VIP_HOME}/sv/assertions/pcie_dll_assertions.sv
${PCIE_VIP_HOME}/sv/assertions/pcie_tl_assertions.sv
