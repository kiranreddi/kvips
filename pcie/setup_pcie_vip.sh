#!/bin/bash
#
# PCIe VIP Environment Setup Script (lightweight)
#
# Usage:
#   source kvips/pcie/setup_pcie_vip.sh --simulator questa|vcs|xcelium
#
# Notes:
# - Keep this script site-portable: prefer `module load` when available.
# - Do not hardcode license servers or internal paths here.

# Get script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Set PCIe VIP home
export PCIE_VIP_HOME="${SCRIPT_DIR}"

if [[ -d "${PCIE_VIP_HOME}/scripts" ]]; then
    export PATH="${PCIE_VIP_HOME}/scripts:${PATH}"
fi

# Default simulator
SIMULATOR="${1:-questa}"

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --simulator|-s)
            SIMULATOR="$2"
            shift 2
            ;;
        --help|-h)
            echo "Usage: source setup_pcie_vip.sh [OPTIONS]"
            echo ""
            echo "Options:"
            echo "  --simulator, -s    Simulator to use (questa, vcs, xcelium)"
            echo "  --help, -h         Show this help message"
            return 0
            ;;
        *)
            shift
            ;;
    esac
done

# Source LSF if available (some sites gate EDA tools behind LSF)
if [[ -f "/tools/lsf/conf/profile.lsf" ]]; then
    # shellcheck disable=SC1091
    source /tools/lsf/conf/profile.lsf
fi

# Setup simulator-specific environment
case "${SIMULATOR}" in
    questa|qvl|modelsim)
        echo "Setting up for Questa/ModelSim..."
        export SIMULATOR="questa"
        if command -v module >/dev/null 2>&1; then
            module load questa/2025_3_2 >/dev/null 2>&1 || true
        fi
        ;;
        
    vcs|synopsys)
        echo "Setting up for VCS..."
        export SIMULATOR="vcs"
        if command -v module >/dev/null 2>&1; then
            module load vcs/2025.06_1 >/dev/null 2>&1 || true
            module load verdi >/dev/null 2>&1 || true
        fi
        ;;
        
    xcelium|xrun|cadence)
        echo "Setting up for Xcelium..."
        export SIMULATOR="xcelium"
        if command -v module >/dev/null 2>&1; then
            module load xcelium/25.03.007 >/dev/null 2>&1 || true
        fi
        ;;
        
    *)
        echo "Warning: Unknown simulator '${SIMULATOR}'"
        echo "Supported: questa, vcs, xcelium"
        ;;
esac

# Print environment
echo ""
echo "PCIe VIP Environment:"
echo "  PCIE_VIP_HOME: ${PCIE_VIP_HOME}"
echo "  SIMULATOR:     ${SIMULATOR}"
echo ""

# Aliases for convenience
alias pcie_sim="cd ${PCIE_VIP_HOME}/examples/uvm_back2back/sim"
alias pcie_doc="cd ${PCIE_VIP_HOME}/docs"
alias pcie_sv="cd ${PCIE_VIP_HOME}/sv"

echo "Aliases defined:"
echo "  pcie_sim  - Go to simulation directory"
echo "  pcie_doc  - Go to documentation"
echo "  pcie_sv   - Go to source files"
echo ""
echo "Setup complete!"
