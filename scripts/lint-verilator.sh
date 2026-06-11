#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
VERILATOR_BIN="${VERILATOR_BIN:-verilator}"

# Portable lint tops intentionally instantiate interfaces without a full testbench.
# Suppress only diagnostics expected for that harness shape.
COMMON_LINT_FLAGS=(
  --lint-only
  --sv
  --language 1800-2017
  -Wall
  -Wno-DECLFILENAME
  -Wno-UNUSEDSIGNAL
  -Wno-UNUSEDPARAM
  -Wno-UNDRIVEN
  -Wno-SYNCASYNCNET
  --bbox-unsup
)

lint_top() {
  local top="$1"
  shift
  echo "==> Verilator lint: ${top}"
  "${VERILATOR_BIN}" "${COMMON_LINT_FLAGS[@]}" --top-module "${top}" "$@"
}

lint_top axi4_lint_top \
  -I"${ROOT}/common/sv" \
  -I"${ROOT}/axi4/sv/pkg" \
  -I"${ROOT}/axi4/sv/if" \
  "${ROOT}/common/sv/lint/axi4_lint_top.sv"

lint_top apb_lint_top \
  -I"${ROOT}/apb/sv/if" \
  "${ROOT}/common/sv/lint/apb_lint_top.sv"

lint_top ahb_lint_top \
  -I"${ROOT}/ahb/sv/if" \
  -I"${ROOT}/ahb/sv/assertions" \
  "${ROOT}/common/sv/lint/ahb_lint_top.sv"

echo "Verilator lint passed for AXI4, APB, and AHB portable subsets."
