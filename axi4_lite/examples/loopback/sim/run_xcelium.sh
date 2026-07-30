#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "${HERE}/../../../.." && pwd)"
OUT="${HERE}/out/xcelium"
mkdir -p "${OUT}"

if [[ -r /usr/share/Modules/init/bash ]]; then
  # shellcheck disable=SC1091
  source /usr/share/Modules/init/bash
fi
if ! command -v xrun >/dev/null 2>&1 && command -v module >/dev/null 2>&1; then
  module load xcelium/25.03.007 >/dev/null 2>&1 || true
fi
command -v xrun >/dev/null 2>&1 || { echo "ERROR: Xcelium xrun not found" >&2; exit 127; }

cd "${OUT}"
rm -rf xcelium.d run.log
xrun -64bit -sv -timescale 1ns/1ps \
  "${ROOT}/axi4_lite/sv/if/axi4_lite_if.sv" \
  "${ROOT}/axi4_lite/examples/loopback/axi4_lite_loopback.sv" \
  "${ROOT}/axi4_lite/examples/loopback/tb.sv" \
  -top tb -l run.log
grep -q "AXI4-LITE LOOPBACK PASS" run.log
