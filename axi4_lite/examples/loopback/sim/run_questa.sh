#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "${HERE}/../../../.." && pwd)"
OUT="${HERE}/out/questa"
mkdir -p "${OUT}"

if [[ -r /usr/share/Modules/init/bash ]]; then
  # shellcheck disable=SC1091
  source /usr/share/Modules/init/bash
fi
if ! command -v vlog >/dev/null 2>&1 && command -v module >/dev/null 2>&1; then
  module load questa/2025_3_2 >/dev/null 2>&1 || true
fi
command -v vlog >/dev/null 2>&1 || { echo "ERROR: Questa vlog not found" >&2; exit 127; }
command -v vsim >/dev/null 2>&1 || { echo "ERROR: Questa vsim not found" >&2; exit 127; }

cd "${OUT}"
rm -rf work transcript vsim.wlf compile.log run.log
vlib work
vlog -sv -timescale 1ns/1ps \
  "${ROOT}/axi4_lite/sv/if/axi4_lite_if.sv" \
  "${ROOT}/axi4_lite/examples/loopback/axi4_lite_loopback.sv" \
  "${ROOT}/axi4_lite/examples/loopback/tb.sv" -l compile.log
vsim -c -do "run -all; quit -f" tb | tee run.log
grep -q "AXI4-LITE LOOPBACK PASS" run.log
