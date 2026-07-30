#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "${HERE}/../../../.." && pwd)"
OUT="${HERE}/out/vcs"
mkdir -p "${OUT}"

if [[ -r /usr/share/Modules/init/bash ]]; then
  # shellcheck disable=SC1091
  source /usr/share/Modules/init/bash
fi
if ! command -v vcs >/dev/null 2>&1 && command -v module >/dev/null 2>&1; then
  module load vcs/2025.06_1 >/dev/null 2>&1 || true
fi
command -v vcs >/dev/null 2>&1 || { echo "ERROR: VCS not found" >&2; exit 127; }

cd "${OUT}"
rm -rf simv csrc simv.daidir ucli.key compile.log run.log
vcs -full64 -sverilog -timescale=1ns/1ps \
  "${ROOT}/axi4_lite/sv/if/axi4_lite_if.sv" \
  "${ROOT}/axi4_lite/examples/loopback/axi4_lite_loopback.sv" \
  "${ROOT}/axi4_lite/examples/loopback/tb.sv" \
  -top tb -o simv -l compile.log
./simv | tee run.log
grep -q "AXI4-LITE LOOPBACK PASS" run.log
