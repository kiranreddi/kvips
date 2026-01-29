#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../../../.." && pwd)"
OUT="${ROOT}/kvips/axi4/examples/uvm_back2back/sim/out/xcelium"
mkdir -p "${OUT}"

cd "${ROOT}"

if ! command -v xrun >/dev/null 2>&1; then
  if [[ -r /usr/share/Modules/init/bash ]]; then
    # shellcheck disable=SC1091
    source /usr/share/Modules/init/bash
  fi
  if command -v module >/dev/null 2>&1; then
    module load xcelium/25.03.007 >/dev/null 2>&1 || true
  fi
fi
if ! command -v xrun >/dev/null 2>&1; then
  echo "ERROR: 'xrun' not found on PATH."
  echo "Hint: run on a node with Xcelium available (e.g. via ignrc/LSF) and load 'xcelium/25.03.007'."
  echo "PATH=${PATH}"
  exit 127
fi

EXTRA_ARGS=("$@")
HAVE_TESTNAME=0
HAVE_VERBOSITY=0
for a in "${EXTRA_ARGS[@]}"; do
  [[ "$a" == +UVM_TESTNAME=* ]] && HAVE_TESTNAME=1
  [[ "$a" == +UVM_VERBOSITY=* ]] && HAVE_VERBOSITY=1
done
[[ "$HAVE_TESTNAME" -eq 0 ]] && EXTRA_ARGS+=("+UVM_TESTNAME=axi4_b2b_test")
[[ "$HAVE_VERBOSITY" -eq 0 ]] && EXTRA_ARGS+=("+UVM_VERBOSITY=UVM_LOW")

xrun -64bit -sv -timescale 1ns/1ps \
  -f kvips/axi4/examples/uvm_back2back/sim/filelist.f \
  -uvm \
  -access +rwc \
  -l "${OUT}/xrun.log" \
  "${EXTRA_ARGS[@]}"
