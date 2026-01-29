#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../../../.." && pwd)"
OUT="${ROOT}/kvips/axi4/examples/uvm_back2back/sim/out/questa"
mkdir -p "${OUT}"

cd "${ROOT}"

rm -rf work 2>/dev/null || true

if ! command -v vlog >/dev/null 2>&1; then
  echo "ERROR: 'vlog' not found on PATH."
  echo "Hint: load Questa module (e.g. 'module load questa/2025_3_2') and ensure \$QUESTA_HOME/bin is accessible."
  echo "PATH=${PATH}"
  exit 127
fi
if ! command -v vsim >/dev/null 2>&1; then
  echo "ERROR: 'vsim' not found on PATH."
  echo "Hint: load Questa module (e.g. 'module load questa/2025_3_2') and ensure \$QUESTA_HOME/bin is accessible."
  echo "PATH=${PATH}"
  exit 127
fi

vlog -sv -f kvips/axi4/examples/uvm_back2back/sim/filelist.f -l "${OUT}/compile.log"

EXTRA_ARGS=("$@")
HAVE_TESTNAME=0
HAVE_VERBOSITY=0
for a in "${EXTRA_ARGS[@]}"; do
  [[ "$a" == +UVM_TESTNAME=* ]] && HAVE_TESTNAME=1
  [[ "$a" == +UVM_VERBOSITY=* ]] && HAVE_VERBOSITY=1
done
[[ "$HAVE_TESTNAME" -eq 0 ]] && EXTRA_ARGS+=("+UVM_TESTNAME=axi4_b2b_test")
[[ "$HAVE_VERBOSITY" -eq 0 ]] && EXTRA_ARGS+=("+UVM_VERBOSITY=UVM_LOW")

vsim -c top \
  -do "run -all; quit -f" \
  "${EXTRA_ARGS[@]}" | tee "${OUT}/run.log"
