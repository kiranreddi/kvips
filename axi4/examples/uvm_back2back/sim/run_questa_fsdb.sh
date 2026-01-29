#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../../../.." && pwd)"
OUT="${ROOT}/kvips/axi4/examples/uvm_back2back/sim/out/questa_fsdb"
mkdir -p "${OUT}"

cd "${ROOT}"
rm -rf work 2>/dev/null || true

if [[ -r /usr/share/Modules/init/bash ]]; then
  # shellcheck disable=SC1091
  source /usr/share/Modules/init/bash
fi

if command -v module >/dev/null 2>&1; then
  module load questa/2025_3_2 >/dev/null 2>&1 || true
  module load verdi/2023.03_sp2 >/dev/null 2>&1 || true
fi

if ! command -v vlog >/dev/null 2>&1; then
  echo "ERROR: 'vlog' not found on PATH (need Questa)."
  echo "Hint: 'module load questa/2025_3_2' (and run via ignrc/LSF if needed)."
  echo "PATH=${PATH}"
  exit 127
fi
if ! command -v vsim >/dev/null 2>&1; then
  echo "ERROR: 'vsim' not found on PATH (need Questa)."
  echo "Hint: 'module load questa/2025_3_2' (and run via ignrc/LSF if needed)."
  echo "PATH=${PATH}"
  exit 127
fi

find_novas_fli() {
  local base
  for base in "${NOVAS_HOME:-}" "${VERDI_HOME:-}" "/tools/synopsys/2023.03/verdi_sp2"; do
    [[ -n "${base}" && -d "${base}" ]] || continue
    # Common locations for the Questa/ModelSim PLI shim.
    if [[ -f "${base}/share/PLI/MODELSIM/linux64/novas_fli.so" ]]; then
      echo "${base}/share/PLI/MODELSIM/linux64/novas_fli.so"
      return 0
    fi
    if [[ -f "${base}/share/PLI/mti/linux64/novas_fli.so" ]]; then
      echo "${base}/share/PLI/mti/linux64/novas_fli.so"
      return 0
    fi
    if [[ -f "${base}/share/PLI/mti/Linux64/novas_fli.so" ]]; then
      echo "${base}/share/PLI/mti/Linux64/novas_fli.so"
      return 0
    fi
  done
  return 1
}

NOVAS_FLI=""
if NOVAS_FLI="$(find_novas_fli 2>/dev/null)"; then
  echo "INFO: Using FSDB PLI: ${NOVAS_FLI}" | tee "${OUT}/fsdb_pli.log"
else
  echo "ERROR: Could not find 'novas_fli.so' (Verdi/Novas PLI)." | tee "${OUT}/fsdb_pli.log"
  echo "Hint: ensure Verdi module is available in your ignrc/LSF environment." | tee -a "${OUT}/fsdb_pli.log"
  exit 2
fi

vlog -sv -f kvips/axi4/examples/uvm_back2back/sim/filelist.f +define+FSDB -l "${OUT}/compile.log"

EXTRA_ARGS=("$@" "+KVIPS_WAVES")
HAVE_TESTNAME=0
HAVE_VERBOSITY=0
for a in "${EXTRA_ARGS[@]}"; do
  [[ "$a" == +UVM_TESTNAME=* ]] && HAVE_TESTNAME=1
  [[ "$a" == +UVM_VERBOSITY=* ]] && HAVE_VERBOSITY=1
done
[[ "$HAVE_TESTNAME" -eq 0 ]] && EXTRA_ARGS+=("+UVM_TESTNAME=axi4_b2b_test")
[[ "$HAVE_VERBOSITY" -eq 0 ]] && EXTRA_ARGS+=("+UVM_VERBOSITY=UVM_LOW")

vsim -c top \
  -pli "${NOVAS_FLI}" \
  -do "run -all; quit -f" \
  "${EXTRA_ARGS[@]}" | tee "${OUT}/run.log"

if [[ -f "${ROOT}/kvips_axi4_b2b.fsdb" ]]; then
  mv -f "${ROOT}/kvips_axi4_b2b.fsdb" "${OUT}/kvips_axi4_b2b.fsdb"
  echo "WROTE: ${OUT}/kvips_axi4_b2b.fsdb"
fi

