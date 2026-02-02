#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../../../.." && pwd)"
OUT="${ROOT}/kvips/pcie/examples/uvm_back2back/sim/out/vcs"
mkdir -p "${OUT}"

ORIG_FILELIST="${ROOT}/kvips/pcie/examples/uvm_back2back/sim/filelist.f"
ABS_FILELIST="${OUT}/filelist.abs.f"

make_abs_filelist() {
  local in="$1"
  local out="$2"
  : >"${out}"
  while IFS= read -r line || [[ -n "${line}" ]]; do
    case "${line}" in
      ""|\#*)
        printf '%s\n' "${line}" >>"${out}"
        ;;
      +incdir+*)
        p="${line#'+incdir+'}"
        if [[ "${p}" = /* ]]; then
          printf '%s\n' "${line}" >>"${out}"
        else
          printf '+incdir+%s\n' "${ROOT}/${p}" >>"${out}"
        fi
        ;;
      +*|-*)
        printf '%s\n' "${line}" >>"${out}"
        ;;
      *)
        if [[ "${line}" = /* ]]; then
          printf '%s\n' "${line}" >>"${out}"
        else
          printf '%s\n' "${ROOT}/${line}" >>"${out}"
        fi
        ;;
    esac
  done <"${in}"
}

if [[ ! -f "${ORIG_FILELIST}" ]]; then
  echo "ERROR: missing filelist: ${ORIG_FILELIST}"
  exit 2
fi
make_abs_filelist "${ORIG_FILELIST}" "${ABS_FILELIST}"

cd "${OUT}"

rm -rf simv* csrc ucli.key vc_hdrs.h 2>/dev/null || true

if ! command -v vcs >/dev/null 2>&1; then
  if [[ -r /usr/share/Modules/init/bash ]]; then
    # shellcheck disable=SC1091
    source /usr/share/Modules/init/bash
  fi
  if command -v module >/dev/null 2>&1; then
    module load vcs/2025.06_1 >/dev/null 2>&1 || true
  fi
fi
if ! command -v vcs >/dev/null 2>&1; then
  echo "ERROR: 'vcs' not found on PATH."
  echo "Hint: run on a node with VCS available (e.g. via LSF bsub) and load 'vcs/2025.06_1'."
  echo "PATH=${PATH}"
  exit 127
fi

VCS_EXTRA=()

# Optional FSDB (requires Verdi installation + VCS PLI files)
# Usage:
#   export KVIPS_FSDB=1
#   export VERDI_HOME=/path/to/verdi
#   ./run_vcs.sh +KVIPS_WAVES
if [[ "${KVIPS_FSDB:-0}" == "1" ]]; then
  if [[ -z "${VERDI_HOME:-}" && -d "/tools/synopsys/2023.03/verdi_sp2" ]]; then
    VERDI_HOME="/tools/synopsys/2023.03/verdi_sp2"
  fi
  if [[ -z "${VERDI_HOME:-}" ]]; then
    echo "ERROR: KVIPS_FSDB=1 requires VERDI_HOME (or a known install under /tools/synopsys/...)."
    exit 2
  fi
  TAB="${VERDI_HOME}/share/PLI/VCS/LINUX64/novas.tab"
  PLI="${VERDI_HOME}/share/PLI/VCS/LINUX64/pli.a"
  if [[ ! -f "${TAB}" || ! -f "${PLI}" ]]; then
    echo "ERROR: Verdi VCS PLI not found:"
    echo "  TAB=${TAB}"
    echo "  PLI=${PLI}"
    exit 2
  fi
  VCS_EXTRA+=("-P" "${TAB}" "${PLI}" "+define+FSDB")
fi

vcs -full64 -sverilog -timescale=1ns/1ps \
  -ntb_opts uvm-1.2 \
  "${VCS_EXTRA[@]}" \
  -f "${ABS_FILELIST}" \
  -Mdir=csrc \
  -o simv \
  -l "${OUT}/compile.log"

if [ ! -x "${OUT}/simv" ]; then
  echo "ERROR: simv not produced; see ${OUT}/compile.log"
  exit 2
fi

EXTRA_ARGS=("$@")
HAVE_TESTNAME=0
HAVE_VERBOSITY=0
for a in "${EXTRA_ARGS[@]}"; do
  [[ "$a" == +UVM_TESTNAME=* ]] && HAVE_TESTNAME=1
  [[ "$a" == +UVM_VERBOSITY=* ]] && HAVE_VERBOSITY=1
done
[[ "$HAVE_TESTNAME" -eq 0 ]] && EXTRA_ARGS+=("+UVM_TESTNAME=pcie_b2b_smoke_test")
[[ "$HAVE_VERBOSITY" -eq 0 ]] && EXTRA_ARGS+=("+UVM_VERBOSITY=UVM_LOW")

./simv "${EXTRA_ARGS[@]}" | tee "${OUT}/run.log"
