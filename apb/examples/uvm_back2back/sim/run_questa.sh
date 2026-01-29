#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../../../.." && pwd)"
OUT="${ROOT}/kvips/apb/examples/uvm_back2back/sim/out/questa"
mkdir -p "${OUT}"

ORIG_FILELIST="${ROOT}/kvips/apb/examples/uvm_back2back/sim/filelist.f"
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

cd "${OUT}"

if ! command -v vsim >/dev/null 2>&1; then
  if [[ -r /usr/share/Modules/init/bash ]]; then
    # shellcheck disable=SC1091
    source /usr/share/Modules/init/bash
  fi
  if command -v module >/dev/null 2>&1; then
    module load questa/2025_3_2 >/dev/null 2>&1 || true
  fi
fi
if ! command -v vlib >/dev/null 2>&1; then
  echo "ERROR: Questa not found on PATH."
  exit 127
fi

rm -rf work transcript vsim.wlf *.log 2>/dev/null || true
vlib work

make_abs_filelist "${ORIG_FILELIST}" "${ABS_FILELIST}"
vlog -sv -timescale 1ns/1ps -f "${ABS_FILELIST}" -l compile.log

EXTRA_ARGS=("$@")
HAVE_TESTNAME=0
HAVE_VERBOSITY=0
for a in "${EXTRA_ARGS[@]}"; do
  [[ "$a" == +UVM_TESTNAME=* ]] && HAVE_TESTNAME=1
  [[ "$a" == +UVM_VERBOSITY=* ]] && HAVE_VERBOSITY=1
done
[[ "$HAVE_TESTNAME" -eq 0 ]] && EXTRA_ARGS+=("+UVM_TESTNAME=apb_b2b_smoke_test")
[[ "$HAVE_VERBOSITY" -eq 0 ]] && EXTRA_ARGS+=("+UVM_VERBOSITY=UVM_LOW")

vsim -c -uvmcontrol=all -do "run -all; quit -f" tb_top "${EXTRA_ARGS[@]}" | tee run.log
