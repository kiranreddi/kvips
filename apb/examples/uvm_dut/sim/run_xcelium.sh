#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../../.." && pwd)"
OUT="${ROOT}/apb/examples/uvm_dut/sim/out/xcelium"
ORIG_FILELIST="${ROOT}/apb/examples/uvm_dut/sim/filelist.f"
ABS_FILELIST="${OUT}/filelist.abs.f"
mkdir -p "${OUT}"

make_abs_filelist() {
  local in="$1" out="$2" line p
  : >"${out}"
  while IFS= read -r line || [[ -n "${line}" ]]; do
    case "${line}" in
      ""|\#*) printf '%s\n' "${line}" >>"${out}" ;;
      +incdir+*)
        p="${line#'+incdir+'}"
        [[ "${p}" = /* ]] && printf '%s\n' "${line}" >>"${out}" || printf '+incdir+%s\n' "${ROOT}/${p}" >>"${out}"
        ;;
      +*|-*) printf '%s\n' "${line}" >>"${out}" ;;
      *) [[ "${line}" = /* ]] && printf '%s\n' "${line}" >>"${out}" || printf '%s\n' "${ROOT}/${line}" >>"${out}" ;;
    esac
  done <"${in}"
}

[[ -f "${ORIG_FILELIST}" ]] || { echo "ERROR: missing filelist ${ORIG_FILELIST}" >&2; exit 2; }
cd "${OUT}"
if ! command -v xrun >/dev/null 2>&1; then
  [[ -r /usr/share/Modules/init/bash ]] && source /usr/share/Modules/init/bash
  command -v module >/dev/null 2>&1 && module load xcelium/25.03.007 >/dev/null 2>&1 || true
fi
command -v xrun >/dev/null 2>&1 || { echo "ERROR: Xcelium not found on PATH." >&2; exit 127; }

rm -rf xcelium.d xrun.* run.log waves shm
make_abs_filelist "${ORIG_FILELIST}" "${ABS_FILELIST}"
args=("$@")
has_test=0; has_verbosity=0
for arg in "${args[@]}"; do
  [[ "${arg}" == +UVM_TESTNAME=* ]] && has_test=1
  [[ "${arg}" == +UVM_VERBOSITY=* ]] && has_verbosity=1
done
[[ ${has_test} -eq 1 ]] || args+=(+UVM_TESTNAME=apb_dut_smoke_test)
[[ ${has_verbosity} -eq 1 ]] || args+=(+UVM_VERBOSITY=UVM_LOW)

xrun -64bit -sv -uvm -timescale 1ns/1ps -f "${ABS_FILELIST}" \
  -top tb_top -l run.log "${args[@]}"
