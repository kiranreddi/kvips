#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../../.." && pwd)"
OUT="${ROOT}/ahb/examples/uvm_dut/sim/out/questa"
FILELIST="${ROOT}/ahb/examples/uvm_dut/sim/filelist.f"
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

[[ -f "${FILELIST}" ]] || { echo "ERROR: missing filelist ${FILELIST}" >&2; exit 2; }
if ! command -v vlog >/dev/null 2>&1; then
  module load questa/2025_3_2 >/dev/null 2>&1 || true
fi
command -v vlog >/dev/null 2>&1 && command -v vsim >/dev/null 2>&1 || {
  echo "ERROR: Questa vlog/vsim is unavailable; load questa/2025_3_2." >&2; exit 127;
}
make_abs_filelist "${FILELIST}" "${ABS_FILELIST}"
cd "${OUT}"
if [[ "${KVIPS_REUSE_BUILD:-0}" != "1" || ! -d work ]]; then
  rm -rf work modelsim.ini transcript vsim.wlf
  vlib work
  vmap work work
  vlog -sv -timescale 1ns/1ps -f "${ABS_FILELIST}" -l compile.log
fi
args=("$@")
has_test=0; has_verbosity=0
for arg in "${args[@]}"; do
  [[ "${arg}" == +UVM_TESTNAME=* ]] && has_test=1
  [[ "${arg}" == +UVM_VERBOSITY=* ]] && has_verbosity=1
done
[[ ${has_test} -eq 1 ]] || args+=(+UVM_TESTNAME=ahb_dut_smoke_test)
[[ ${has_verbosity} -eq 1 ]] || args+=(+UVM_VERBOSITY=UVM_LOW)
vsim -c top -do "run -all; quit -f" "${args[@]}" | tee run.log
