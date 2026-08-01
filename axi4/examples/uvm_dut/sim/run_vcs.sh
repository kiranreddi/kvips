#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../../.." && pwd)"
OUT="${ROOT}/axi4/examples/uvm_dut/sim/out/vcs"
mkdir -p "${OUT}"
FILELIST="${ROOT}/axi4/examples/uvm_dut/sim/filelist.f"
ABS_FILELIST="${OUT}/filelist.abs.f"

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

make_abs_filelist "${FILELIST}" "${ABS_FILELIST}"
if ! command -v vcs >/dev/null 2>&1; then
  module load vcs/2025.06_1 >/dev/null 2>&1 || true
fi
if ! command -v vcs >/dev/null 2>&1; then
  echo "ERROR: VCS is unavailable; run on a node with vcs/2025.06_1 loaded." >&2
  exit 127
fi

cd "${OUT}"
if [[ "${KVIPS_REUSE_BUILD:-0}" != "1" || ! -x simv ]]; then
  rm -rf simv csrc ucli.key vc_hdrs.h
  vcs -full64 -sverilog -timescale=1ns/1ps -ntb_opts uvm-1.2 -f "${ABS_FILELIST}" -Mdir=csrc -o simv -l "${OUT}/compile.log"
fi

args=("$@")
has_test=0
has_verbosity=0
for arg in "${args[@]}"; do
  [[ "${arg}" == +UVM_TESTNAME=* ]] && has_test=1
  [[ "${arg}" == +UVM_VERBOSITY=* ]] && has_verbosity=1
done
[[ ${has_test} -eq 1 ]] || args+=(+UVM_TESTNAME=axi4_dut_smoke_test)
[[ ${has_verbosity} -eq 1 ]] || args+=(+UVM_VERBOSITY=UVM_LOW)
./simv "${args[@]}" | tee "${OUT}/run.log"
