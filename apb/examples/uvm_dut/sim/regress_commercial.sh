#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../../.." && pwd)"
SIM_DIR="${ROOT}/apb/examples/uvm_dut/sim"
TESTLIST="${SIM_DIR}/tests_questa.list"
sim="${1:-}"
case "${sim}" in
  questa) runner="${SIM_DIR}/run_questa.sh" ;;
  vcs) runner="${SIM_DIR}/run_vcs.sh" ;;
  xcelium) runner="${SIM_DIR}/run_xcelium.sh" ;;
  *) echo "usage: $0 {questa|vcs|xcelium} [plusargs...]" >&2; exit 2 ;;
esac
shift

out="${SIM_DIR}/out/${sim}"
mkdir -p "${out}"
summary="${out}/regress.log"
: >"${summary}"
status=0
first=1

while IFS= read -r test_name || [[ -n "${test_name}" ]]; do
  [[ -z "${test_name}" || "${test_name}" == \#* ]] && continue
  echo "=== ${sim}: ${test_name} ===" | tee -a "${summary}"
  if [[ "${first}" -eq 1 || "${sim}" == "xcelium" ]]; then
    runner_args=("${runner}" +UVM_TESTNAME="${test_name}")
    first=0
  else
    runner_args=(env KVIPS_REUSE_BUILD=1 "${runner}" +UVM_TESTNAME="${test_name}")
  fi

  if "${runner_args[@]}" "$@"; then
    log="${out}/run.log"
    test_log="${out}/${test_name}.log"
    cp -f "${log}" "${test_log}"
    mon_line="$(rg 'APB summary: wr=' "${test_log}" | tail -n1 || true)"
    sb_line="$(rg 'APB SB summary:' "${test_log}" | tail -n1 || true)"
    wr="$(sed -n 's/.*APB summary: wr=\([0-9][0-9]*\).*/\1/p' <<<"${mon_line}")"
    rd="$(sed -n 's/.*APB summary: wr=[0-9][0-9]* rd=\([0-9][0-9]*\).*/\1/p' <<<"${mon_line}")"
    err="$(sed -n 's/.*APB summary: wr=[0-9][0-9]* rd=[0-9][0-9]* err=\([0-9][0-9]*\).*/\1/p' <<<"${mon_line}")"
    sb_wr="$(sed -n 's/.*wr=\([0-9][0-9]*\).*/\1/p' <<<"${sb_line}")"
    sb_rd="$(sed -n 's/.*rd=\([0-9][0-9]*\).*/\1/p' <<<"${sb_line}")"
    mismatch="$(sed -n 's/.*mismatch=\([0-9][0-9]*\).*/\1/p' <<<"${sb_line}")"
    wr="${wr:-0}"; rd="${rd:-0}"; err="${err:-0}"
    sb_wr="${sb_wr:-0}"; sb_rd="${sb_rd:-0}"; mismatch="${mismatch:-1}"
    expected_err=0
    [[ "${test_name}" == "apb_dut_error_test" ]] && expected_err=1
    bad=0
    [[ -z "${mon_line}" || -z "${sb_line}" ]] && bad=1
    [[ "${wr}" -eq 0 || "${rd}" -eq 0 || "${sb_wr}" -eq 0 || "${sb_rd}" -eq 0 ]] && bad=1
    [[ "${mismatch}" -ne 0 ]] && bad=1
    if [[ "${expected_err}" -eq 1 ]]; then
      [[ "${err}" -eq 0 ]] && bad=1
    else
      [[ "${err}" -ne 0 ]] && bad=1
    fi
    if rg -q 'UVM_(ERROR|FATAL)[^:]*@|UVM_(ERROR|FATAL)[[:space:]]*:[[:space:]]*[1-9]|(\# \*\* (Error|Fatal):|Error-\[|\*E,|\*F,)' "${test_log}"; then
      bad=1
    fi
    if [[ "${bad}" -ne 0 ]]; then
      echo "FAIL ${test_name}: missing/nonzero APB or scoreboard evidence" | tee -a "${summary}"
      status=1
    else
      echo "PASS ${test_name} wr=${wr} rd=${rd} err=${err} sb_wr=${sb_wr} sb_rd=${sb_rd} mismatch=${mismatch}" | tee -a "${summary}"
    fi
  else
    echo "FAIL ${test_name}: simulator returned non-zero" | tee -a "${summary}"
    status=1
  fi
done <"${TESTLIST}"
exit "${status}"
