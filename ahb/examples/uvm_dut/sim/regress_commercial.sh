#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../../.." && pwd)"
SIM_DIR="${ROOT}/ahb/examples/uvm_dut/sim"
TESTLIST="${SIM_DIR}/tests_questa.list"
sim="${1:-}"
case "${sim}" in
  questa) runner="${SIM_DIR}/run_questa.sh"; log_name=run.log ;;
  vcs) runner="${SIM_DIR}/run_vcs.sh"; log_name=run.log ;;
  xcelium) runner="${SIM_DIR}/run_xcelium.sh"; log_name=xrun.log ;;
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
  test_plusargs=("$@")
  [[ "${test_name}" == ahb_dut_full_mode_test ]] && test_plusargs+=(+AHB_MODE=AHB_FULL)
  if [[ "${first}" -eq 1 ]]; then
    runner_args=("${runner}" +UVM_TESTNAME="${test_name}")
    first=0
  else
    runner_args=(env KVIPS_REUSE_BUILD=1 "${runner}" +UVM_TESTNAME="${test_name}")
  fi
  if "${runner_args[@]}" "${test_plusargs[@]}"; then
    test_log="${out}/${test_name}.log"
    cp -f "${out}/${log_name}" "${test_log}"
    sb_line="$(grep -E 'AHB SB summary:' "${test_log}" | tail -n1 || true)"
    log_line="$(grep -E 'AHB log summary:' "${test_log}" | tail -n1 || true)"
    wr="$(sed -n 's/.* wr=\([0-9][0-9]*\).*/\1/p' <<<"${sb_line}")"
    rd="$(sed -n 's/.* rd=\([0-9][0-9]*\).*/\1/p' <<<"${sb_line}")"
    err="$(sed -n 's/.* err=\([0-9][0-9]*\).*/\1/p' <<<"${sb_line}")"
    mis="$(sed -n 's/.* mismatch=\([0-9][0-9]*\).*/\1/p' <<<"${sb_line}")"
    stalls="$(sed -n 's/.* stall_cycles=\([0-9][0-9]*\).*/\1/p' <<<"${log_line}")"
    wr="${wr:-0}"; rd="${rd:-0}"; err="${err:-1}"; mis="${mis:-1}"; stalls="${stalls:-0}"
    if [[ -z "${sb_line}" || -z "${log_line}" || "${wr}" -eq 0 || "${rd}" -eq 0 || "${err}" -ne 0 || "${mis}" -ne 0 ]]; then
      echo "FAIL ${test_name}: missing/nonzero DUT scoreboard evidence" | tee -a "${summary}"
      status=1
    elif [[ "${test_name}" == ahb_dut_wait_state_test && "${stalls}" -eq 0 ]]; then
      echo "FAIL ${test_name}: no wait-state evidence" | tee -a "${summary}"
      status=1
    elif grep -Eq 'UVM_(ERROR|FATAL)[^:]*@|UVM_(ERROR|FATAL)[[:space:]]*:[[:space:]]*[1-9]' "${test_log}"; then
      echo "FAIL ${test_name}: UVM error/fatal found" | tee -a "${summary}"
      status=1
    else
      echo "PASS ${test_name} wr=${wr} rd=${rd} stall_cycles=${stalls}" | tee -a "${summary}"
    fi
  else
    echo "FAIL ${test_name}: simulator returned non-zero" | tee -a "${summary}"
    status=1
  fi
done <"${TESTLIST}"
exit "${status}"
