#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../../.." && pwd)"
SIM_DIR="${ROOT}/axi4/examples/uvm_dut/sim"
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
  if [[ "${first}" -eq 1 ]]; then
    runner_args=("${runner}" +UVM_TESTNAME="${test_name}")
    first=0
  else
    runner_args=(env KVIPS_REUSE_BUILD=1 "${runner}" +UVM_TESTNAME="${test_name}")
  fi
  if "${runner_args[@]}" "$@"; then
    log="${out}/run.log"
    [[ "${sim}" == "xcelium" ]] && log="${out}/xrun.log"
    test_log="${out}/${test_name}.log"
    cp -f "${log}" "${test_log}"
    chk_line="$(rg 'AXI4_CHK.*AW=' "${test_log}" | tail -n1 || true)"
    sb_line="$(rg 'AXI4 SB summary:' "${test_log}" | tail -n1 || true)"
    aw="$(sed -n 's/.*AW=\([0-9][0-9]*\).*/\1/p' <<<"${chk_line}")"
    w="$(sed -n 's/.* W=\([0-9][0-9]*\).*/\1/p' <<<"${chk_line}")"
    b="$(sed -n 's/.* B=\([0-9][0-9]*\).*/\1/p' <<<"${chk_line}")"
    ar="$(sed -n 's/.* AR=\([0-9][0-9]*\).*/\1/p' <<<"${chk_line}")"
    r="$(sed -n 's/.* R=\([0-9][0-9]*\).*/\1/p' <<<"${chk_line}")"
    chk_errors="$(sed -n 's/.* errors=\([0-9][0-9]*\).*/\1/p' <<<"${chk_line}")"
    sideband_errors="$(sed -n 's/.* sideband_errors=\([0-9][0-9]*\).*/\1/p' <<<"${chk_line}")"
    wr_txns="$(sed -n 's/.*wr_txns=\([0-9][0-9]*\).*/\1/p' <<<"${sb_line}")"
    rd_txns="$(sed -n 's/.*rd_txns=\([0-9][0-9]*\).*/\1/p' <<<"${sb_line}")"
    rd_mismatch="$(sed -n 's/.*rd_mismatch_beats=\([0-9][0-9]*\).*/\1/p' <<<"${sb_line}")"
    aw="${aw:-0}"; w="${w:-0}"; b="${b:-0}"; ar="${ar:-0}"; r="${r:-0}"
    chk_errors="${chk_errors:-1}"; sideband_errors="${sideband_errors:-1}"
    wr_txns="${wr_txns:-0}"; rd_txns="${rd_txns:-0}"; rd_mismatch="${rd_mismatch:-1}"
    if [[ -z "${chk_line}" || -z "${sb_line}" || -z "${aw}" || -z "${ar}" ||
          "${aw}" -eq 0 || "${w}" -eq 0 || "${b}" -eq 0 || "${ar}" -eq 0 || "${r}" -eq 0 ||
          "${chk_errors}" -ne 0 || "${sideband_errors}" -ne 0 ||
          -z "${wr_txns}" || -z "${rd_txns}" || "${wr_txns}" -eq 0 || "${rd_txns}" -eq 0 ||
          "${rd_mismatch}" -ne 0 ]]; then
      echo "FAIL ${test_name}: missing/nonzero protocol or scoreboard evidence" | tee -a "${summary}"
      status=1
    elif rg -q 'UVM_(ERROR|FATAL)[^:]*@|UVM_(ERROR|FATAL)[[:space:]]*:[[:space:]]*[1-9]' "${test_log}"; then
      echo "FAIL ${test_name}: UVM error/fatal found" | tee -a "${summary}"
      status=1
    else
      echo "PASS ${test_name} AW=${aw} W=${w} B=${b} AR=${ar} R=${r} wr=${wr_txns} rd=${rd_txns}" | tee -a "${summary}"
    fi
  else
    echo "FAIL ${test_name}: simulator returned non-zero" | tee -a "${summary}"
    status=1
  fi
done <"${TESTLIST}"
exit "${status}"
