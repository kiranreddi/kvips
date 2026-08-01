#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "${HERE}" && git rev-parse --show-toplevel)"
OUT="${ROOT}/apb/examples/uvm_dut/sim/out/verilator"
mkdir -p "${OUT}"

TESTS_FILE="${HERE}/tests_questa.list"
if [[ ! -f "${TESTS_FILE}" ]]; then
  echo "ERROR: missing ${TESTS_FILE}"
  exit 2
fi

TESTS=()
while IFS= read -r t || [[ -n "${t}" ]]; do
  [[ -z "${t}" || "${t}" =~ ^[[:space:]]*# ]] && continue
  TESTS+=("${t}")
done <"${TESTS_FILE}"

if [[ "${#TESTS[@]}" -eq 0 ]]; then
  echo "ERROR: no tests found in ${TESTS_FILE}" >&2
  exit 2
fi

log_has_issue() {
  local log="$1"
  grep -Eq 'UVM/RELNOTES' "${log}" || \
    grep -Eq '^(%Warning|%Error)' "${log}" || \
    grep -Eq '^UVM_(WARNING|ERROR|FATAL)[[:space:]][^:]+@' "${log}" || \
    grep -Eq '^UVM_(WARNING|ERROR|FATAL)[[:space:]]*:[[:space:]]*[1-9]' "${log}"
}

SUMMARY_MD="${OUT}/summary.md"
{
  echo "# APB DUT-Design Verilator Summary"
  echo ""
  echo "| Test | Status | wr | rd | err | mismatch |"
  echo "|---|---:|---:|---:|---:|---:|"
} >"${SUMMARY_MD}"

FIRST=1
for t in "${TESTS[@]}"; do
  echo "==== ${t} ===="
  status="PASS"
  LOG="${OUT}/${t}.log"
  if [[ "${FIRST}" -eq 1 ]]; then
    VERILATOR_REUSE_BUILD=0 "${HERE}/run_verilator.sh" +UVM_TESTNAME="${t}" "$@" || status="FAIL"
    FIRST=0
  else
    VERILATOR_REUSE_BUILD=1 "${HERE}/run_verilator.sh" +UVM_TESTNAME="${t}" "$@" || status="FAIL"
  fi
  [[ -f "${OUT}/run.log" ]] && cp -f "${OUT}/run.log" "${LOG}"
  if [[ -f "${OUT}/compile.log" ]] && log_has_issue "${OUT}/compile.log"; then
    status="FAIL"
  fi
  if log_has_issue "${LOG}"; then
    status="FAIL"
  fi
  sb_line="$(grep -E "APB SB summary:" "${OUT}/run.log" | tail -n1 || true)"
  dut_line="$(grep -E "APB_DUT_SUMMARY" "${OUT}/run.log" | tail -n1 || true)"
  wr="$(echo "${sb_line}" | sed -n 's/.*wr=\([0-9]\+\).*/\1/p')"
  rd="$(echo "${sb_line}" | sed -n 's/.*rd=\([0-9]\+\).*/\1/p')"
  err="$(echo "${sb_line}" | sed -n 's/.*err=\([0-9]\+\).*/\1/p')"
  mis="$(echo "${sb_line}" | sed -n 's/.*mismatch=\([0-9]\+\).*/\1/p')"
  [[ -z "${wr}" ]] && wr="NA"
  [[ -z "${rd}" ]] && rd="NA"
  [[ -z "${err}" ]] && err="NA"
  [[ -z "${mis}" ]] && mis="NA"
  if [[ "${wr}" == "0" || -z "${wr}" ]]; then
    wr_fallback="$(echo "${dut_line}" | sed -n 's/.*wr=\([0-9]\+\).*/\1/p')"
    [[ -n "${wr_fallback}" ]] && wr="${wr_fallback}"
  fi
  if [[ "${rd}" == "0" || -z "${rd}" ]]; then
    rd_fallback="$(echo "${dut_line}" | sed -n 's/.*rd=\([0-9]\+\).*/\1/p')"
    [[ -n "${rd_fallback}" ]] && rd="${rd_fallback}"
  fi
  echo "| ${t} | ${status} | ${wr} | ${rd} | ${err} | ${mis} |" >> "${SUMMARY_MD}"
  if [[ "${status}" == "FAIL" ]]; then
    echo "FAIL: ${t}"
    exit 1
  else
    echo "PASS: ${t}"
  fi
done

echo "DONE. See ${OUT}/run.log"
echo "Summary: ${SUMMARY_MD}"
