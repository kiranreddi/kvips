#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "${HERE}" && git rev-parse --show-toplevel)"
OUT="${ROOT}/apb/examples/uvm_real_design/sim/out/verilator"

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

SUMMARY_MD="${OUT}/summary.md"
{
  echo "# APB Real-Design Verilator Summary"
  echo ""
  echo "| Test | Status | wr | rd | err | mismatch |"
  echo "|---|---:|---:|---:|---:|---:|"
} >"${SUMMARY_MD}"

FIRST=1
for t in "${TESTS[@]}"; do
  echo "==== ${t} ===="
  status="PASS"
  if [[ "${FIRST}" -eq 1 ]]; then
    VERILATOR_REUSE_BUILD=0 "${HERE}/run_verilator.sh" +UVM_TESTNAME="${t}" "$@" || status="FAIL"
    FIRST=0
  else
    VERILATOR_REUSE_BUILD=1 "${HERE}/run_verilator.sh" +UVM_TESTNAME="${t}" "$@" || status="FAIL"
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
done

echo "DONE. See ${OUT}/run.log"
echo "Summary: ${SUMMARY_MD}"
