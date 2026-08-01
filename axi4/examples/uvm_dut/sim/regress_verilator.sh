#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && git rev-parse --show-toplevel)"
SIM_DIR="${ROOT}/axi4/examples/uvm_dut/sim"
OUT_DIR="${SIM_DIR}/out/verilator"
TESTLIST="${SIM_DIR}/tests_questa.list"

if [[ ! -f "${TESTLIST}" ]]; then
  echo "ERROR: missing test list: ${TESTLIST}" >&2
  exit 2
fi

mkdir -p "${OUT_DIR}"

REGRESS_LOG="${OUT_DIR}/regress.log"
: >"${REGRESS_LOG}"
SUMMARY_MD="${OUT_DIR}/summary.md"
{
  echo "# AXI4 DUT-Design Verilator Summary"
  echo ""
  echo "| Test | Status | wr_txns | rd_txns | wr_err | rd_mismatch_beats | rd_uninit_warn_beats |"
  echo "|---|---:|---:|---:|---:|---:|---:|"
} >"${SUMMARY_MD}"

log_has_issue() {
  local log="$1"
  grep -Eq 'UVM/RELNOTES' "${log}" || \
    grep -Eq '^(%Warning|%Error)' "${log}" || \
    grep -Eq '^UVM_(WARNING|ERROR|FATAL)[[:space:]][^:]+@' "${log}" || \
    grep -Eq '^UVM_(WARNING|ERROR|FATAL)[[:space:]]*:[[:space:]]*[1-9]' "${log}"
}

FIRST=1
while IFS= read -r line || [[ -n "${line}" ]]; do
  case "${line}" in
    ""|\#*)
      continue
      ;;
  esac
  test_name="$(echo "${line}" | awk '{print $1}')"
  [[ -z "${test_name}" ]] && continue
  echo "=== Running ${test_name} ===" | tee -a "${REGRESS_LOG}"
  if [[ "${FIRST}" -eq 1 ]]; then
    VERILATOR_REUSE_BUILD=0 "${SIM_DIR}/run_verilator.sh" +UVM_TESTNAME="${test_name}"
    FIRST=0
  else
    VERILATOR_REUSE_BUILD=1 "${SIM_DIR}/run_verilator.sh" +UVM_TESTNAME="${test_name}"
  fi
  [[ -f "${OUT_DIR}/run.log" ]] && cp -f "${OUT_DIR}/run.log" "${OUT_DIR}/${test_name}.log"
  status="PASS"
  if [[ -f "${OUT_DIR}/compile.log" ]] && log_has_issue "${OUT_DIR}/compile.log"; then
    echo "FAIL: ${test_name} (compile.log has Warning/Error)" | tee -a "${REGRESS_LOG}"
    status="FAIL"
  elif log_has_issue "${OUT_DIR}/${test_name}.log"; then
    echo "FAIL: ${test_name}" | tee -a "${REGRESS_LOG}"
    status="FAIL"
  else
    echo "PASS: ${test_name}" | tee -a "${REGRESS_LOG}"
  fi
  sb_line="$(grep -E "AXI4 SB summary:" "${OUT_DIR}/${test_name}.log" | tail -n1 || true)"
  dut_line="$(grep -E "AXI4_DUT_SUMMARY" "${OUT_DIR}/${test_name}.log" | tail -n1 || true)"
  wr_txns="$(echo "${sb_line}" | sed -n 's/.*wr_txns=\([0-9]\+\).*/\1/p')"
  rd_txns="$(echo "${sb_line}" | sed -n 's/.*rd_txns=\([0-9]\+\).*/\1/p')"
  wr_err="$(echo "${sb_line}" | sed -n 's/.*wr_err=\([0-9]\+\).*/\1/p')"
  rd_mis="$(echo "${sb_line}" | sed -n 's/.*rd_mismatch_beats=\([0-9]\+\).*/\1/p')"
  rd_uninit="$(echo "${sb_line}" | sed -n 's/.*rd_uninit_warn_beats=\([0-9]\+\).*/\1/p')"
  [[ -z "${wr_txns}" ]] && wr_txns="NA"
  [[ -z "${rd_txns}" ]] && rd_txns="NA"
  [[ -z "${wr_err}" ]] && wr_err="NA"
  [[ -z "${rd_mis}" ]] && rd_mis="NA"
  [[ -z "${rd_uninit}" ]] && rd_uninit="NA"
  if [[ "${wr_txns}" == "0" || -z "${wr_txns}" ]]; then
    wr_fallback="$(echo "${dut_line}" | sed -n 's/.*wr_txns=\([0-9]\+\).*/\1/p')"
    [[ -n "${wr_fallback}" ]] && wr_txns="${wr_fallback}"
  fi
  if [[ "${rd_txns}" == "0" || -z "${rd_txns}" ]]; then
    rd_fallback="$(echo "${dut_line}" | sed -n 's/.*rd_txns=\([0-9]\+\).*/\1/p')"
    [[ -n "${rd_fallback}" ]] && rd_txns="${rd_fallback}"
  fi
  echo "| ${test_name} | ${status} | ${wr_txns} | ${rd_txns} | ${wr_err} | ${rd_mis} | ${rd_uninit} |" >> "${SUMMARY_MD}"
  if [[ "${status}" == "FAIL" ]]; then
    exit 1
  fi
  echo "" >>"${REGRESS_LOG}"
done <"${TESTLIST}"
echo "Summary: ${SUMMARY_MD}" | tee -a "${REGRESS_LOG}"
