#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && git rev-parse --show-toplevel)"
SIM_DIR="${ROOT}/axi4/examples/uvm_real_design/sim"
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
  echo "# AXI4 Real-Design Verilator Summary"
  echo ""
  echo "| Test | Status | wr_txns | rd_txns | wr_err | rd_mismatch_beats | rd_uninit_warn_beats |"
  echo "|---|---:|---:|---:|---:|---:|---:|"
} >"${SUMMARY_MD}"

export VERILATOR_REUSE_BUILD=1

while IFS= read -r line || [[ -n "${line}" ]]; do
  case "${line}" in
    ""|\#*)
      continue
      ;;
  esac
  test_name="$(echo "${line}" | awk '{print $1}')"
  [[ -z "${test_name}" ]] && continue
  echo "=== Running ${test_name} ===" | tee -a "${REGRESS_LOG}"
  "${SIM_DIR}/run_verilator.sh" +UVM_TESTNAME="${test_name}" | tee "${OUT_DIR}/${test_name}.log"
  status="PASS"
  if grep -Eq "^UVM_(FATAL|ERROR) @" "${OUT_DIR}/${test_name}.log" || \
      grep -Eq "^%Error" "${OUT_DIR}/${test_name}.log"; then
    echo "FAIL: ${test_name}" | tee -a "${REGRESS_LOG}"
    status="FAIL"
  else
    echo "PASS: ${test_name}" | tee -a "${REGRESS_LOG}"
  fi
  sb_line="$(grep -E "AXI4 SB summary:" "${OUT_DIR}/${test_name}.log" | tail -n1 || true)"
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
  echo "| ${test_name} | ${status} | ${wr_txns} | ${rd_txns} | ${wr_err} | ${rd_mis} | ${rd_uninit} |" >> "${SUMMARY_MD}"
  echo "" >>"${REGRESS_LOG}"
done <"${TESTLIST}"
echo "Summary: ${SUMMARY_MD}" | tee -a "${REGRESS_LOG}"
