#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && git rev-parse --show-toplevel)"
SIM_DIR="${ROOT}/axi4/examples/uvm_back2back/sim"
OUT_DIR="${SIM_DIR}/out/verilator"
TESTLIST="${SIM_DIR}/tests_questa.list"

if [[ ! -f "${TESTLIST}" ]]; then
  echo "ERROR: missing test list: ${TESTLIST}" >&2
  exit 2
fi

mkdir -p "${OUT_DIR}"

REGRESS_LOG="${OUT_DIR}/regress.log"
: >"${REGRESS_LOG}"

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
  if [[ -f "${OUT_DIR}/compile.log" ]] && log_has_issue "${OUT_DIR}/compile.log"; then
    echo "FAIL: ${test_name}" | tee -a "${REGRESS_LOG}"
    exit 1
  fi
  if log_has_issue "${OUT_DIR}/${test_name}.log"; then
    echo "FAIL: ${test_name}" | tee -a "${REGRESS_LOG}"
    exit 1
  else
    echo "PASS: ${test_name}" | tee -a "${REGRESS_LOG}"
  fi
  echo "" >>"${REGRESS_LOG}"
done <"${TESTLIST}"
