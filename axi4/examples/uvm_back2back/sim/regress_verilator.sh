#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../../../.." && pwd)"
SIM_DIR="${ROOT}/kvips/axi4/examples/uvm_back2back/sim"
OUT_DIR="${SIM_DIR}/out/verilator"
TESTLIST="${SIM_DIR}/tests_questa.list"

if [[ ! -f "${TESTLIST}" ]]; then
  echo "ERROR: missing test list: ${TESTLIST}" >&2
  exit 2
fi

mkdir -p "${OUT_DIR}"

REGRESS_LOG="${OUT_DIR}/regress.log"
: >"${REGRESS_LOG}"

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
    if grep -Eq "^UVM_(FATAL|ERROR) @" "${OUT_DIR}/${test_name}.log" || \
      grep -Eq "^%Error" "${OUT_DIR}/${test_name}.log"; then
    echo "FAIL: ${test_name}" | tee -a "${REGRESS_LOG}"
  else
    echo "PASS: ${test_name}" | tee -a "${REGRESS_LOG}"
  fi
  echo "" >>"${REGRESS_LOG}"
done <"${TESTLIST}"
