#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "${HERE}" && git rev-parse --show-toplevel)"
OUT="${ROOT}/ahb/examples/uvm_back2back/sim/out/verilator"
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

FIRST=1
for t in "${TESTS[@]}"; do
  echo "==== ${t} ===="
  LOG="${OUT}/${t}.log"
  TEST_PLUSARGS=("$@")
  # The Full-mode tests configure the UVM agents directly, but the
  # interface-bound assertions select their legality rules from this runtime
  # plusarg.  Keep the two views in sync, as the commercial regressions do.
  case "${t}" in
    ahb_full_retry_test|ahb_full_split_test)
      TEST_PLUSARGS+=("+AHB_MODE=AHB_FULL")
      ;;
  esac
  if [[ "${FIRST}" -eq 1 ]]; then
    VERILATOR_REUSE_BUILD=0 "${HERE}/run_verilator.sh" +UVM_TESTNAME="${t}" "${TEST_PLUSARGS[@]}"
    FIRST=0
  else
    VERILATOR_REUSE_BUILD=1 "${HERE}/run_verilator.sh" +UVM_TESTNAME="${t}" "${TEST_PLUSARGS[@]}"
  fi
  [[ -f "${OUT}/run.log" ]] && cp -f "${OUT}/run.log" "${LOG}"
  if [[ -f "${OUT}/compile.log" ]] && log_has_issue "${OUT}/compile.log"; then
    echo "FAIL: ${t}"
    exit 1
  fi
  if log_has_issue "${LOG}"; then
    echo "FAIL: ${t}"
    exit 1
  else
    echo "PASS: ${t}"
  fi
done

echo "DONE. See ${OUT}/run.log"
