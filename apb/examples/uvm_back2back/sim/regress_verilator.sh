#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "${HERE}" && git rev-parse --show-toplevel)"
OUT="${ROOT}/apb/examples/uvm_back2back/sim/out/verilator"

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

FIRST=1
for t in "${TESTS[@]}"; do
  echo "==== ${t} ===="
  if [[ "${FIRST}" -eq 1 ]]; then
    VERILATOR_REUSE_BUILD=0 "${HERE}/run_verilator.sh" +UVM_TESTNAME="${t}" "$@"
    FIRST=0
  else
    VERILATOR_REUSE_BUILD=1 "${HERE}/run_verilator.sh" +UVM_TESTNAME="${t}" "$@"
  fi
done

echo "DONE. See ${OUT}/run.log"
