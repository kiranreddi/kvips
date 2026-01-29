#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "${HERE}/../../../../.." && pwd)"
OUT="${ROOT}/kvips/apb/examples/uvm_back2back/sim/out/vcs"

TESTS_FILE="${HERE}/tests_questa.list"
if [[ ! -f "${TESTS_FILE}" ]]; then
  echo "ERROR: missing ${TESTS_FILE}"
  exit 2
fi

while IFS= read -r t || [[ -n "${t}" ]]; do
  [[ -z "${t}" || "${t}" =~ ^# ]] && continue
  echo "==== ${t} ===="
  "${HERE}/run_vcs.sh" +UVM_TESTNAME="${t}" "$@"
done <"${TESTS_FILE}"

echo "DONE. See ${OUT}/run.log"

