#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../../.." && pwd)"
cd "${ROOT}"

LIST="axi4/examples/uvm_back2back/sim/tests_questa.list"
if [[ ! -f "${LIST}" ]]; then
  echo "ERROR: missing ${LIST}"
  exit 2
fi

while read -r t; do
  [[ -z "${t}" ]] && continue
  [[ "${t}" == \#* ]] && continue
  echo "=== RUN ${t} ==="
  axi4/examples/uvm_back2back/sim/run_vcs.sh \
    +UVM_TESTNAME="${t}" \
    +UVM_VERBOSITY=UVM_LOW \
    "$@" </dev/null
done < "${LIST}"
