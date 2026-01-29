#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../../../.." && pwd)"
cd "${ROOT}"

if [ -f /etc/profile.d/modules.sh ]; then
  # shellcheck disable=SC1091
  source /etc/profile.d/modules.sh
fi

module load lsf >/dev/null 2>&1 || true
module load questa >/dev/null 2>&1 || true

LIST="kvips/axi4/examples/uvm_back2back/sim/tests_questa.list"
if [[ ! -f "${LIST}" ]]; then
  echo "ERROR: missing ${LIST}"
  exit 2
fi

while read -r t; do
  [[ -z "${t}" ]] && continue
  [[ "${t}" == \#* ]] && continue
  echo "=== RUN ${t} ==="
  /tools/scripts/ignrc kvips/axi4/examples/uvm_back2back/sim/run_questa.sh \
    +UVM_TESTNAME="${t}" \
    +UVM_VERBOSITY=UVM_LOW \
    "$@" </dev/null
done < "${LIST}"
