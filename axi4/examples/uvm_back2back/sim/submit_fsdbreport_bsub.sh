#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../../../.." && pwd)"
SIM_DIR="${ROOT}/axi4/examples/uvm_back2back/sim"

if [[ $# -lt 1 ]]; then
  echo "Usage: submit_fsdbreport_bsub.sh <fsdb_path> [--bt <time>] [--et <time>] [--cfg <cfgfile>] [--out <outfile>]"
  exit 2
fi

if ! command -v bsub >/dev/null 2>&1; then
  echo "ERROR: bsub not found on PATH (need 'module load lsf')."
  exit 127
fi

QUEUE="${LSF_QUEUE:-short}"
APP="${LSF_APP:-gnrc}"
PROJECT="${LSF_PROJECT:-}"
LP="${LSF_LP:-}"

BSUB_ARGS=(-q "${QUEUE}" -app "${APP}")
[[ -n "${PROJECT}" ]] && BSUB_ARGS+=(-P "${PROJECT}")
[[ -n "${LP}" ]] && BSUB_ARGS+=(-Lp "${LP}")

FSDB="$1"
shift

CMD=(bash "${SIM_DIR}/run_fsdbreport_lsf.sh" "${FSDB}" "$@")

echo "bsub ${BSUB_ARGS[*]} ${CMD[*]}"
exec bsub "${BSUB_ARGS[@]}" "${CMD[@]}"
