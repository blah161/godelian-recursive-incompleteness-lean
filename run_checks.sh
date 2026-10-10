#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
printf '%s\n' 'Lean toolchain:'
lean --version
LOG="$(mktemp)"
trap 'rm -f "$LOG"' EXIT
printf '%s\n' 'Building complete project:'
lake build 2>&1 | tee -a "$LOG"
printf '%s\n' 'Checking concrete proof transport (Lean kernel):'
lake env lean AADCertification/ConcreteTransport.lean 2>&1 | tee -a "$LOG"
printf '%s\n' 'Checking conditional structural induction (Lean kernel):'
lake env lean AADCertification/AbstractInvariance.lean 2>&1 | tee -a "$LOG"
printf '%s\n' 'Checking printed theorem dependencies (no sorryAx):'
if grep -F 'sorryAx' "$LOG"; then
  echo 'ERROR: Lean reported an incomplete proof dependency (sorryAx)' >&2
  exit 1
fi
printf '%s\n' 'Source integrity (no admitted goals / user axioms):' 
if grep -nE '^[[:space:]]*(sorry|admit|axiom)([[:space:]]|$)|:=[[:space:]]*(sorry|admit)([[:space:]]|$)' \
  AADCertification/ConcreteTransport.lean AADCertification/AbstractInvariance.lean; then
  echo 'ERROR: Found an admitted goal or user-declared axiom' >&2
  exit 1
fi
printf '%s\n' 'BUILD COMPLETED. Scope: concrete toy calculus plus conditional abstract results; arithmetic obligations remain.'
