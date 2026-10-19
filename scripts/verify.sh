#!/usr/bin/env bash
set -euo pipefail

# Run dependency setup from the README once before using this local check.
cd "$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
python3 scripts/check_project.py --require-dependencies
lake --no-cache build MomentAmbiguity MomentAmbiguityChecks

for module in Regression FoundationRegression IIDRegression AxiomAudit; do
  lake --no-cache env lean -j1 -DwarningAsError=true "MomentAmbiguity/Verification/${module}.lean"
done

printf '%s\n' 'Complete verification passed.'
