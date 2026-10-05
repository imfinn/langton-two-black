#!/usr/bin/env bash
set -euo pipefail
repo_dir="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
case "${1:-}" in
  ""|--clean) ;;
  *) echo 'Usage: scripts/validate.sh [--clean]' >&2; exit 2 ;;
esac
out_dir="${AUDIT_OUTPUT_DIR:-$repo_dir/audit/local}"
mkdir -p "$out_dir"
out_dir="$(CDPATH= cd -- "$out_dir" && pwd)"
python3 "$repo_dir/scripts/scan_source.py" > "$out_dir/source-scan.json"
cd "$repo_dir/lean"
lean --version | tee "$out_dir/lean-version.txt"
lake --version | tee "$out_dir/lake-version.txt"
if [[ "${1:-}" == --clean ]]; then lake clean; fi
lake --no-cache build 2>&1 | tee "$out_dir/build.log"
lake env lean TheoremAAxioms.lean 2>&1 | tee "$out_dir/theoremA-axioms.out"
python3 "$repo_dir/scripts/check_axioms.py" "$out_dir/theoremA-axioms.out"
lake env lean Axioms.lean > "$out_dir/axioms-all.out"
lake build TwoBlack.PartMut 2>&1 | tee "$out_dir/part-mutations.log"
lake env lean "$repo_dir/tests/CoreMutations.lean" 2>&1 | tee "$out_dir/core-mutations.log"
lake env lean "$repo_dir/tests/IntegrationMutations.lean" 2>&1 | tee "$out_dir/integration-mutations.log"
echo "Validation completed. Fresh logs: $out_dir"
