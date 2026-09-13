#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
report_dir="${1:-audit/latest}"
mkdir -p "$report_dir"

python3 -B scripts/source_audit.py | tee "$report_dir/source_audit.txt"
manifest_before="$(shasum -a 256 lake-manifest.json | awk '{print $1}')"

# Use the existing lockfile. Do not run `lake update` during verification.
lake exe cache get > "$report_dir/cache.log" 2>&1
test "$manifest_before" = "$(shasum -a 256 lake-manifest.json | awk '{print $1}')"
lean_version="$(lake env lean --version)"
case "$lean_version" in
  *"Lean (version 4.33.0-rc2"*"commit d8b18978322de05a8f3dba51ef03cf5461676c17"*) ;;
  *) echo "Unexpected Lean binary: $lean_version" >&2; exit 1 ;;
esac
echo "$lean_version" | tee "$report_dir/lean_version.txt"

python3 -B - <<'PYDEPS' | tee "$report_dir/dependencies.txt"
import json
import subprocess
from pathlib import Path
for package in json.loads(Path('lake-manifest.json').read_text())['packages']:
    directory = str(Path('.lake/packages') / package['name'])
    revision = subprocess.check_output(['git', '-C', directory, 'rev-parse', 'HEAD'], text=True).strip()
    status = subprocess.check_output(['git', '-C', directory, 'status', '--porcelain', '--untracked-files=no'], text=True)
    if revision != package['rev'] or status:
        raise SystemExit('Dependency mismatch or modified tracked source: ' + package['name'])
    print(package['name'], revision, 'tracked source clean')
PYDEPS

lake build > "$report_dir/build.log" 2>&1
lake env lean Verification.lean > "$report_dir/axioms_and_types.txt" 2>&1
python3 -B scripts/check_axioms.py "$report_dir/axioms_and_types.txt" "$report_dir/axioms.json"

modules=(
  LogdetLean.SampleCorrelationBeta
  LogdetLean.NullUniformEdgeworthTarget
  LogdetLean.GeneralRPaperExactTranslation
  LogdetLean.NullAUniformAsymptotics
  LogdetLean.NullVUniformAsymptotics
  LogdetLean.NullRefinedAsymptotics
  LogdetLean.NullSharpSupremum
  LogdetLean.NullSharpSupremumDecimal
  LogdetLean.ConditionalVariance
  LogDetBerryEsseen
)
for module in "${modules[@]}"; do
  lake env leanchecker "$module" > "$report_dir/leanchecker-$module.txt" 2>&1
done
test "$manifest_before" = "$(shasum -a 256 lake-manifest.json | awk '{print $1}')"
echo "Verification passed. Reports: $report_dir"
