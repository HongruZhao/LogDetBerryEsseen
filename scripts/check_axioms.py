#!/usr/bin/env python3
"""Check an exact inventory of Lean axiom reports and the environment sorry audit."""
import json
import re
import sys
from pathlib import Path

root = Path(__file__).resolve().parents[1]
inventory = json.loads((root / "scripts/audit_declarations.json").read_text())
expected = {item["name"] for item in inventory}
text = Path(sys.argv[1]).read_text()
reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S)
names = [name for name, _ in reports]
if len(names) != len(set(names)) or set(names) != expected:
    raise SystemExit("Missing, duplicate, or unexpected declaration reports")
allowed = {"propext", "Classical.choice", "Quot.sound"}
results = {}
for name, report in reports:
    actual = {item.strip() for item in report.split(",") if item.strip()}
    if not actual <= allowed:
        raise SystemExit(f"Extra axioms in {name}: {sorted(actual - allowed)}")
    results[name] = sorted(actual)
if text.count("Declarations are sorry-free!") != 1:
    raise SystemExit("The environment sorry audit did not report exactly one clean result")
receipt = {
    "checked_declarations": len(reports),
    "project_axioms": [],
    "sorry_free_import_closure": True,
    "declarations": [dict(item, axioms=results[item["name"]]) for item in inventory],
    "limitation": "Axiom reports do not discharge ordinary theorem hypotheses.",
}
if len(sys.argv) > 2:
    Path(sys.argv[2]).write_text(json.dumps(receipt, indent=2) + "\n")
print(f"All {len(reports)} declaration reports use only the three allowed foundations.")
print("The full imported declaration closure is sorry-free.")
