#!/usr/bin/env python3
"""Audit project Lean source and pinned dependencies, excluding local build caches."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.33.0-rc2"
EXPECTED_MATHLIB_REV = "641fbd329d4ffb62bef83c51f54088469056bd36"
EXPECTED_LEAN_FILES = 142
IGNORED_DIRS = {".git", ".lake", "__pycache__"}

def mask_lean_comments_and_strings(text: str) -> str:
    """Preserve newlines while masking nested comments and string contents."""
    out: list[str] = []
    i = 0
    block_depth = 0
    in_line = False
    in_string = False
    escaped = False
    while i < len(text):
        pair = text[i : i + 2]
        ch = text[i]
        if in_line:
            if ch == "\n":
                in_line = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue
        if block_depth:
            if pair == "/-":
                block_depth += 1
                out.extend((" ", " "))
                i += 2
            elif pair == "-/":
                block_depth -= 1
                out.extend((" ", " "))
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue
        if in_string:
            out.append("\n" if ch == "\n" else " ")
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            i += 1
            continue
        if pair == "--":
            in_line = True
            out.extend((" ", " "))
            i += 2
        elif pair == "/-":
            block_depth = 1
            out.extend((" ", " "))
            i += 2
        elif ch == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(ch)
            i += 1
    if block_depth or in_string:
        raise ValueError("unterminated Lean comment or string")
    return "".join(out)



def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--release", action="store_true",
                        help="also reject generated directories and compiled artifacts")
    args = parser.parse_args()
    failures = []
    files = []
    for directory, dirs, names in os.walk(ROOT, followlinks=False):
        base = Path(directory)
        for name in list(dirs):
            p = base / name
            if p.is_symlink():
                failures.append(f"symbolic link: {p.relative_to(ROOT)}")
                dirs.remove(name)
            elif name in IGNORED_DIRS:
                if args.release:
                    failures.append(f"generated directory in release: {p.relative_to(ROOT)}")
                dirs.remove(name)
        files.extend(base / name for name in names)
    lean_files = sorted(p for p in files if p.suffix == ".lean")
    if len(lean_files) != EXPECTED_LEAN_FILES:
        failures.append(f"Lean source count {len(lean_files)} != {EXPECTED_LEAN_FILES}")
    forbidden = re.compile(
        r"\b(?:sorry|admit|sorryAx|axiom|postulate|constant|constants|unsafe|"
        r"extern|implemented_by|native_decide|by_native_decide|run_tac|ofReduceBool)\b"
        r"|\.axiomDecl\b|\b(?:Lean\.)?addDecl\b"
        r"|(?m:^\s*(?:run_cmd|elab|elab_rules|command_elab|macro|macro_rules|syntax|"
        r"declare_syntax_cat|initialize)\b)"
    )
    modules = {str(p.relative_to(ROOT).with_suffix("")).replace(os.sep, "."): p
               for p in lean_files}
    graph = {}
    for module, p in modules.items():
        try:
            code = mask_lean_comments_and_strings(p.read_text(encoding="utf-8"))
        except (ValueError, UnicodeError) as exc:
            failures.append(f"{p.relative_to(ROOT)}: {exc}")
            continue
        for match in forbidden.finditer(code):
            line = code.count("\n", 0, match.start()) + 1
            failures.append(f"{p.relative_to(ROOT)}:{line}: forbidden trust construct")
        imports = []
        for match in re.finditer(r"(?m)^\s*import\s+(.+)$", code):
            for dep in match.group(1).split():
                if dep in modules:
                    imports.append(dep)
                elif dep != "Mathlib" and not dep.startswith("Mathlib."):
                    failures.append(f"{p.relative_to(ROOT)}: unresolved/unapproved import {dep}")
        graph[module] = imports
    reachable, pending = set(), ["LogDetBerryEsseen", "Verification", "LogdetLean",
                                 "LogdetLean.PaperAxiomAudit"]
    while pending:
        module = pending.pop()
        if module in reachable:
            continue
        reachable.add(module)
        if module not in modules:
            failures.append(f"missing root/import {module}")
        pending.extend(graph.get(module, []))
    for module in sorted(set(modules) - reachable):
        failures.append(f"unreachable Lean source: {module}")
    config = (ROOT / "lakefile.toml").read_text()
    if re.search(r"(?m)^\s*path\s*=", config):
        failures.append("local dependency path in lakefile.toml")
    if f'rev = "{EXPECTED_MATHLIB_REV}"' not in config:
        failures.append("mathlib revision not pinned in lakefile.toml")
    if (ROOT / "lean-toolchain").read_text().strip() != EXPECTED_TOOLCHAIN:
        failures.append("unexpected Lean toolchain")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    if manifest.get("name") != "logdet_berry_esseen_lean":
        failures.append("unexpected Lake package identity")
    mathlib = [p for p in manifest.get("packages", []) if p.get("name") == "mathlib"]
    if len(mathlib) != 1 or mathlib[0].get("rev") != EXPECTED_MATHLIB_REV:
        failures.append("unexpected mathlib manifest revision")
    for dep in manifest.get("packages", []):
        url = str(dep.get("url", ""))
        if (dep.get("type") != "git" or
                not re.fullmatch(r"[0-9a-f]{40}", str(dep.get("rev", ""))) or
                not url.startswith("https://github.com/") or
                "@" in url.removeprefix("https://")):
            failures.append(f"dependency is not pinned to a public Git revision: {dep.get('name')}")
    compiled = {".olean", ".ilean", ".trace", ".c", ".o", ".a", ".so", ".dylib", ".dll", ".pyc"}
    secrets = re.compile("(?:" + "ghp" + r"_|github" + r"_pat_)[A-Za-z0-9_]+"
                         + "|BEGIN (?:RSA |EC |OPENSSH )?PRIVATE " + "KEY")
    machine_paths = re.compile("(?:/" + "Users/|/" + "home/|/private/" + "var/)")
    for p in files:
        rel = p.relative_to(ROOT)
        if p.is_symlink():
            failures.append(f"symbolic link: {rel}")
            continue
        data = p.read_bytes()
        if p.parent == ROOT / "archives" and p.suffix == ".zip":
            checksum_file = ROOT / "archives/SHA256SUMS"
            entries = dict((name, digest) for digest, name in
                           (line.split(None, 1) for line in checksum_file.read_text().splitlines()))
            if entries.get(p.name) != hashlib.sha256(data).hexdigest():
                failures.append(f"historical archive checksum mismatch: {rel}")
            continue
        if p.suffix in compiled or p.name == ".DS_Store":
            failures.append(f"generated artifact outside excluded cache: {rel}")
        if b"\x00" in data:
            failures.append(f"binary/NUL-containing file: {rel}")
        raw = data.decode("utf-8", errors="replace")
        if secrets.search(raw):
            failures.append(f"possible credential in {rel}")
        if machine_paths.search(raw):
            failures.append(f"machine-specific absolute path in {rel}")
    if failures:
        print("SOURCE AUDIT FAILED", file=sys.stderr)
        for failure in failures:
            print("- " + failure, file=sys.stderr)
        return 1
    print(f"Source audit passed: {len(lean_files)} Lean files; all local imports resolve.")
    print("No proof placeholders, project axioms, native/unsafe escapes, or custom elaborators.")
    print("Toolchain and public Git dependencies are pinned; source closure is complete.")
    print("Build caches are excluded from source inspection; kernel checks are separate.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
