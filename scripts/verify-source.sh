#!/usr/bin/env bash
set -euo pipefail

capsule_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$capsule_root"
python3 -B scripts/source_audit.py "$@"
