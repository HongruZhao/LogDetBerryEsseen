# Verification and reproducibility

## Fresh local checks on 2026-09-13

| Check | Result and boundary |
|---|---|
| Integrity of all three supplied ZIPs | CRC checks passed; archive hashes recorded |
| Original Lean source identity | All 138 original Lean files preserved byte for byte |
| Original project | Fresh local source build passed, 4,068 Lake jobs reported |
| Updated project | Build passed, 4,072 Lake jobs reported |
| Original endpoint audit | All 13 types elaborated; each axiom set is exactly the three standard foundations |
| Expanded audit | 36 declarations: 13 original endpoints, 13 public wrappers, 8 model/normalization bridges, 2 conditional variance wrappers |
| Imported proof closure | Environment-aware sorry audit passed |
| Local source scan | 142 Lean files; no project axiom, placeholder, or unsafe/native escape found |
| Compiler messages | 21 inherited linter warnings; no final build errors |
| Additional module checking | All ten named `leanchecker` checks passed with exit code 0 |

Fresh logs and machine-readable receipts are in [audit/2026-09-13](../audit/2026-09-13/). The separate module rechecks with `leanchecker` are recorded there with exit codes. Read those receipts for their completed status rather than inferring success from the availability of a verification command.

The original build started without project `.olean` files. The pinned third-party dependency source and compiled caches were copied from an existing local installation. All nine dependency revisions matched the lockfile and their tracked source trees were clean. No original project proof artifact was reused. Mathlib and the Lean compiler were not rebuilt from source in this audit.

`leanchecker` is a further check with Lean's checker. It is not a Comparator statement match or a Nanoda run. No such independent-tool receipt is claimed here.

## Reproduce

Use the checked-in `lean-toolchain` and `lake-manifest.json`. Do not run `lake update` as part of verification: it is unnecessary and can change dependency resolution.

```sh
python3 -B scripts/source_audit.py
lake exe cache get
lake build
lake env lean Verification.lean
```

The complete procedure writes reports under `audit/latest/` by default:

```sh
bash scripts/verify.sh
```

It scans project source, fetches the pinned dependency cache, checks dependency revisions and tracked-source cleanliness, builds the registered targets, checks the exact inventory of axiom reports, requires a clean environment sorry report, and runs ten named module checks with `leanchecker`. It fails on missing/duplicate axiom reports, unapproved axioms, source trust escapes, build errors, or failed module checks.

For a newly extracted source-only archive, the stricter packaging check is:

```sh
python3 -B scripts/source_audit.py --release
```

Run this before creating `.lake/`. The normal source audit excludes `.lake/` and `.git/`, so it can also be rerun in a working checkout.

## What the checks mean

A successful build establishes that Lean accepts the formal proof terms. The source scan complements that check; it is not a proof checker. The axiom audit reports foundational dependencies, while the full theorem types expose ordinary hypotheses. The conditional variance wrappers illustrate why all three checks matter.

The statement review compared the paper's quantifiers, definitions, rates, loss, dimension conditions, and model bridges with the formal endpoints. It did not independently re-prove every line of the paper or establish bibliographic novelty.

## Historical evidence

[audit/legacy-v1.1.2](../audit/legacy-v1.1.2/) preserves the reports and documentation supplied in the old archive. Their dates and claims are historical. Its `SHA256SUMS` and file manifest describe paths in the original archive, not the reorganized repository. Use the new receipts for this revision.
