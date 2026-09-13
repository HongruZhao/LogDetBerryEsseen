# Verification of the three main results

The focused v1.1.4 project passed verification on 2026-09-13.

| Check | Result |
|---|---|
| Build of the reduced project | Passed; 4,062 Lake jobs, zero errors |
| Public theorem axiom reports | All three use only `propext`, `Classical.choice`, `Quot.sound` |
| Imported declaration closure | Sorry-free |
| Source audit | All 131 active Lean files resolve within the main-result/verification import closure; no project axioms or proof escapes |
| `leanchecker` | Four module checks passed, including the public entry module |
| Dependency pins | All nine Git revisions matched, with clean tracked source |
| Source identity | 125 original files unchanged; two changed; eleven retired from the active library; five helper definitions/proofs extracted unchanged |

The 131 active files comprise the three-result interface and its supporting proof
library. The public proof entry file has 26 lines; `Challenge.lean` gives the
full target propositions in 55 lines.

## Reproduce

```sh
bash scripts/verify.sh
```

The script checks the pinned dependency revisions and exact Lean binary,
builds the project, checks all three public axiom reports and the imported
closure, and runs `leanchecker` on the null, general-correlation, supremum,
and public entry modules. It uses the committed dependency lockfile.

## Evidence and limits

The [current receipts](../audit/2026-09-13-main-results) contain the build log,
verification outputs, source hashes, and [machine-readable summary](../audit/2026-09-13-main-results/summary.json).

This revision rebuilt the changed files and their affected imports, reusing
unchanged project artifacts from the earlier successful build and the exact
pinned dependency caches. Lean and Mathlib were not rebuilt from source.
Sixteen inherited linter warnings remain; they are recorded in the build log.

The complete original project had previously passed a fresh local source
build; its broader receipts remain in [the earlier revision](https://github.com/HongruZhao/LogDetBerryEsseen/tree/ec41febe106f5b4c543bf908ff6e25764fe210bd/audit/2026-09-13).
Those receipts cover that earlier source tree, not the reduced interface.

`leanchecker` checks compiled proof terms. Comparator and Nanoda were not run,
and `Challenge.lean` reuses the development's definitions. The semantic review
covers the main statements and their model bridges, not every manuscript
assertion or every supporting argument independently.
