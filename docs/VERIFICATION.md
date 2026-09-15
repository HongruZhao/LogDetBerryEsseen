# Verification of the three main results

The focused v1.1.4 project was freshly rebuilt and checked on **2026-09-14**
for synchronization with [Zenodo v1.1.4](https://doi.org/10.5281/zenodo.22739087).

| Check | Result |
|---|---|
| Fresh build of the reduced project | Passed; all 131 active project Lean modules built from source, 4,062 Lake jobs, zero errors |
| Public theorem axiom reports | All three use only `propext`, `Classical.choice`, `Quot.sound` |
| Imported declaration closure | Sorry-free |
| Source audit | All 131 active Lean files resolve within the main-result/verification import closure; no project axioms or proof escapes |
| `leanchecker` | Four module checks passed, including the public entry module |
| Dependency pins | All nine Git revisions matched, with clean tracked source |
| Source correspondence with the published full ZIP | 128 active Lean files byte-identical; two focused import roots; five unchanged helpers collected in one focused module |

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

The [current receipts](../audit/2026-09-14-zenodo-sync) contain the build log,
verification outputs, source hashes, dependency revisions, source correspondence,
and [machine-readable summary](../audit/2026-09-14-zenodo-sync/summary.json).

This run started with no project build cache and compiled all 131 active project
Lean modules from source. Only the pinned third-party dependency caches were
reused. Lean and Mathlib were not rebuilt from source. Seventeen linter warnings
are recorded in the build log; none is a proof hole or compiler error.

The source audit, dependency and binary checks, build, endpoint audit, and all
four `leanchecker` invocations were run individually using the same checks as
`scripts/verify.sh`. The dependency download step was unnecessary because the
exact pinned caches were already available.

The [September 13 receipts](../audit/2026-09-13-main-results) preserve the earlier
incremental build and focused-source extraction history.

The complete original project had previously passed a fresh local source
build; its broader receipts remain in [the earlier revision](https://github.com/HongruZhao/LogDetBerryEsseen/tree/ec41febe106f5b4c543bf908ff6e25764fe210bd/audit/2026-09-13).
Those receipts cover that earlier source tree, not the reduced interface.

`leanchecker` checks compiled proof terms. Comparator and Nanoda were not run,
and `Challenge.lean` reuses the development's definitions. The semantic review
covers the main statements and their model bridges, not every manuscript
assertion or every supporting argument independently.
