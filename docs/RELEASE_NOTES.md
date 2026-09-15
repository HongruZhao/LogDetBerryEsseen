# Version v1.1.4

The full formalization is published at
[10.5281/zenodo.22739087](https://doi.org/10.5281/zenodo.22739087).
The matching GitHub release contains the exact same full Lean ZIP.

## September 14 synchronization

- Keep the public GitHub interface focused on Theorem 4.2, Theorem 5.2, and
  Corollary 6.2. Its three interface files are byte-identical to the full archive.
- Synchronize `GeneralRCenterIdentity.lean` and `HardEdgeConstant.lean` with the
  published archive, retaining the existing compact import structure.
- Link the README, citation, scope report, and statement map to the full release.
- Update the historical gap notes: the full archive completes all 38 remaining
  inventory entries, including the actual covariance and exact variance identity.
- Record the source correspondence and current focused verification in
  [audit/2026-09-14-zenodo-sync](../audit/2026-09-14-zenodo-sync).

The full archive covers 243 inventory entries with 288 audited endpoints; the
GitHub landing page continues to present only the three main results. See
[ZENODO_RELEASE.md](ZENODO_RELEASE.md) for archive hashes and the source relationship.

## September 13 focused development

- Reduce the public interface from thirteen declarations to three main results:
  Theorem 4.2, Theorem 5.2, and Corollary 6.2.
- Shorten the README, statement map, and formalization metadata to that scope.
- Retire twelve unused or out-of-scope Lean modules to the historical archive, including the optional
  conditional exact-variance identity and decimal constant certification.
- Extract five unchanged unconditional helpers into `GeneralRVarianceBasics`.
  Every active Lean source module belongs to the main-result or verification
  import closure.
- Preserve historical capsules, retired modules, and broader audit reports
  outside the active build, alongside the current verification record.
- Preserve the Lean/Mathlib pins, internal package identity, and GPL-3.0-only
  license. The old thirteen-wrapper interface is intentionally replaced.
