# Revision 1.1.4

Prepared on 2026-09-13. This is a focused source revision, not a new archived
DOI or GitHub release.

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
