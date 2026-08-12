# Lean verification for *Sharp Berry--Esseen Bounds for the Log Determinant of a Gaussian Sample Correlation Matrix*

This repository distributes the paper-specific Lean 4 verification capsule for the manuscript submitted to *Probability Theory and Related Fields*.

## Current verified release

Download [`logdet_Berry_Esseen_PTRF_Lean_verification_v1.1.2.zip`](./logdet_Berry_Esseen_PTRF_Lean_verification_v1.1.2.zip) and extract it into a new folder.

- Capsule version: `v1.1.2`
- Permanent Zenodo record: [10.5281/zenodo.21898548](https://doi.org/10.5281/zenodo.21898548)
- ZIP SHA-256: `563800a00392742c4c4aa1e37296d274bd66b61abf7ec7a11844d1258220dc4e`
- License: `GPL-3.0-only`
- `lake-manifest.json` SHA-256: `47e7499d3e7d67f2f3152def1c96126a13aeb23b3c2911deee5ae5bdb640d2ff`

Version 1.1.2 contains thirteen stable public theorem endpoints. It preserves the eleven endpoints from v1.1.1 and adds:

```lean
LogdetLean.paperEquationSixThree_exact
LogdetLean.paperEquationSixSix_exact
```

These expose the complete growing-gap statement (6.3) and hard-edge identity (6.6), respectively.

Earlier archives are retained for version history. Use v1.1.2 for the paper and for all new verification.

## One-command reproduction

Install [Elan](https://github.com/leanprover/elan), open a terminal in a freshly extracted v1.1.2 folder, and run:

```bash
./scripts/verify.sh
```

The first run needs network access to obtain the pinned Lean toolchain, mathlib checkout, and binary cache. Elan reads `lean-toolchain` automatically, so no system-wide Lean version change is needed.

A successful verification ends with:

```text
Paper-specific Lean verification passed.
```

For manual inspection, the main commands are:

```bash
./scripts/verify-source.sh
lake update
lake exe cache get
lake build
lake env lean LogdetLean/PaperAxiomAudit.lean
```

## Reproducibility record

The exact v1.1.2 ZIP was verified both from a clean source tree and after extraction into another fresh directory.

- Lean source files audited: 138
- Advertised endpoint declarations elaborated: 13
- Root modules checked by `leanchecker`: 8
- All advertised `#print axioms` reports: exactly `[propext, Classical.choice, Quot.sound]`
- Endpoint closure: sorry-free
- Project axioms and unsafe trust escapes found: none
- Pinned manifest changed during verification: no
- Pinned mathlib checkout dirty after acquisition: no
- Complete `lake build`: passed

The build-job count is intentionally not used as a release identifier because it can reflect cache organization. The durable identifiers are the capsule version, Zenodo DOI, ZIP checksum, toolchain commit, mathlib commit, and manifest checksum.

## What is verified

The archive's `STATEMENT_CROSSWALK.md` gives the complete paper-facing boundary. The thirteen public declarations cover:

- Proposition 4.1;
- Theorems 4.2, 5.1, and 5.2;
- all clauses of Proposition 6.1, including the uniform equivalents, growing-gap formula (6.3), refined square variance (6.5), and hard-edge identity (6.6); and
- the sharp supremum and decimal constant in Corollary 6.2.

Lean checks the encoded declarations and their formal dependencies. It does not kernel-check ordinary manuscript prose, bibliographic priority, or attribution claims.

## Exact software versions

- Elan used for the recorded run: `4.2.3` (version manager, not a proof dependency)
- Lake used for the recorded run: `5.0.0-src+d8b1897`
- Lean toolchain tag: `leanprover/lean4:v4.33.0-rc2`
- Lean commit: `d8b18978322de05a8f3dba51ef03cf5461676c17`
- mathlib commit: `641fbd329d4ffb62bef83c51f54088469056bd36`

All remaining Lean package revisions are pinned in `lake-manifest.json`. Inside the extracted capsule, see `README.md`, `STATEMENT_CROSSWALK.md`, `REPRODUCIBILITY.md`, `SCOPE.md`, `RELEASE_NOTES.md`, and `LICENSE`.
