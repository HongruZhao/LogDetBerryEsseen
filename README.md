# Lean verification for *Sharp Berry--Esseen Bounds for the Log Determinant of a Gaussian Sample Correlation Matrix*

This repository distributes the paper-specific Lean 4 verification capsule for the manuscript submitted to *Probability Theory and Related Fields*.

## Current verified release

Download [`logdet_Berry_Esseen_PTRF_Lean_verification_v1.1.0.zip`](./logdet_Berry_Esseen_PTRF_Lean_verification_v1.1.0.zip) and extract it into a new folder.

- Capsule version: `v1.1.0`
- Archive release commit: `07d1854cc686cccd8f4582ffb883e04b734522ed`
- ZIP SHA-256: `32e2728af1de5a74eac25a9042c588d890d33e84361e5b373389ddbcb49a7f54`
- `lake-manifest.json` SHA-256: `47e7499d3e7d67f2f3152def1c96126a13aeb23b3c2911deee5ae5bdb640d2ff`

Version 1.1.0 adds the exact Lean theorem for the square-variance refinement (6.5):

```lean
LogdetLean.tendsto_square_nullVSeries_sub_two_log
```

In the paper's notation, it proves `V_{p,p} - 2 log p -> 2 gamma_E + pi^2/4`.

The previous [v1.0.0 archive](./logdet_Berry_Esseen_PTRF_Lean_verification_v1.0.0.zip) is retained for history.

## One-command reproduction

Install [Elan](https://github.com/leanprover/elan), open a terminal in a freshly extracted v1.1.0 folder, and run:

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

A full run from a fresh extraction completed successfully on August 11, 2026.

- Lean source files audited: 138
- Advertised endpoint declarations elaborated: 11
- Root modules checked by `leanchecker`: 8
- All advertised `#print axioms` reports: exactly `[propext, Classical.choice, Quot.sound]`
- Endpoint closure: sorry-free
- Project axioms and unsafe trust escapes found: none
- Pinned manifest changed during verification: no
- Pinned mathlib checkout dirty after acquisition: no
- `lake build`: completed successfully

The build-job count is intentionally not used as a release identifier: it can reflect build progress and cache organization. The durable identifiers are the capsule version, Git commit, ZIP checksum, toolchain commit, mathlib commit, and manifest checksum.

## What is verified

The archive's `STATEMENT_CROSSWALK.md` gives the complete paper-facing boundary. Version 1.1.0 contains eleven advertised declarations covering:

- Proposition 4.1;
- Theorems 4.2, 5.1, and 5.2;
- the uniform `A_{m,p}` and `V_{m,p}` equivalents (6.2) and (6.4);
- the exact square variance refinement (6.5); and
- the sharp supremum and decimal constant in Corollary 6.2.

Lean checks the encoded declarations and their formal dependencies. It does not by itself certify manuscript prose, bibliography, attribution claims, simulations, or every numbered manuscript equation.

## Exact software versions

- Elan used for the recorded run: `4.2.3` (version manager, not a proof dependency)
- Lake used for the recorded run: `5.0.0-src+d8b1897`
- Lean toolchain tag: `leanprover/lean4:v4.33.0-rc2`
- Lean commit: `d8b18978322de05a8f3dba51ef03cf5461676c17`
- mathlib commit: `641fbd329d4ffb62bef83c51f54088469056bd36`

All remaining Lean package revisions are pinned in `lake-manifest.json`. See `README.md`, `STATEMENT_CROSSWALK.md`, `REPRODUCIBILITY.md`, `SCOPE.md`, and `COPYRIGHT.md` inside the extracted capsule.
