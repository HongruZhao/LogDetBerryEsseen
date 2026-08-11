# Lean verification for *Sharp Berry--Esseen Bounds for the Log Determinant of a Gaussian Sample Correlation Matrix*

This private repository distributes the paper-specific Lean 4 verification capsule for the manuscript submitted to *Probability Theory and Related Fields*.

## Current download

Download [`logdet_Berry_Esseen_PTRF_Lean_verification_v1.1.0.zip`](./logdet_Berry_Esseen_PTRF_Lean_verification_v1.1.0.zip) and extract it into a new folder.

SHA-256:

```text
32e2728af1de5a74eac25a9042c588d890d33e84361e5b373389ddbcb49a7f54
```

Version 1.1.0 adds the exact Lean theorem for the square-variance refinement (6.5):

```lean
LogdetLean.tendsto_square_nullVSeries_sub_two_log
```

It proves

```text
V_{p,p} - 2 log p  ->  2 gamma_E + pi^2/4.
```

The previous [`v1.0.0 archive`](./logdet_Berry_Esseen_PTRF_Lean_verification_v1.0.0.zip) is retained for history.

## Build and verify

Open a terminal in the extracted v1.1.0 folder and run:

```bash
./scripts/verify-source.sh
lake update
lake exe cache get
lake build
lake env lean LogdetLean/PaperAxiomAudit.lean
```

On macOS or Linux, the complete convenience command is:

```bash
./scripts/verify.sh
```

A successful full verification ends with:

```text
Paper-specific Lean verification passed.
```

## What the capsule checks

The archive's `STATEMENT_CROSSWALK.md` documents the complete paper-facing boundary. Version 1.1.0 contains eleven advertised Lean declarations covering:

- Proposition 4.1;
- Theorems 4.2, 5.1, and 5.2;
- the uniform A and V equivalents (6.2) and (6.4);
- the exact square refinement (6.5); and
- the sharp supremum and decimal constant in Corollary 6.2.

The new (6.5) endpoint compiled successfully and its axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. The ZIP checksum and compressed-data integrity checks also pass. Run `./scripts/verify.sh` in a freshly extracted copy for the complete local source, build, axiom, sorry, and `leanchecker` verification.

Lean checks the encoded declarations and their dependencies. It does not certify manuscript prose, bibliography, attribution claims, simulations, or every numbered manuscript equation.

## Reproducible versions

- Lean toolchain: `leanprover/lean4:v4.33.0-rc2`
- Lean commit: `d8b18978322de05a8f3dba51ef03cf5461676c17`
- mathlib commit: `641fbd329d4ffb62bef83c51f54088469056bd36`

See `README.md`, `STATEMENT_CROSSWALK.md`, `REPRODUCIBILITY.md`, `SCOPE.md`, and `COPYRIGHT.md` inside the extracted capsule for details.
