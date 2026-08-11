# Lean verification for *Sharp Berry--Esseen Bounds for the Log Determinant of a Gaussian Sample Correlation Matrix*

This private repository distributes the paper-specific Lean 4 verification
capsule for the manuscript submitted to *Probability Theory and Related
Fields*.

## Download

Download
[`logdet_Berry_Esseen_PTRF_Lean_verification_v1.0.0.zip`](./logdet_Berry_Esseen_PTRF_Lean_verification_v1.0.0.zip)
and extract it into a new folder.

SHA-256:

```text
34138125be349a163cbe0bde13a0a8a4b6a4032cd64df89fd114d22f6a770bc0
```

## Install Lean with Visual Studio Code

1. Install [Visual Studio Code](https://code.visualstudio.com/).
2. Install the official **Lean 4** extension published by `leanprover`.
3. Follow the extension's setup instructions to install Elan and Lean.
4. Open the extracted capsule folder in Visual Studio Code.

The included `lean-toolchain` file automatically selects the pinned Lean
version. The first dependency download requires an internet connection.

## Build and verify

From a newly extracted copy, run:

```bash
./scripts/verify-source.sh
lake update
lake exe cache get
lake build
lake env lean LogdetLean/PaperAxiomAudit.lean
```

Alternatively, on macOS or Linux, the following convenience script performs
the source checks, dependency setup, build, endpoint axiom audit, sorry audit,
and `leanchecker` run:

```bash
./scripts/verify.sh
```

A successful release verification ends with:

```text
Paper-specific Lean verification passed.
```

## What the capsule checks

The capsule contains the source-complete dependency closure for the ten
paper-facing Lean declarations listed in its `STATEMENT_CROSSWALK.md`. These
cover the Table 2 endpoints for Proposition 4.1, Theorems 4.2, 5.1, and 5.2,
the uniform \(A_{m,p}\) and \(V_{m,p}\) equivalents in Proposition 6.1, and
Corollary 6.2.

Lean checks the encoded declarations and their dependencies under the axioms
reported by `#print axioms`. It does not certify the manuscript's prose,
bibliography, attribution claims, simulations, or every numbered manuscript
equation. The exact boundary and bridge information are documented inside the
archive.

## Reproducible versions

- Lean toolchain: `leanprover/lean4:v4.33.0-rc2`
- Lean commit: `d8b18978322de05a8f3dba51ef03cf5461676c17`
- mathlib commit: `641fbd329d4ffb62bef83c51f54088469056bd36`

The archive contains the build, axiom, theorem-type, source-audit, dependency,
and `leanchecker` reports from the verified release. See `README.md`,
`REPRODUCIBILITY.md`, `SCOPE.md`, and `COPYRIGHT.md` inside the extracted
capsule for details.
