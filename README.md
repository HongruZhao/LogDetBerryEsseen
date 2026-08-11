# Lean verification for *Sharp Berry--Esseen Bounds for the Log Determinant of a Gaussian Sample Correlation Matrix*

This repository hosts the paper-specific Lean 4 verification capsule for the
manuscript submitted to **Probability Theory and Related Fields**.

## Download the verification archive

Download [`logdet_Berry_Esseen_PTRF_Lean_verification_v1.0.0.zip`](./logdet_Berry_Esseen_PTRF_Lean_verification_v1.0.0.zip), then extract it to a
folder on your computer.

SHA-256:

```text
3556bb6c0e039817cb98a79b4b0aa5155f3c1ed7d4ef2e95e05e0c2ec8c0572e
```

## Install Lean with VS Code

1. Install [Visual Studio Code](https://code.visualstudio.com/).
2. In VS Code, open **Extensions** and install the official **Lean 4** extension
   published by `leanprover` (`leanprover.lean4`).
3. Follow the setup guide opened by the extension. The project contains a
   `lean-toolchain` file, so Lean/Elan will select the pinned Lean version.
4. Extract the ZIP and open the extracted folder in VS Code using
   **File > Open Folder**.

Official installation guide: <https://lean-lang.org/install/>

## Verify the proofs

Open a terminal in the extracted capsule folder and run:

```bash
lake exe cache get
lake build
lake env lean LogdetLean/PaperAxiomAudit.lean
```

On macOS or Linux, one command runs the source scan, build, and axiom audit:

```bash
./scripts/verify.sh
```

On Windows PowerShell:

```powershell
lake exe cache get
.\scripts\verify.ps1
```

A successful run completes without Lean errors. The paper-facing axiom audit
should list only standard Lean/mathlib foundations such as `propext`,
`Classical.choice`, and `Quot.sound`.

## What this capsule checks

The public statement boundary is recorded in `STATEMENT_CROSSWALK.md`
inside the archive. It covers
the Table 2 endpoints for Proposition 4.1, Theorems 4.2, 5.1, and 5.2, the
uniform \(A_{m,p}\)- and \(V_{m,p}\)-equivalents in Proposition 6.1, and
Corollary 6.2.

The Heiny--Johnston--Prochno bound displayed as equation (3.1) is an external
cited result and is not re-proved here. Lean checks the encoded mathematical
declarations and their dependencies; it does not certify prose, bibliography,
priority, or numerical experiments.

## Reproducible versions

- Lean: `leanprover/lean4:v4.33.0-rc2`
- mathlib: `641fbd329d4ffb62bef83c51f54088469056bd36`

## Scope and reuse

The archive is source-complete for the advertised endpoints but intentionally
limited to this paper. Broader proof-engineering infrastructure, unrelated
projects, private automation, generators, prompts, and Git history are not
included. See `SCOPE.md` and `LICENSE.md` inside the archive.
