# Lean verification capsule

This archive contains the paper-specific Lean 4 verification source for

*Sharp Berry--Esseen Bounds for the Log Determinant of a Gaussian Sample
Correlation Matrix*

submitted to *Probability Theory and Related Fields*.

The archive is source-complete for the thirteen paper-facing declarations listed
in [`STATEMENT_CROSSWALK.md`](STATEMENT_CROSSWALK.md). It is intentionally
limited to this paper and is not a general-purpose Edgeworth, Wishart,
random-matrix, or probability library.

## What Lean checks

Lean checks that each advertised declaration follows from its formal
assumptions and the foundations reported by `#print axioms`. The formal
source also contains the exact law bridges used to connect canonical random
variables to the sample statistics printed in the paper.

Lean does not check the manuscript's English prose, bibliography,
attribution or originality claims, simulations, hardware timings, or
practical recommendations. The capsule also does not claim that every
numbered equation in the manuscript has been formalized. See
[`SCOPE.md`](SCOPE.md) for the precise boundary.

## Pinned versions

- Lean toolchain: `leanprover/lean4:v4.33.0-rc2`
- Lean commit: `d8b18978322de05a8f3dba51ef03cf5461676c17`
- mathlib commit: `641fbd329d4ffb62bef83c51f54088469056bd36`

The toolchain and dependency are pinned by `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json`.

## Validation status

Version v1.1.2 is the finalized paper-specific capsule. The full verification
procedure was run from a fresh extraction and then repeated from the final ZIP.
All thirteen endpoint reports contain exactly `propext`, `Classical.choice`, and
`Quot.sound`; the imported endpoint closure is sorry-free. The generated
reports and checksums in this archive identify the exact verified bytes.

## Install Lean using Visual Studio Code

1. Install [Visual Studio Code](https://code.visualstudio.com/).
2. Open the Extensions panel in Visual Studio Code.
3. Install the official **Lean 4** extension published by `leanprover`.
4. Follow the extension's setup instructions to install Elan and Lean.
5. Extract this ZIP archive into a new folder.
6. In Visual Studio Code, choose **File > Open Folder** and open the extracted
   capsule folder.
7. Open **Terminal > New Terminal**. The terminal should start in the capsule
   folder.

The `lean-toolchain` file automatically selects the required Lean version.
The first dependency download requires an internet connection.

## Build and verify

On a newly extracted copy, run the source audit before dependency setup
creates `.lake/`:

```bash
./scripts/verify-source.sh
lake update
lake exe cache get
lake build
lake env lean LogdetLean/PaperAxiomAudit.lean
```

The last command prints the types and axioms of all thirteen advertised
declarations. The release is verified only if every command exits
successfully, the source audit reports no forbidden construct, and the axiom
output contains no unapproved axiom. The verification reports included with
a finalized release are the authoritative record of that run; this README
does not replace them.

The convenience script `scripts/verify.sh` combines dependency setup, the
source and environment checks, build, endpoint axiom audit, sorry audit, and
eight-module `leanchecker` run. Run it only from a clean extraction before
`.lake/` exists:

```bash
./scripts/verify.sh
```

## Where to start reading

- [`STATEMENT_CROSSWALK.md`](STATEMENT_CROSSWALK.md): paper statements,
  endpoint names, and exact bridge information.
- [`LogdetLean/PaperTable2Endpoints.lean`](LogdetLean/PaperTable2Endpoints.lean):
  narrow public Lean interface.
- [`LogdetLean/PaperAxiomAudit.lean`](LogdetLean/PaperAxiomAudit.lean): all
  endpoint `#check` and `#print axioms` commands.
- [`REPRODUCIBILITY.md`](REPRODUCIBILITY.md): clean-room verification
  procedure and release evidence.
- [`ENVIRONMENT.md`](ENVIRONMENT.md): Elan, Lean, Lake, mathlib, and manifest
  versions used for the clean verification.
- [`DEPENDENCY_REPORT.md`](DEPENDENCY_REPORT.md): local source-closure and
  external dependency audit.
- [`PROVENANCE.md`](PROVENANCE.md): mathematical credit and proof-route
  summary.

## Use from another Lean file

The root import deliberately exposes only the paper-specific public module:

```lean
import LogdetLean

#check LogdetLean.uniformNullEdgeworthTarget_proved
#check LogdetLean.paperTheoremFiveTwo_exact
#check LogdetLean.tendsto_scaledNullKolmogorovSup_closed
#check LogdetLean.tendsto_square_nullVSeries_sub_two_log
#check LogdetLean.paperEquationSixThree_exact
#check LogdetLean.paperEquationSixSix_exact
```

Lean reconstructs and checks proof terms. It does not generate a separate
long prose proof file for each theorem.

## License

The project-authored source and documentation are distributed under
`GPL-3.0-only`; see [`LICENSE`](LICENSE). Lean, mathlib, and other
downloaded dependencies retain their respective licenses.

## Citation

After Zenodo publishes this exact v1.1.2 ZIP, cite the version-specific DOI
shown on that record. Machine-readable citation metadata are in
[`CITATION.cff`](CITATION.cff). The archive SHA-256 independently identifies
the exact uploaded bytes.
