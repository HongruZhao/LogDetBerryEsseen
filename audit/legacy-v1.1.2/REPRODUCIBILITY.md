# Reproducibility

This document belongs to release v1.1.2. The archive SHA-256 identifies the
exact bytes and is recorded on the Zenodo record and repository landing page.

## Exact environment

The capsule records:

- Lean toolchain `leanprover/lean4:v4.33.0-rc2`;
- Lean commit `d8b18978322de05a8f3dba51ef03cf5461676c17`; and
- mathlib commit `641fbd329d4ffb62bef83c51f54088469056bd36`;
- Elan `4.2.3`; and
- Lake `5.0.0-src+d8b1897`.

`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` are the
machine-readable pins. The manifest contains only public Git dependencies;
it contains no private path dependency.

## Clean verification procedure

Use a newly extracted copy of the final archive. Do not copy an existing
`.lake/` directory or compiled `.olean` files into it.

1. Confirm that the extraction contains no `.git`, `.lake`, `.olean`, or
   other compiled cache.
2. Before creating `.lake/`, run:

   ```bash
   ./scripts/verify-source.sh
   ```

3. Install the pinned dependencies and obtain the compatible mathlib cache:

   ```bash
   lake update
   lake exe cache get
   ```

4. Build the capsule:

   ```bash
   lake build
   ```

5. Check every advertised theorem type and print its kernel dependencies:

   ```bash
   lake env lean LogdetLean/PaperAxiomAudit.lean
   ```

The commands must be run from the capsule root. The first setup requires
network access; later builds may use the downloaded cache.

## Pass conditions

A release verification passes only if all of the following hold in the fresh
extraction:

- the source audit exits successfully;
- `lake build` exits successfully;
- `PaperAxiomAudit.lean` elaborates successfully;
- exactly thirteen endpoint axiom reports are present;
- every endpoint reports exactly `propext`, `Classical.choice`, and
  `Quot.sound`, the set reproduced in the clean release run;
- the source contains no `sorry`, `admit`, `sorryAx`, project-defined axiom,
  postulate, unsafe/native trust escape, unavailable local import, private
  path dependency, compiled proof artifact, or machine-specific path;
- the theorem types match the recorded public boundary; and
- the checksum verification succeeds after extracting the final ZIP.

No success is inferred merely from the existence of source files or from a
build performed in another workspace.

## Release evidence

This finalized capsule contains the following generated records:

- `BUILD_LOG.txt`: complete fresh dependency, build, and audit output;
- `AXIOM_REPORT.txt`: the thirteen `#print axioms` results;
- `SOURCE_AUDIT.txt`: the fail-closed source-audit output;
- `THEOREM_TYPES.txt`: exact elaborated endpoint types;
- `PUBLIC_FILE_MANIFEST.txt`: the complete released file list; and
- `SHA256SUMS`: checksums for every released file except `SHA256SUMS` itself.

Those files are evidence only for the exact archive whose checksums they
record. A changed Lean source, toolchain file, manifest, or documentation file
requires regenerating the manifest, checksums, and any affected verification
report.

## Convenience script

`scripts/verify.sh` combines the source audit, build, and thirteen-endpoint axiom
check. Because the source audit intentionally rejects `.lake/`, run the
script from a clean extraction before dependency setup has created that
directory. For an already initialized tree, use the numbered manual procedure
above on a new extraction.
