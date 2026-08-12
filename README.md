# Lean verification for *Sharp Berry--Esseen Bounds for the Log Determinant of a Gaussian Sample Correlation Matrix*

This repository accompanies the paper-specific Lean 4 verification capsule.

## Permanent v1.1.1 archive

- Zenodo DOI: <https://doi.org/10.5281/zenodo.21896819>
- ZIP SHA-256: `9b631de6fa41926805f2863673c3d64648bddacad79e166e99d395494069b682`
- Lean: `4.33.0-rc2`, commit `d8b18978322de05a8f3dba51ef03cf5461676c17`
- Lake: `5.0.0-src+d8b1897`
- Elan used for the recorded run: `4.2.3`
- mathlib: `641fbd329d4ffb62bef83c51f54088469056bd36`

The final ZIP was verified from a fresh extraction. The source audit, complete
build, eleven public endpoint checks, sorry audit, exact permitted axiom audit,
and eight-module `leanchecker` run all passed.

## Reproduce the verification

Download the ZIP from Zenodo, extract it into a new folder, open a terminal in
that folder, and run:

```bash
./scripts/verify.sh
```

The first run needs network access to obtain the pinned toolchain and
dependencies. A successful run ends with:

```text
Paper-specific Lean verification passed.
```

## What the public interface contains

The capsule advertises eleven stable public endpoints for Proposition 4.1,
Theorems 4.2, 5.1, and 5.2, Proposition 6.1, and Corollary 6.2. Proposition
6.1 has three public entry points for (6.2), (6.4), and (6.5), with supporting
declarations in the same dependency cone for (6.1), (6.3), and (6.6).

Lean checks encoded declarations and their formal dependencies. It does not
kernel-check the manuscript's English prose, citations, priority claims, or
the ordinary mathematical exposition in the supplement.

## Before this draft replaces the repository README

The permanent v1.1.1 ZIP contains a metadata inconsistency: its
`CITATION.cff` says `GPL-3.0-or-later`, whereas the Zenodo record says
`GPL-3.0-only`; its internal crosswalk also retains the earlier narrower
Proposition 6.1 description. Because changing those files changes the archive
checksum, publish a corrected v1.1.2 archive before presenting all release
metadata as identical.
