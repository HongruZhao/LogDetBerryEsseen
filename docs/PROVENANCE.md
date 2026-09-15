# Provenance

This project formalizes three main results in Hongru Zhao's *Sharp
Berry–Esseen Bounds for the Log Determinant of a Gaussian Sample Correlation
Matrix*: Theorem 4.2, Theorem 5.2, and Corollary 6.2.

The sources were extracted from the supplied v1.1.2 Lean capsule, whose SHA-256 is
`563800a00392742c4c4aa1e37296d274bd66b61abf7ec7a11844d1258220dc4e`.
Both supplied manuscript source versions were used for the statement review.
The original capsule is identified in the paper by
[DOI 10.5281/zenodo.21898548](https://doi.org/10.5281/zenodo.21898548).
That DOI does not identify this revised GitHub source tree.

The full v1.1.4 formalization is published as
[DOI 10.5281/zenodo.22739087](https://doi.org/10.5281/zenodo.22739087).
The matching GitHub release mirrors that ZIP exactly. The GitHub source tree
keeps the concise three-result interface, whose statement, proof-entry, and
verification files are byte-identical to those in the full archive.

Revision 1.1.4 narrows the public interface to three theorem statements and
retains their transitive supporting modules. Five unconditional definitions
and lemmas were extracted without changing their bodies into
`LogdetLean/GeneralRVarianceBasics.lean`; one importing module was updated.
The September 14 synchronization also imports the archive's additions to
`GeneralRCenterIdentity.lean` and `HardEdgeConstant.lean`. The other shared proof
files are unchanged except for the existing focused import in
`KibbleCovarianceBounds.lean`. The [version correspondence](ZENODO_RELEASE.md)
and [verification record](VERIFICATION.md) document these differences.

The historical ZIPs and retired source modules remain in [archives](../archives/README.md),
and earlier audit reports remain under `audit/`. The broader v1.1.3 source
package is also available in [Git history](https://github.com/HongruZhao/LogDetBerryEsseen/tree/ec41febe106f5b4c543bf908ff6e25764fe210bd).

The proof uses classical Gaussian, beta, gamma, Bartlett, and Wishart
identities, developed in the included Lean sources or the pinned Mathlib
library. A cited paper is not imported as an unproved axiom. The manuscript
provides the mathematical bibliography; this repository does not establish
priority or certify that bibliography.

The public statement/proof layout follows the examples
[PrimeGaps186](https://github.com/openai/PrimeGaps186) and
[NavierStokesAndEuler](https://github.com/openai/NavierStokesAndEuler).
The verification record reports only checks actually run for this project.
