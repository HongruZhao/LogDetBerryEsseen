# Mathematical provenance

This capsule distinguishes formal deduction from scholarly attribution. Lean
checks proof terms; it does not determine who first proved a mathematical
result or whether a citation is historically complete.

No cited paper is imported as an unproved project axiom. A formal dependency
is either proved in the included Lean source or imported from the pinned
mathlib dependency. Citations below identify mathematical origins, standard
ingredients, or proof routes; they are not trust escapes from the Lean
kernel.

This document describes the proof routes represented in the source. The
successful fresh and post-ZIP verification runs are recorded in the release
evidence specified in `REPRODUCIBILITY.md`.

## Independent beta product

The exact beta-product representation for normalized Gram and correlation
determinants is classical. The parameterization and sequential
Gram--Schmidt route used here agree with Alain Rouault, *Asymptotic behavior
of random determinants in the Laguerre, Gram and Jacobi ensembles* (2007),
and his earlier pathwise treatment of uniform Gram and Wishart ensembles.
The underlying Gaussian quadratic-form and Wishart decompositions go back to
work including Bartlett and Cochran.

The capsule proves the centered Gaussian sample statement directly. The
literature is credited for the mathematical result and route, not used as an
axiom.

## Mellin transforms, cumulants, and the null expansion

The beta Mellin transform and gamma-function identities are classical. The
Lean source develops the exact log-beta law, cumulant series, characteristic
function, and full-frequency estimates needed for this paper. The resulting
endpoint-uniform signed first Edgeworth assembly is paper-specific.

The finite normal-approximation result of Heiny, Johnston, and Prochno and the
higher-order proportional-regime calculations of Xie and Sun are relevant
comparisons in the manuscript. They are not substituted for the two Theorem
4.2 endpoints and are not imported as formal assumptions.

## General population correlation

The proof uses classical Gaussian and Wishart structures, including the
Wishart density, matrix-gamma transform, orthogonal invariance, and
partitioned-Wishart identities commonly presented in multivariate-analysis
references such as Muirhead. The decomposition and several covariance and
transform calculations also build on formulas developed in Hongru Zhao's
earlier work on Gaussian sample-correlation log determinants.

For this capsule, every non-mathlib identity required by the thirteen advertised
endpoints is represented by included Lean source. The paper-facing endpoints
also contain the finite law bridges from the literal iid Gaussian sample to
the canonical residual model.

Four elementary variance and trace declarations formerly stored with broader
reusable computations have been placed in
`LogdetLean/GeneralRVarianceTraceBasics.lean`. Their statements and proofs are
unchanged in substance; the paper-specific extraction avoids publishing an
unrelated earlier-paper module.

## Uniform asymptotics and the square constant

The `A` and `V` equivalents are proved from positive reciprocal-power series,
elementary sum comparisons, and exact beta cumulants. Public endpoint
`paperEquationSixThree_exact` packages the stronger explicit tail bounds and
the growing-gap equivalent that establish (6.3). Public endpoint
`paperEquationSixSix_exact` packages the exact hard-edge recurrence, the
square constant, and strict decrease required by (6.6). The square constant
is evaluated through the corresponding hard-edge series, the classical values
of the even zeta sum, and the positive series defining `zeta(3)`. Lean
separately checks the rational interval used for the displayed decimal.

## What this record does not claim

This summary does not claim priority for classical ingredients, certify the
bibliography, or assert that every informal analogy in the manuscript is a
formal proof dependency. Exact paper-to-Lean statement relations are recorded
separately in [`STATEMENT_CROSSWALK.md`](STATEMENT_CROSSWALK.md).
