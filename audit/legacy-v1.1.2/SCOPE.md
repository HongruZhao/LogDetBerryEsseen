# Verification scope

## Public statement boundary

The public mathematical interface consists of exactly the following thirteen Lean
declarations:

1. `map_centeredSampleCorrelationDet_succ_eq_map_product_betaFactors`
2. `uniformNullEdgeworthTarget_proved`
3. `tendsto_uniformActualNullSharpKolmogorov_relative_error_zero`
4. `paperTheoremFiveOne_exact`
5. `paperTheoremFiveTwo_exact`
6. `paperTheoremFiveTwo_arbitraryCovariance_exact`
7. `tendsto_nullASeries_div_uniformScale`
8. `paperEquationSixThree_exact`
9. `tendsto_nullVSeries_div_uniformScale`
10. `tendsto_square_nullVSeries_sub_two_log`
11. `paperEquationSixSix_exact`
12. `tendsto_scaledNullKolmogorovSup_closed`
13. `nullSharpSupremumConstant_decimal8`

They correspond to Proposition 4.1, Theorems 4.2, 5.1, and 5.2, the uniform
complete equations (6.2)--(6.6) of Proposition 6.1, and Corollary 6.2.
Equation (6.1) is the formal definition used by these endpoints rather than a
separate theorem endpoint. The exact
statement relations and named law bridges are recorded in
[`STATEMENT_CROSSWALK.md`](STATEMENT_CROSSWALK.md).

`LogdetLean/PaperTable2Endpoints.lean` is the narrow public interface.
Declarations present only because they lie in the transitive dependency
closure are not additional advertised paper results.

## Included formal content

The source closure contains the formal ingredients required by the thirteen
endpoints, including:

- the centered Gaussian sample-correlation determinant and independent beta
  product law;
- exact log-beta laws, centering, variance, and cumulant series;
- characteristic-function estimates, signed first Edgeworth comparison,
  full-frequency control, and Kolmogorov transfer;
- all-array uniform `A` and positive-gap uniform `V` equivalents;
- the constrained null supremum and its symbolic and decimal constants;
- the Gaussian/Wishart general-correlation decomposition, analytic transform,
  leading-term bound, nonlinear perturbation, and simplified rate; and
- exact original-sample-to-canonical and arbitrary-covariance law bridges
  used by the paper-facing general-correlation statements.

## Explicit exclusions

This capsule does **not** claim formal verification of:

- the Heiny--Johnston--Prochno bound quoted as equation (3.1), which is an
  externally cited theorem rather than a new theorem of this paper;
- every displayed or numbered equation in the paper;
- the optional exact general-correlation variance identity unless it is
  separately added to the public endpoint list and freshly audited;
- bibliography, provenance, priority, originality, or the accuracy of
  natural-language descriptions;
- numerical simulations, figures, hardware timings, computing-cost claims,
  power recommendations, or other empirical conclusions;
- conjectured sharper rates or open problems;
- any result belonging only to an earlier paper or another local project; or
- any theorem merely present in mathlib or in the local dependency cone but
  absent from the public list above.

## Meaning of verification

Kernel checking establishes a conditional statement: the encoded conclusion
follows from the encoded assumptions and the axioms printed by Lean. It does
not by itself establish that the formal definitions are the intended
statistical model. That translation question is addressed by the exact law
bridges listed in the crosswalk and must be reviewed separately from kernel
correctness.

The human-written manuscript and supplement remain ordinary mathematical
prose. They are not themselves checked by the Lean kernel.
