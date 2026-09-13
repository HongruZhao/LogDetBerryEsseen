# Main results and their Lean statements

This version covers three headline results. The target propositions are in
[Challenge.lean](../Challenge.lean), and their proofs are in
[LogDetBerryEsseen.lean](../LogDetBerryEsseen.lean).

| Paper result | Public theorem | Supporting proof |
|---|---|---|
| Theorem 4.2: uniform signed first Edgeworth expansion and sharp Kolmogorov equivalent | `LogDetBerryEsseen.sharp_null` | `uniformNullEdgeworthTarget_proved` and `tendsto_uniformActualNullSharpKolmogorov_relative_error_zero` in [NullUniformEdgeworthTarget.lean](../LogdetLean/NullUniformEdgeworthTarget.lean) |
| Theorem 5.2: finite general-correlation bounds | `LogDetBerryEsseen.general_correlation` | `paperTheoremFiveTwo_arbitraryCovariance_exact` in [GeneralRPaperExactTranslation.lean](../LogdetLean/GeneralRPaperExactTranslation.lean) |
| Corollary 6.2: sharp supremum over all sample sizes | `LogDetBerryEsseen.worst_case` | `tendsto_scaledNullKolmogorovSup_closed` in [NullSharpSupremum.lean](../LogdetLean/NullSharpSupremum.lean) |

Theorem 4.2 is packaged as one conjunction, so both the signed expansion and
sharp distance equivalent remain explicit. Theorem 5.2 includes the finer
matrix-dependent rate and the simpler dimension-only bound, for arbitrary
Gaussian mean and positive-definite population covariance.

## Identification with the sample in the paper

- [OriginalGaussianPearsonReduction.lean](../LogdetLean/OriginalGaussianPearsonReduction.lean)
  proves the law bridge from literal iid Gaussian observations to the residual
  model, including empirical centering and marginal-scale invariance.
- [GeneralRPaperExactTranslation.lean](../LogdetLean/GeneralRPaperExactTranslation.lean)
  identifies the Pearson matrix with the printed centered-scatter formula and
  proves the equality of laws for the general-correlation statistic.
- [NullCenterStandardization.lean](../LogdetLean/NullCenterStandardization.lean)
  identifies the actual standardized null statistic with the log-beta-sum law
  and the exact finite digamma centering.
- [StandardizedCumulantBridge.lean](../LogdetLean/StandardizedCumulantBridge.lean)
  identifies the exact variance, third cumulant magnitude, and skew scale
  with the finite series used in the paper.

These are proved finite identities, rather than additional model hypotheses.
The supporting lemmas are implementation dependencies, not additional
advertised paper results.
