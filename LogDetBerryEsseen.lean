import Challenge

/-!
# Sharp Berry–Esseen bounds for Gaussian correlation log determinants

The thirteen public results below prove the explicit propositions in
`Challenge.lean` using the original v1.1.2 development in `LogdetLean/`.
All original theorem names remain available. The assumptions and remaining
conditional variance identity are documented in `docs/ASSUMPTIONS_AND_GAPS.md`.

Run `lake build` and then `lake env lean Verification.lean` to check the
statements and their axiom dependencies. See `README.md` for the mathematics.
-/

namespace LogDetBerryEsseen

/-- Proposition 4.1: independent beta-product representation. -/
theorem beta_product : Challenge.betaProduct :=
  LogdetLean.map_centeredSampleCorrelationDet_succ_eq_map_product_betaFactors

/-- Theorem 4.2: uniform signed first Edgeworth expansion. -/
theorem null_edgeworth : Challenge.nullEdgeworth :=
  LogdetLean.uniformNullEdgeworthTarget_proved

/-- Theorem 4.2: sharp Kolmogorov equivalent for the sample statistic. -/
theorem null_sharp_kolmogorov : Challenge.nullSharpKolmogorov :=
  LogdetLean.tendsto_uniformActualNullSharpKolmogorov_relative_error_zero

/-- Theorem 5.1: leading-term bound and the spectral cubic estimate. -/
theorem general_correlation_leading : Challenge.generalCorrelationLeading :=
  LogdetLean.paperTheoremFiveOne_exact

/-- Theorem 5.2: full-statistic bounds for population correlation `R`. -/
theorem general_correlation_full : Challenge.generalCorrelationFull :=
  LogdetLean.paperTheoremFiveTwo_exact

/-- Theorem 5.2: arbitrary population covariance and mean. -/
theorem general_covariance_full : Challenge.generalCovarianceFull :=
  LogdetLean.paperTheoremFiveTwo_arbitraryCovariance_exact

/-- Proposition 6.1, equation (6.2): uniform third-cumulant equivalent. -/
theorem third_cumulant_equivalent : Challenge.thirdCumulantEquivalent := by
  intro mseq pseq hp hadm
  exact LogdetLean.tendsto_nullASeries_div_uniformScale hp hadm

/-- Proposition 6.1, equation (6.3): growing-gap evaluation. -/
theorem growing_gap : Challenge.growingGap :=
  LogdetLean.paperEquationSixThree_exact

/-- Proposition 6.1, equation (6.4): positive-gap variance equivalent. -/
theorem variance_equivalent : Challenge.varianceEquivalent := by
  intro mseq pseq hp hadm hgap
  exact LogdetLean.tendsto_nullVSeries_div_uniformScale hp hadm hgap

/-- Proposition 6.1, equation (6.5): square variance refinement. -/
theorem square_variance : Challenge.squareVariance :=
  LogdetLean.tendsto_square_nullVSeries_sub_two_log

/-- Proposition 6.1, equation (6.6): exact hard-edge constants. -/
theorem hard_edge_constants : Challenge.hardEdgeConstants :=
  LogdetLean.paperEquationSixSix_exact

/-- Corollary 6.2: sharp supremum over every admissible sample size. -/
theorem square_supremum : Challenge.squareSupremum :=
  LogdetLean.tendsto_scaledNullKolmogorovSup_closed

/-- Corollary 6.2: eight-decimal rational interval. -/
theorem square_constant_decimal : Challenge.squareConstantDecimal :=
  LogdetLean.nullSharpSupremumConstant_decimal8

end LogDetBerryEsseen
