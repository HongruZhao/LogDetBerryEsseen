import LogdetLean.GeneralRPaperBounds
import LogdetLean.GeneralRCenterIdentity
import LogdetLean.GeneralRCenteredSampleBridge
import LogdetLean.OriginalGaussianPearsonReduction
import Mathlib.Tactic

/-!
# Literal Lean statements of the paper's general-correlation theorems

This module closes the semantic gap between the canonical `m`-row Wishart
space used by the proof and the statistic printed in Theorems 5.1--5.2 of
Zhao, *Sharp Berry--Esseen Bounds for the Log Determinant of a Gaussian
Sample Correlation Matrix*.

The printed data consist of `n = m + 1` iid observations with the literal law
`N_p(mu, Sigma)`.  Their empirical Pearson matrix is `rawPearsonMatrix`, the
population correlation is `Sigma.correlation`, and the printed statistic is

`(log det Rhat - log det R - b_(m,p)) / s_R`.

The preceding modules prove, rather than assume, that

* the printed Pearson matrix has the canonical residual-coordinate law; and
* the canonical deterministic center equals `log det R + b_(m,p)` exactly.

The final declarations below state both clauses of each paper theorem under
one universal constant.  They introduce no new probabilistic hypothesis.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory Real

/-! ## The literal `N_p(mu,R)` sample in the printed theorem -/

/-- The paper's `m + 1` iid `N_p(mu,R)` sample, written directly with
Mathlib's `multivariateGaussian` constructor. -/
def paperIidGaussianCorrelationSampleMeasure (m : ℕ) {p : ℕ}
    (mu : CorrelationMatrix.Observation p) (R : CorrelationMatrix p) :
    Measure (GaussianData (m + 1) p) :=
  Measure.pi fun _ : Fin (m + 1) ↦ multivariateGaussian mu R.val

instance paperIidGaussianCorrelationSampleMeasure_isProbability
    (m : ℕ) {p : ℕ} (mu : CorrelationMatrix.Observation p)
    (R : CorrelationMatrix p) :
    IsProbabilityMeasure (paperIidGaussianCorrelationSampleMeasure m mu R) := by
  unfold paperIidGaussianCorrelationSampleMeasure
  infer_instance

/-- The translated realization used in the centered-sample bridge is exactly
Mathlib's literal multivariate Gaussian with mean `mu` and covariance `R`. -/
theorem generalRGaussianObservationMeasure_eq_multivariateGaussian
    {p : ℕ} (mu : CorrelationMatrix.Observation p)
    (R : CorrelationMatrix p) :
    generalRGaussianObservationMeasure mu R =
      multivariateGaussian mu R.val := by
  unfold generalRGaussianObservationMeasure CorrelationMatrix.gaussianMeasure
    multivariateGaussian
  rw [Measure.map_map]
  · congr 1
    funext x
    simp
  · fun_prop
  · fun_prop

/-- The product measure in the centered-sample bridge is definitionally the
same iid `N_p(mu,R)` sample as the one displayed above. -/
theorem originalGeneralRSampleMeasure_eq_literalGaussian
    (m : ℕ) {p : ℕ} (mu : CorrelationMatrix.Observation p)
    (R : CorrelationMatrix p) :
    originalGeneralRSampleMeasure m mu R =
      paperIidGaussianCorrelationSampleMeasure m mu R := by
  unfold originalGeneralRSampleMeasure
    paperIidGaussianCorrelationSampleMeasure
  congr 1
  funext k
  exact generalRGaussianObservationMeasure_eq_multivariateGaussian mu R

/-- The scalar functional printed in equation (2.8) of the manuscript,
applied to a candidate Pearson matrix. -/
def paperGeneralRStandardizeMatrix {p : ℕ} (m : ℕ)
    (R : CorrelationMatrix p) (Rhat : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  (Real.log Rhat.det - Real.log R.val.det -
      nullCenterDigammaSeries m p) / generalRProxyScale m R

theorem measurable_paperGeneralRStandardizeMatrix {m p : ℕ}
    (R : CorrelationMatrix p) :
    Measurable (paperGeneralRStandardizeMatrix m R) := by
  unfold paperGeneralRStandardizeMatrix
  have hdet : Measurable
      (fun S : Matrix (Fin p) (Fin p) ℝ ↦ S.det) := by
    simp_rw [Matrix.det_apply']
    fun_prop
  exact (((hdet.log.sub_const _).sub_const _).div_const _)

/-- The paper's statistic on the original `n = m + 1` raw observations.
The function depends on the population correlation `R`; the data law below
supplies `R = correlation(Sigma)`. -/
def paperGeneralRStatistic {p : ℕ} (m : ℕ) (R : CorrelationMatrix p)
    (x : GaussianData (m + 1) p) : ℝ :=
  paperGeneralRStandardizeMatrix m R (rawPearsonMatrix x)

theorem measurable_paperGeneralRStatistic {m p : ℕ}
    (R : CorrelationMatrix p) : Measurable (paperGeneralRStatistic m R) := by
  exact (measurable_paperGeneralRStandardizeMatrix R).comp
    measurable_rawPearsonMatrix

/-- The matrix used inside `paperGeneralRStatistic` is literally the
centered-scatter-and-diagonal-normalization matrix displayed in the paper. -/
theorem paperGeneralRSampleCorrelation_eq_printedScatterFormula
    {m p : ℕ} (x : GaussianData (m + 1) p) :
    rawPearsonMatrix x = originalPearsonFromCenteredScatter x :=
  originalGeneralRSampleCorrelation_eq_centeredScatterNormalization x

/-- On the canonical residual space, the statistic printed in the paper is
pointwise identical to the already proved `ZRmpStatistic`. -/
theorem paperGeneralRStandardizeMatrix_canonical_eq_ZRmpStatistic
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p)
    (z : GaussianData m p) :
    paperGeneralRStandardizeMatrix m R
        (sampleCorrelationMatrix (correlateRows R z)) =
      ZRmpStatistic m R z := by
  unfold paperGeneralRStandardizeMatrix ZRmpStatistic
    GeneralRDecomposition.sampleCorrelation
  rw [GeneralRDecomposition.logDetCenter_eq_logDet_add_nullCenterDigammaSeries
    h R]
  ring

/-- Exact law identity from the paper's literal iid `N_p(mu,Sigma)` sample
to the canonical statistic used in the quantitative proof.  This equality is
finite-sample and has no limiting qualification. -/
theorem map_paperGeneralRStatistic_iidGaussian_eq_ZRmpStatistic
    {m p : ℕ} (h : Admissible m p)
    (mu : CorrelationMatrix.Observation p) (Sigma : CovarianceMatrix p) :
    Measure.map (paperGeneralRStatistic m Sigma.correlation)
        (iidGaussianDataMeasureWithMean (m + 1) mu Sigma) =
      Measure.map (ZRmpStatistic m Sigma.correlation)
        (standardGaussianDataMeasure m p) := by
  let f : Matrix (Fin p) (Fin p) ℝ → ℝ :=
    paperGeneralRStandardizeMatrix m Sigma.correlation
  have hf : Measurable f :=
    measurable_paperGeneralRStandardizeMatrix Sigma.correlation
  calc
    Measure.map (paperGeneralRStatistic m Sigma.correlation)
        (iidGaussianDataMeasureWithMean (m + 1) mu Sigma) =
      Measure.map (f ∘ rawPearsonMatrix)
        (iidGaussianDataMeasureWithMean (m + 1) mu Sigma) := by rfl
    _ = Measure.map
        (f ∘ sampleCorrelationMatrix ∘ correlateRows Sigma.correlation)
        (standardGaussianDataMeasure m p) :=
      map_comp_rawPearson_iidGaussian_succ_eq_canonicalResidual
        m p mu Sigma f hf
    _ = Measure.map (ZRmpStatistic m Sigma.correlation)
        (standardGaussianDataMeasure m p) := by
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun z ↦
        paperGeneralRStandardizeMatrix_canonical_eq_ZRmpStatistic
          h Sigma.correlation z

/-- Exact law identity in the correlation-matrix parametrization used in
Theorem 5.2: `m + 1` iid `N_p(mu,R)` observations, empirical centering, and
the printed finite center are sent to the canonical `ZRmpStatistic` law. -/
theorem map_paperGeneralRStatistic_originalCorrelation_eq_ZRmpStatistic
    {m p : ℕ} (h : Admissible m p)
    (mu : CorrelationMatrix.Observation p) (R : CorrelationMatrix p) :
    Measure.map (paperGeneralRStatistic m R)
        (originalGeneralRSampleMeasure m mu R) =
      Measure.map (ZRmpStatistic m R)
        (standardGaussianDataMeasure m p) := by
  have hfun : paperGeneralRStatistic m R = originalGeneralRStatistic m R := by
    funext x
    unfold paperGeneralRStatistic paperGeneralRStandardizeMatrix
      originalGeneralRStatistic generalRMatrixStatistic
      originalGeneralRSampleCorrelation
    rw [GeneralRDecomposition.logDetCenter_eq_logDet_add_nullCenterDigammaSeries
      h R]
    ring
  rw [hfun]
  exact map_originalGeneralRStatistic_eq_ZRmpStatistic m p mu R

/-- The same law identity with the source measure written literally as the
finite iid product of `multivariateGaussian mu R.val`. -/
theorem map_paperGeneralRStatistic_literalCorrelation_eq_ZRmpStatistic
    {m p : ℕ} (h : Admissible m p)
    (mu : CorrelationMatrix.Observation p) (R : CorrelationMatrix p) :
    Measure.map (paperGeneralRStatistic m R)
        (paperIidGaussianCorrelationSampleMeasure m mu R) =
      Measure.map (ZRmpStatistic m R)
        (standardGaussianDataMeasure m p) := by
  rw [← originalGeneralRSampleMeasure_eq_literalGaussian m mu R]
  exact map_paperGeneralRStatistic_originalCorrelation_eq_ZRmpStatistic h mu R

/-- Finite full-statistic bound stated directly for the paper's original
`m + 1` iid `N_p(mu,Sigma)` observations. -/
theorem kolmogorovDistance_paperGeneralRStatistic_le_paperRate
    {m p : ℕ} (h : Admissible m p)
    (mu : CorrelationMatrix.Observation p) (Sigma : CovarianceMatrix p) :
    kolmogorovDistance
        (Measure.map (paperGeneralRStatistic m Sigma.correlation)
          (iidGaussianDataMeasureWithMean (m + 1) mu Sigma))
        (gaussianReal 0 1) ≤
      generalRPaperUniversalConstant *
        generalRPaperFullRate m Sigma.correlation := by
  rw [map_paperGeneralRStatistic_iidGaussian_eq_ZRmpStatistic h mu Sigma]
  exact kolmogorovDistance_ZRmpStatistic_le_paperRate
    h Sigma.correlation

/-- Finite simplified bound stated directly for the paper's original
`m + 1` iid `N_p(mu,Sigma)` observations. -/
theorem kolmogorovDistance_paperGeneralRStatistic_le_simplePaperRate
    {m p : ℕ} (h : Admissible m p)
    (mu : CorrelationMatrix.Observation p) (Sigma : CovarianceMatrix p) :
    kolmogorovDistance
        (Measure.map (paperGeneralRStatistic m Sigma.correlation)
          (iidGaussianDataMeasureWithMean (m + 1) mu Sigma))
        (gaussianReal 0 1) ≤
      generalRPaperSimpleUniversalConstant *
        (nullLambdaSeries m p + generalRDimensionCubeRootRate p) := by
  rw [map_paperGeneralRStatistic_iidGaussian_eq_ZRmpStatistic h mu Sigma]
  exact kolmogorovDistance_ZRmpStatistic_le_simplePaperRate
    h Sigma.correlation

/-- The full finite bound in Theorem 5.2, in the theorem's own
correlation-matrix parametrization and on its original centered sample. -/
theorem kolmogorovDistance_paperGeneralRStatistic_correlation_le_paperRate
    {m p : ℕ} (h : Admissible m p)
    (mu : CorrelationMatrix.Observation p) (R : CorrelationMatrix p) :
    kolmogorovDistance
        (Measure.map (paperGeneralRStatistic m R)
          (paperIidGaussianCorrelationSampleMeasure m mu R))
        (gaussianReal 0 1) ≤
      generalRPaperUniversalConstant * generalRPaperFullRate m R := by
  rw [map_paperGeneralRStatistic_literalCorrelation_eq_ZRmpStatistic h mu R]
  exact kolmogorovDistance_ZRmpStatistic_le_paperRate h R

/-- The simplified finite bound in Theorem 5.2, in the theorem's own
correlation-matrix parametrization and on its original centered sample. -/
theorem kolmogorovDistance_paperGeneralRStatistic_correlation_le_simplePaperRate
    {m p : ℕ} (h : Admissible m p)
    (mu : CorrelationMatrix.Observation p) (R : CorrelationMatrix p) :
    kolmogorovDistance
        (Measure.map (paperGeneralRStatistic m R)
          (paperIidGaussianCorrelationSampleMeasure m mu R))
        (gaussianReal 0 1) ≤
      generalRPaperSimpleUniversalConstant *
        (nullLambdaSeries m p + generalRDimensionCubeRootRate p) := by
  rw [map_paperGeneralRStatistic_literalCorrelation_eq_ZRmpStatistic h mu R]
  exact kolmogorovDistance_ZRmpStatistic_le_simplePaperRate h R

/-- The explicit upper bound in the `Moreover` clause of Theorem 5.1,
written in the algebraically identical form
`1 / (2 * sqrt 2 * sqrt m) = 1 / (2^(3/2) * sqrt m)`. -/
def generalRPaperRhoSimpleBound (m : ℕ) : ℝ :=
  1 / (2 * Real.sqrt 2 * Real.sqrt (m : ℝ))

private theorem generalRPaperFullRate_nonneg_exact
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    0 ≤ generalRPaperFullRate m R := by
  have hlambda : 0 ≤ nullLambdaSeries m p := (nullLambdaSeries_pos h).le
  have hp : 0 ≤ 1 / (p : ℝ) := by positivity
  have hs : 0 < generalRProxyScale m R := generalRProxyScale_pos h R
  have hrho : 0 ≤ generalRSpectralCubicRate m R := by
    unfold generalRSpectralCubicRate generalRCubicRateRho
    positivity
  have hq : 0 ≤ generalRNonlinearCubeRootRate m R :=
    (generalRNonlinearCubeRootRate_pos h R).le
  unfold generalRPaperFullRate generalRPaperLeadingRate
  positivity

/-- Literal bundled form of Theorem 5.1.  One universal constant controls
the leading Kolmogorov bound, and the same declaration includes the printed
uniform estimate for `rho_R`. -/
theorem paperTheoremFiveOne_exact :
    ∃ C : ℝ, 0 < C ∧
      ∀ {m p : ℕ}, ∀ (_h : Admissible m p), ∀ R : CorrelationMatrix p,
        kolmogorovDistance
            (Measure.map
              (fun z ↦ GeneralRDecomposition.M_R m R z /
                generalRProxyScale m R)
              (standardGaussianDataMeasure m p))
            (gaussianReal 0 1) ≤
              C * generalRPaperLeadingRate m R ∧
        generalRSpectralCubicRate m R ≤ generalRPaperRhoSimpleBound m := by
  refine ⟨generalRPaperUniversalConstant,
    generalRPaperUniversalConstant_pos, ?_⟩
  intro m p h R
  exact ⟨kolmogorovDistance_M_R_proxyScale_le_paperRate h R,
    generalRSpectralCubicRate_le_simple h R⟩

/-- Literal bundled form of Theorem 5.2.  The quantifiers, the original
`m + 1` centered `N_p(mu,R)` sample, the printed statistic, and both displayed
bounds occur in one proposition.  One universal constant simultaneously
satisfies the full and the `in particular` clauses. -/
theorem paperTheoremFiveTwo_exact :
    ∃ C : ℝ, 0 < C ∧
      ∀ {m p : ℕ}, ∀ (_h : Admissible m p),
        ∀ (mu : CorrelationMatrix.Observation p),
        ∀ R : CorrelationMatrix p,
          kolmogorovDistance
              (Measure.map (paperGeneralRStatistic m R)
                (paperIidGaussianCorrelationSampleMeasure m mu R))
              (gaussianReal 0 1) ≤ C * generalRPaperFullRate m R ∧
          kolmogorovDistance
              (Measure.map (paperGeneralRStatistic m R)
                (paperIidGaussianCorrelationSampleMeasure m mu R))
              (gaussianReal 0 1) ≤
                C * (nullLambdaSeries m p +
                  generalRDimensionCubeRootRate p) := by
  refine ⟨generalRPaperSimpleUniversalConstant,
    generalRPaperSimpleUniversalConstant_pos, ?_⟩
  intro m p h mu R
  have hfull :=
    kolmogorovDistance_paperGeneralRStatistic_correlation_le_paperRate
      h mu R
  have hsimple :=
    kolmogorovDistance_paperGeneralRStatistic_correlation_le_simplePaperRate
      h mu R
  have hrate : 0 ≤ generalRPaperFullRate m R :=
    generalRPaperFullRate_nonneg_exact h R
  have hconstants : generalRPaperUniversalConstant ≤
      generalRPaperSimpleUniversalConstant := by
    unfold generalRPaperSimpleUniversalConstant
    nlinarith [generalRPaperUniversalConstant_pos]
  exact ⟨hfull.trans (mul_le_mul_of_nonneg_right hconstants hrate), hsimple⟩

/-- Arbitrary-covariance version of Theorem 5.2 for the literal iid
`N_p(mu,Sigma)` model from the paper's model section.  Its population
correlation is definitionally `Sigma.correlation`. -/
theorem paperTheoremFiveTwo_arbitraryCovariance_exact :
    ∃ C : ℝ, 0 < C ∧
      ∀ {m p : ℕ}, ∀ (_h : Admissible m p),
        ∀ (mu : CorrelationMatrix.Observation p),
        ∀ Sigma : CovarianceMatrix p,
          kolmogorovDistance
              (Measure.map
                (paperGeneralRStatistic m Sigma.correlation)
                (iidGaussianDataMeasureWithMean (m + 1) mu Sigma))
              (gaussianReal 0 1) ≤
                C * generalRPaperFullRate m Sigma.correlation ∧
          kolmogorovDistance
              (Measure.map
                (paperGeneralRStatistic m Sigma.correlation)
                (iidGaussianDataMeasureWithMean (m + 1) mu Sigma))
              (gaussianReal 0 1) ≤
                C * (nullLambdaSeries m p +
                  generalRDimensionCubeRootRate p) := by
  refine ⟨generalRPaperSimpleUniversalConstant,
    generalRPaperSimpleUniversalConstant_pos, ?_⟩
  intro m p h mu Sigma
  have hfull :=
    kolmogorovDistance_paperGeneralRStatistic_le_paperRate h mu Sigma
  have hsimple :=
    kolmogorovDistance_paperGeneralRStatistic_le_simplePaperRate h mu Sigma
  have hrate : 0 ≤ generalRPaperFullRate m Sigma.correlation :=
    generalRPaperFullRate_nonneg_exact h Sigma.correlation
  have hconstants : generalRPaperUniversalConstant ≤
      generalRPaperSimpleUniversalConstant := by
    unfold generalRPaperSimpleUniversalConstant
    nlinarith [generalRPaperUniversalConstant_pos]
  have hfull' :
      kolmogorovDistance
          (Measure.map
            (paperGeneralRStatistic m Sigma.correlation)
            (iidGaussianDataMeasureWithMean (m + 1) mu Sigma))
          (gaussianReal 0 1) ≤
        generalRPaperSimpleUniversalConstant *
          generalRPaperFullRate m Sigma.correlation := by
    exact hfull.trans (mul_le_mul_of_nonneg_right hconstants hrate)
  exact ⟨hfull', hsimple⟩

end

end LogdetLean
