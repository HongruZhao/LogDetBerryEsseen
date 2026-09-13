import LogdetLean.MatrixSphericalExtension
import Mathlib.Tactic

/-!
# Exact reduction of the paper's original Gaussian sample model

The general-correlation theorems in the paper start with `m + 1` independent
observations having the literal law `N_p(mu, Sigma)`, where `Sigma` is an
arbitrary positive-definite covariance matrix.  The quantitative argument is
carried out on `m` independent standard Gaussian residual rows with population
correlation `R`.

This file proves the complete equality-in-law bridge between those two models.
The proof is deliberately split into the three semantic operations used in
the paper:

* a common location vector cancels after empirical centering;
* positive coordinatewise population standard deviations cancel after Pearson
  normalization, leaving `R = diag(Sigma)⁻¹ Sigma diag(Sigma)⁻¹`;
* centering `m + 1` Gaussian observations is exactly equivalent in law to `m`
  independent residual Gaussian coordinates.

The final theorem is stated for the Pearson matrix itself.  Consequently every
measurable statistic of that matrix, including its determinant and log
determinant, inherits the same exact law by composition.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators MatrixOrder RealInnerProductSpace

/-! ## The literal `N_p(mu, Sigma)` product sample -/

/-- One observation from the paper's original Gaussian model, written
literally as Mathlib's multivariate Gaussian with mean `mu` and covariance
`Sigma`. -/
def gaussianObservationMeasureWithMean {p : ℕ}
    (mu : CorrelationMatrix.Observation p) (Sigma : CovarianceMatrix p) :
    Measure (CorrelationMatrix.Observation p) :=
  multivariateGaussian mu Sigma.val

instance gaussianObservationMeasureWithMean_isProbability {p : ℕ}
    (mu : CorrelationMatrix.Observation p) (Sigma : CovarianceMatrix p) :
    IsProbabilityMeasure (gaussianObservationMeasureWithMean mu Sigma) := by
  unfold gaussianObservationMeasureWithMean
  infer_instance

/-- The law of `n` iid observations from `N_p(mu, Sigma)`. -/
def iidGaussianDataMeasureWithMean {p : ℕ} (n : ℕ)
    (mu : CorrelationMatrix.Observation p) (Sigma : CovarianceMatrix p) :
    Measure (GaussianData n p) :=
  Measure.pi fun _ : Fin n ↦ gaussianObservationMeasureWithMean mu Sigma

instance iidGaussianDataMeasureWithMean_isProbability {p : ℕ} (n : ℕ)
    (mu : CorrelationMatrix.Observation p) (Sigma : CovarianceMatrix p) :
    IsProbabilityMeasure (iidGaussianDataMeasureWithMean n mu Sigma) := by
  unfold iidGaussianDataMeasureWithMean
  infer_instance

/-- Translating a centered `N_p(0, Sigma)` observation by `mu` produces the
literal `N_p(mu, Sigma)` measure. -/
theorem map_add_mu_covarianceGaussian_eq_gaussianWithMean {p : ℕ}
    (mu : CorrelationMatrix.Observation p) (Sigma : CovarianceMatrix p) :
    Measure.map (fun x ↦ mu + x) Sigma.gaussianMeasure =
      gaussianObservationMeasureWithMean mu Sigma := by
  unfold CovarianceMatrix.gaussianMeasure
    gaussianObservationMeasureWithMean multivariateGaussian
  rw [Measure.map_map]
  · congr 1
    funext x
    simp
  · fun_prop
  · fun_prop

/-- Rowwise translation of the centered iid covariance sample is exactly the
paper's iid `N_p(mu, Sigma)` sample law. -/
theorem map_addLocationData_covarianceGaussian_eq_iidWithMean
    {n p : ℕ} (mu : CorrelationMatrix.Observation p)
    (Sigma : CovarianceMatrix p) :
    Measure.map (addLocationData mu)
        (covarianceGaussianDataMeasure n Sigma) =
      iidGaussianDataMeasureWithMean n mu Sigma := by
  let _ (k : Fin n) : IsProbabilityMeasure
      (Measure.map (fun x ↦ mu + x) Sigma.gaussianMeasure) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  unfold covarianceGaussianDataMeasure iidGaussianDataMeasureWithMean
  change Measure.map (fun x : GaussianData n p ↦ fun k ↦ mu + x k)
      (Measure.pi fun _ : Fin n ↦ Sigma.gaussianMeasure) = _
  rw [Measure.pi_map_pi (fun _ ↦ Measurable.aemeasurable (by fun_prop))]
  congr 1
  funext k
  exact map_add_mu_covarianceGaussian_eq_gaussianWithMean mu Sigma

/-! ## Translation, marginal scaling, and residual-coordinate reduction -/

/-- Exact Pearson-law translation invariance for the full iid sample. -/
theorem map_rawPearson_iidWithMean_eq_covarianceCentered
    {n p : ℕ} (hn : 0 < n) (mu : CorrelationMatrix.Observation p)
    (Sigma : CovarianceMatrix p) :
    Measure.map rawPearsonMatrix
        (iidGaussianDataMeasureWithMean n mu Sigma) =
      Measure.map rawPearsonMatrix
        (covarianceGaussianDataMeasure n Sigma) := by
  rw [← map_addLocationData_covarianceGaussian_eq_iidWithMean mu Sigma]
  rw [Measure.map_map measurable_rawPearsonMatrix
    (measurable_addLocationData mu)]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall fun x ↦
    rawPearsonMatrix_addLocationData hn mu x

/-- Translation and positive coordinatewise scaling reduce the paper's
`N_p(mu, Sigma)` Pearson matrix to the mean-zero population-correlation model.
The population correlation is definitionally
`diag(stdDev Sigma)⁻¹ * Sigma * diag(stdDev Sigma)⁻¹`. -/
theorem map_rawPearson_iidWithMean_eq_populationCorrelation
    {n p : ℕ} (hn : 0 < n) (mu : CorrelationMatrix.Observation p)
    (Sigma : CovarianceMatrix p) :
    Measure.map rawPearsonMatrix
        (iidGaussianDataMeasureWithMean n mu Sigma) =
      Measure.map rawPearsonMatrix
        (correlatedGaussianDataMeasure n Sigma.correlation) := by
  rw [map_rawPearson_iidWithMean_eq_covarianceCentered hn mu Sigma]
  exact map_rawPearson_covarianceGaussianDataMeasure_eq_correlation Sigma

/-- Exact original-model reduction used by the paper.  The Pearson matrix
computed from `m + 1` iid `N_p(mu, Sigma)` observations has exactly the same
law as the canonical Pearson matrix computed from `m` independent standard
Gaussian residual rows with population correlation `Sigma.correlation`.

This is an equality of matrix-valued pushforward measures, not an asymptotic
approximation. -/
theorem map_rawPearson_iidGaussian_succ_eq_canonicalResidual
    (m p : ℕ) (mu : CorrelationMatrix.Observation p)
    (Sigma : CovarianceMatrix p) :
    Measure.map rawPearsonMatrix
        (iidGaussianDataMeasureWithMean (m + 1) mu Sigma) =
      Measure.map (sampleCorrelationMatrix ∘
          correlateRows Sigma.correlation)
        (standardGaussianDataMeasure m p) := by
  rw [map_rawPearson_iidWithMean_eq_populationCorrelation
    (Nat.zero_lt_succ m) mu Sigma]
  rw [map_rawPearson_correlatedGaussianDataMeasure_eq_squareRoot]
  exact map_rawPearson_correlated_standard_succ_eq_residual
    m p Sigma.correlation

/-! ## Transfer to every measurable statistic of the Pearson matrix -/

/-- Every measurable scalar statistic of the Pearson matrix has the same law
under the paper's original sample and the canonical residual model. -/
theorem map_comp_rawPearson_iidGaussian_succ_eq_canonicalResidual
    (m p : ℕ) (mu : CorrelationMatrix.Observation p)
    (Sigma : CovarianceMatrix p)
    (f : Matrix (Fin p) (Fin p) ℝ → ℝ) (hf : Measurable f) :
    Measure.map (f ∘ rawPearsonMatrix)
        (iidGaussianDataMeasureWithMean (m + 1) mu Sigma) =
      Measure.map (f ∘ sampleCorrelationMatrix ∘
          correlateRows Sigma.correlation)
        (standardGaussianDataMeasure m p) := by
  have hcanonical : Measurable
      (@sampleCorrelationMatrix m p ∘ correlateRows Sigma.correlation) :=
    (measurable_normalizedGramFamily.comp measurable_dataColumns).comp
      (measurable_correlateRows Sigma.correlation)
  rw [← Measure.map_map hf measurable_rawPearsonMatrix]
  rw [map_rawPearson_iidGaussian_succ_eq_canonicalResidual]
  rw [Measure.map_map hf hcanonical]

/-- In particular, the sample-correlation determinant in the paper's
original model has exactly the canonical residual determinant law. -/
theorem map_det_rawPearson_iidGaussian_succ_eq_canonicalResidual
    (m p : ℕ) (mu : CorrelationMatrix.Observation p)
    (Sigma : CovarianceMatrix p) :
    Measure.map (fun x ↦ (rawPearsonMatrix x).det)
        (iidGaussianDataMeasureWithMean (m + 1) mu Sigma) =
      Measure.map
        (fun z ↦ (sampleCorrelationMatrix
          (correlateRows Sigma.correlation z)).det)
        (standardGaussianDataMeasure m p) := by
  have hdet : Measurable (fun A : Matrix (Fin p) (Fin p) ℝ ↦ A.det) := by
    simp_rw [Matrix.det_apply']
    fun_prop
  simpa [Function.comp_def] using
    map_comp_rawPearson_iidGaussian_succ_eq_canonicalResidual
      m p mu Sigma (fun A ↦ A.det) hdet

/-- The log determinant appearing in Theorems 5.1--5.2 likewise has exactly
the canonical residual log-determinant law. -/
theorem map_logDet_rawPearson_iidGaussian_succ_eq_canonicalResidual
    (m p : ℕ) (mu : CorrelationMatrix.Observation p)
    (Sigma : CovarianceMatrix p) :
    Measure.map (fun x ↦ Real.log (rawPearsonMatrix x).det)
        (iidGaussianDataMeasureWithMean (m + 1) mu Sigma) =
      Measure.map
        (fun z ↦ Real.log (sampleCorrelationMatrix
          (correlateRows Sigma.correlation z)).det)
        (standardGaussianDataMeasure m p) := by
  have hdet : Measurable (fun A : Matrix (Fin p) (Fin p) ℝ ↦ A.det) := by
    simp_rw [Matrix.det_apply']
    fun_prop
  simpa [Function.comp_def] using
    map_comp_rawPearson_iidGaussian_succ_eq_canonicalResidual
      m p mu Sigma (fun A ↦ Real.log A.det) hdet.log

end

end LogdetLean
