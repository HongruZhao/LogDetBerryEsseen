import LogdetLean.MatrixSphericalExtension
import LogdetLean.GeneralRStatistic

/-!
# Original centered Gaussian sample versus the residual-coordinate model

The paper starts with `m + 1` independent observations having arbitrary
population location `mu` and correlation matrix `R`, removes the sample mean,
and forms the Pearson sample-correlation matrix.  The quantitative general-`R`
development uses instead `m` independent mean-zero Gaussian residual rows.

This file makes that change of probability space explicit.  The original
sample law is defined as a finite product law, so independence and identical
distribution are part of the formal statement.  The equality in law of the
two Pearson matrices is then passed through the exact centered log-determinant
standardization used by `ZRmpStatistic`.

The geometric content is supplied by
`map_rawPearson_correlated_standard_succ_eq_residual`, which identifies the
centered subspace of `m + 1` observations isometrically with `m` Euclidean
residual coordinates.  No asymptotic approximation is used here.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory

/-! ## The literal iid sample law -/

/-- The law of one `N_p(mu,R)` observation, represented as a translate of the
mean-zero Gaussian measure with covariance (and correlation) `R`. -/
def generalRGaussianObservationMeasure {p : ℕ}
    (mu : CorrelationMatrix.Observation p) (R : CorrelationMatrix p) :
    Measure (CorrelationMatrix.Observation p) :=
  Measure.map (fun x ↦ mu + x) R.gaussianMeasure

instance generalRGaussianObservationMeasure_isProbabilityMeasure {p : ℕ}
    (mu : CorrelationMatrix.Observation p) (R : CorrelationMatrix p) :
    IsProbabilityMeasure (generalRGaussianObservationMeasure mu R) := by
  unfold generalRGaussianObservationMeasure
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The paper's original sample law: `m + 1` iid `N_p(mu,R)` observations. -/
def originalGeneralRSampleMeasure (m : ℕ) {p : ℕ}
    (mu : CorrelationMatrix.Observation p) (R : CorrelationMatrix p) :
    Measure (GaussianData (m + 1) p) :=
  Measure.pi fun _ : Fin (m + 1) ↦ generalRGaussianObservationMeasure mu R

instance originalGeneralRSampleMeasure_isProbabilityMeasure
    (m : ℕ) {p : ℕ} (mu : CorrelationMatrix.Observation p)
    (R : CorrelationMatrix p) :
    IsProbabilityMeasure (originalGeneralRSampleMeasure m mu R) := by
  unfold originalGeneralRSampleMeasure
  infer_instance

/-- Realize the original iid sample from `m + 1` independent standard
Gaussian rows: first introduce correlation `R`, then add the common location
`mu`. -/
def originalGeneralRSampleRealization (m : ℕ) {p : ℕ}
    (mu : CorrelationMatrix.Observation p) (R : CorrelationMatrix p) :
    GaussianData (m + 1) p → GaussianData (m + 1) p :=
  addLocationData mu ∘ correlateRows R

theorem measurable_originalGeneralRSampleRealization
    (m : ℕ) {p : ℕ} (mu : CorrelationMatrix.Observation p)
    (R : CorrelationMatrix p) :
    Measurable (originalGeneralRSampleRealization m mu R) := by
  exact (measurable_addLocationData mu).comp (measurable_correlateRows R)

/-- Adding `mu` independently to the rows of the centered correlated product
measure gives the literal iid `N_p(mu,R)` sample law. -/
theorem map_addLocationData_correlatedGaussianDataMeasure
    (m : ℕ) {p : ℕ} (mu : CorrelationMatrix.Observation p)
    (R : CorrelationMatrix p) :
    Measure.map (addLocationData mu)
        (correlatedGaussianDataMeasure (m + 1) R) =
      originalGeneralRSampleMeasure m mu R := by
  let _ (k : Fin (m + 1)) : IsProbabilityMeasure
      (R.gaussianMeasure.map (fun x ↦ mu + x)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  unfold addLocationData originalGeneralRSampleMeasure
    generalRGaussianObservationMeasure correlatedGaussianDataMeasure
  rw [Measure.pi_map_pi (fun _ ↦ (by fun_prop))]

/-- Exact square-root-and-translation realization of the paper's original iid
sample law from independent standard Gaussian rows. -/
theorem map_originalGeneralRSampleRealization_standardGaussianDataMeasure
    (m : ℕ) {p : ℕ} (mu : CorrelationMatrix.Observation p)
    (R : CorrelationMatrix p) :
    Measure.map (originalGeneralRSampleRealization m mu R)
        (standardGaussianDataMeasure (m + 1) p) =
      originalGeneralRSampleMeasure m mu R := by
  unfold originalGeneralRSampleRealization
  rw [← Measure.map_map (measurable_addLocationData mu)
    (measurable_correlateRows R)]
  rw [map_correlateRows_standardGaussianDataMeasure]
  exact map_addLocationData_correlatedGaussianDataMeasure m mu R

/-! ## Exact Pearson-matrix law -/

/-- The centered scatter matrix printed in the paper,
`S = Σ_k (X_k-X̄)(X_k-X̄)ᵀ`, for `m + 1` raw observations. -/
def originalCenteredScatter {m p : ℕ} (x : GaussianData (m + 1) p) :
    Matrix (Fin p) (Fin p) ℝ :=
  scatterMatrix (centerGaussianData x)

@[simp]
theorem originalCenteredScatter_apply {m p : ℕ}
    (x : GaussianData (m + 1) p) (i j : Fin p) :
    originalCenteredScatter x i j =
      ∑ k, (x k i - sampleMean (dataColumn x i)) *
        (x k j - sampleMean (dataColumn x j)) := by
  unfold originalCenteredScatter
  rw [scatterMatrix_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rfl

/-- The paper's diagonal normalization of its centered scatter matrix. -/
def originalPearsonFromCenteredScatter {m p : ℕ}
    (x : GaussianData (m + 1) p) : Matrix (Fin p) (Fin p) ℝ :=
  correlationNormalizeMatrix (originalCenteredScatter x)

/-- The sample-correlation matrix formed exactly as in the paper: subtract the
sample mean from `m + 1` raw observations and normalize the centered variable
columns. -/
def originalGeneralRSampleCorrelation {m p : ℕ}
    (x : GaussianData (m + 1) p) : Matrix (Fin p) (Fin p) ℝ :=
  rawPearsonMatrix x

/-- The normalized-Gram implementation of Pearson correlation is exactly the
paper's centered-scatter-and-diagonal-normalization formula.  The identity is
total, including zero empirical-variance columns. -/
theorem originalGeneralRSampleCorrelation_eq_centeredScatterNormalization
    {m p : ℕ} (x : GaussianData (m + 1) p) :
    originalGeneralRSampleCorrelation x =
      originalPearsonFromCenteredScatter x := by
  unfold originalGeneralRSampleCorrelation rawPearsonMatrix
    originalPearsonFromCenteredScatter originalCenteredScatter
  ext i j
  rw [sampleCorrelationMatrix_apply]
  rw [correlationNormalizeMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hi : scatterMatrix (centerGaussianData x) i i =
      ‖dataColumn (centerGaussianData x) i‖ ^ 2 := by
    rw [scatterMatrix_eq_gram_dataColumns]
    simp [Matrix.gram_apply, dataColumns]
  have hj : scatterMatrix (centerGaussianData x) j j =
      ‖dataColumn (centerGaussianData x) j‖ ^ 2 := by
    rw [scatterMatrix_eq_gram_dataColumns]
    simp [Matrix.gram_apply, dataColumns]
  rw [hi, hj]
  simp only [Real.sqrt_sq_eq_abs, abs_norm]
  ring

theorem measurable_originalGeneralRSampleCorrelation {m p : ℕ} :
    Measurable (originalGeneralRSampleCorrelation (m := m) (p := p)) := by
  exact measurable_rawPearsonMatrix

/-- Exact equality in law between the paper's mean-centered `m + 1`-sample
Pearson matrix (with arbitrary location) and the canonical `m`-row
residual-coordinate Pearson matrix used by the general-`R` development. -/
theorem map_originalGeneralRSampleCorrelation_eq_canonical
    (m p : ℕ) (mu : CorrelationMatrix.Observation p)
    (R : CorrelationMatrix p) :
    Measure.map (originalGeneralRSampleCorrelation (m := m))
        (originalGeneralRSampleMeasure m mu R) =
      Measure.map (GeneralRDecomposition.sampleCorrelation R)
        (standardGaussianDataMeasure m p) := by
  rw [← map_originalGeneralRSampleRealization_standardGaussianDataMeasure
    m mu R]
  rw [Measure.map_map measurable_originalGeneralRSampleCorrelation
    (measurable_originalGeneralRSampleRealization m mu R)]
  calc
    Measure.map
        (originalGeneralRSampleCorrelation (m := m) ∘
          originalGeneralRSampleRealization m mu R)
        (standardGaussianDataMeasure (m + 1) p) =
      Measure.map (rawPearsonMatrix ∘ correlateRows R)
        (standardGaussianDataMeasure (m + 1) p) := by
          apply Measure.map_congr
          exact Filter.Eventually.of_forall fun z ↦ by
            change rawPearsonMatrix
                (addLocationData mu (correlateRows R z)) =
              rawPearsonMatrix (correlateRows R z)
            exact rawPearsonMatrix_addLocationData
              (Nat.zero_lt_succ m) mu (correlateRows R z)
    _ = Measure.map (sampleCorrelationMatrix ∘ correlateRows R)
        (standardGaussianDataMeasure m p) :=
      map_rawPearson_correlated_standard_succ_eq_residual m p R
    _ = Measure.map (GeneralRDecomposition.sampleCorrelation R)
        (standardGaussianDataMeasure m p) := by
          rfl

/-! ## Exact statistic law -/

/-- Apply the exact deterministic center and proxy scale from the paper's
general-`R` argument to an arbitrary candidate correlation matrix. -/
def generalRMatrixStatistic {p : ℕ} (m : ℕ) (R : CorrelationMatrix p)
    (S : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  (Real.log S.det - GeneralRDecomposition.logDetCenter m R) /
    generalRProxyScale m R

theorem measurable_generalRMatrixStatistic {p : ℕ} (m : ℕ)
    (R : CorrelationMatrix p) : Measurable (generalRMatrixStatistic m R) := by
  unfold generalRMatrixStatistic
  have hdet : Measurable
      (fun S : Matrix (Fin p) (Fin p) ℝ ↦ S.det) := by
    simp_rw [Matrix.det_apply']
    fun_prop
  exact (hdet.log.sub_const _).div_const _

/-- The paper's original statistic evaluated on `m + 1` iid observations,
including empirical mean removal inside `rawPearsonMatrix`. -/
def originalGeneralRStatistic {p : ℕ} (m : ℕ)
    (R : CorrelationMatrix p) (x : GaussianData (m + 1) p) : ℝ :=
  generalRMatrixStatistic m R (originalGeneralRSampleCorrelation x)

theorem measurable_originalGeneralRStatistic {p : ℕ} (m : ℕ)
    (R : CorrelationMatrix p) : Measurable (originalGeneralRStatistic m R) := by
  exact (measurable_generalRMatrixStatistic m R).comp
    measurable_originalGeneralRSampleCorrelation

@[simp]
theorem generalRMatrixStatistic_sampleCorrelation_eq_ZRmpStatistic
    {m p : ℕ} (R : CorrelationMatrix p) (z : GaussianData m p) :
    generalRMatrixStatistic m R
        (GeneralRDecomposition.sampleCorrelation R z) =
      ZRmpStatistic m R z := by
  rfl

/-- Exact equality in law of the paper's original, mean-centered statistic
and the canonical statistic to which the general-`R` Berry--Esseen bounds are
proved.  This theorem includes arbitrary population location `mu`; no
location-zero convention remains implicit. -/
theorem map_originalGeneralRStatistic_eq_ZRmpStatistic
    (m p : ℕ) (mu : CorrelationMatrix.Observation p)
    (R : CorrelationMatrix p) :
    Measure.map (originalGeneralRStatistic m R)
        (originalGeneralRSampleMeasure m mu R) =
      Measure.map (ZRmpStatistic m R)
        (standardGaussianDataMeasure m p) := by
  have hcanonical : Measurable
      (GeneralRDecomposition.sampleCorrelation R :
        GaussianData m p → Matrix (Fin p) (Fin p) ℝ) :=
    (measurable_normalizedGramFamily.comp measurable_dataColumns).comp
      (measurable_correlateRows R)
  calc
    Measure.map (originalGeneralRStatistic m R)
        (originalGeneralRSampleMeasure m mu R) =
      Measure.map (generalRMatrixStatistic m R)
        (Measure.map (originalGeneralRSampleCorrelation (m := m))
          (originalGeneralRSampleMeasure m mu R)) := by
            rw [Measure.map_map (measurable_generalRMatrixStatistic m R)
              measurable_originalGeneralRSampleCorrelation]
            rfl
    _ = Measure.map (generalRMatrixStatistic m R)
        (Measure.map (GeneralRDecomposition.sampleCorrelation R)
          (standardGaussianDataMeasure m p)) := by
            rw [map_originalGeneralRSampleCorrelation_eq_canonical]
    _ = Measure.map
        (generalRMatrixStatistic m R ∘
          GeneralRDecomposition.sampleCorrelation R)
        (standardGaussianDataMeasure m p) := by
            rw [Measure.map_map (measurable_generalRMatrixStatistic m R)
              hcanonical]
    _ = Measure.map (ZRmpStatistic m R)
        (standardGaussianDataMeasure m p) := by
          apply Measure.map_congr
          exact Filter.Eventually.of_forall fun z ↦ by rfl

end

end LogdetLean
