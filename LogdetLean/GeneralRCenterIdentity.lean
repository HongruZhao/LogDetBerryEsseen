import LogdetLean.WishartLogDetMoments
import LogdetLean.GeneralRRadialMoments
import LogdetLean.NullCenterStandardization
import Mathlib.Tactic

/-!
# Exact finite center for the general-correlation statistic

This module isolates the deterministic centering bridge used in Theorem 5.2
of Zhao, *Sharp Berry--Esseen Bounds for the Log Determinant of a Gaussian
Sample Correlation Matrix*.  The bridge is an equality, not an asymptotic
replacement:

`logDetCenter m R = log(det R) + nullCenterDigammaSeries m p`.

The proof identifies the identity-covariance sample-correlation determinant
with the already formalized Bartlett/Gram--Schmidt product of independent
Beta factors, transfers its first moment, and invokes the proved digamma
formula for that product.  No new probability law or moment formula is
assumed in this file.
-/

namespace LogdetLean
namespace GeneralRDecomposition

noncomputable section

open MeasureTheory ProbabilityTheory Real

private theorem map_log_det_sampleCorrelationMatrix_standard_eq_logBetaSumLaw_center
    {m p : ℕ} (hpm : p ≤ m) :
    Measure.map
        (fun z : GaussianData m p ↦
          Real.log (sampleCorrelationMatrix z).det)
        (standardGaussianDataMeasure m p) = logBetaSumLaw m p := by
  let E := ObservationSpace m
  let F : (Fin p → E) → ℝ := fun v ↦ Real.log (normalizedGram v).det
  have hF : Measurable F := by
    dsimp [F, E]
    exact (measurable_det_normalizedGram
      (E := ObservationSpace m) p).log
  calc
    Measure.map
        (fun z : GaussianData m p ↦
          Real.log (sampleCorrelationMatrix z).det)
        (standardGaussianDataMeasure m p) =
      Measure.map F
        (Measure.map dataColumns (standardGaussianDataMeasure m p)) := by
          rw [Measure.map_map hF measurable_dataColumns]
          rfl
    _ = Measure.map F
        (Measure.pi fun _ : Fin p ↦ stdGaussian E) := by
          rw [map_dataColumns_standardGaussianDataMeasure]
    _ = Measure.map F
        (Measure.map (nestedTupleToFin (α := E) p)
          (nestedProductMeasure (stdGaussian E) p)) := by
          rw [map_nestedTupleToFin_nestedProductMeasure]
    _ = Measure.map (F ∘ nestedTupleToFin (α := E) p)
        (nestedProductMeasure (stdGaussian E) p) :=
          Measure.map_map hF (measurable_nestedTupleToFin p)
    _ = Measure.map (Real.log ∘ nestedNormalizedGramDet (E := E) p)
        (nestedProductMeasure (stdGaussian E) p) := by rfl
    _ = Measure.map Real.log
        (Measure.map (nestedNormalizedGramDet (E := E) p)
          (nestedProductMeasure (stdGaussian E) p)) :=
          (Measure.map_map measurable_log
            ((measurable_det_normalizedGram (E := E) p).comp
              (measurable_nestedTupleToFin p))).symm
    _ = Measure.map Real.log
        (Measure.map (nestedRealProduct p)
          (nestedProductMeasureFamily
            (gaussianGramSchmidtFactorMeasure m) p)) := by
          rw [map_gaussianNormalizedGramDet_eq_map_product_betaFactors
            m p (by simp [E]) hpm]
    _ = Measure.map (Real.log ∘ nestedRealProduct p)
        (nestedProductMeasureFamily
          (gaussianGramSchmidtFactorMeasure m) p) :=
          Measure.map_map measurable_log (measurable_nestedRealProduct p)
    _ = logBetaSumLaw m p :=
          map_log_nestedRealProduct_gaussianFactors_eq_logBetaSumLaw hpm

private theorem correlateRows_identity_center {m p : ℕ}
    (z : GaussianData m p) :
    correlateRows (CorrelationMatrix.identity p) z = z := by
  ext k i
  simp [correlateRows, CorrelationMatrix.correlateObservation,
    CorrelationMatrix.covarianceSqrt]

/-- The identity-scatter contribution to the general-`R` center is exactly
the finite digamma center of the null log-Beta sum. -/
theorem W0LogDetMean_sub_mul_chiSquareLogMean_eq_nullCenterDigammaSeries
    {m p : ℕ} (h : Admissible m p) :
    W0LogDetMean m p - (p : ℝ) * chiSquareLogMean m =
      nullCenterDigammaSeries m p := by
  have hp2 : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hm : 0 < m := by omega
  have hW : Integrable (fun z : GaussianData m p ↦
      Real.log (W0 z).det) (standardGaussianDataMeasure m p) :=
    (memLp_log_det_W0_two hm h.2).integrable (by norm_num)
  have hQ : ∀ i : Fin p, Integrable (fun z : GaussianData m p ↦
      Real.log (Q (CorrelationMatrix.identity p) z i))
      (standardGaussianDataMeasure m p) := fun i ↦
    integrable_log_Q hm (CorrelationMatrix.identity p) i
  have hcenterIdentity :=
    (integrable_log_det_sampleCorrelation_and_integral_eq_center
      hm h.2 (CorrelationMatrix.identity p) hW hQ).2
  have hsampleIdentity :
      sampleCorrelation (CorrelationMatrix.identity p) =
        (sampleCorrelationMatrix : GaussianData m p →
          Matrix (Fin p) (Fin p) ℝ) := by
    funext z
    unfold sampleCorrelation
    rw [correlateRows_identity_center]
  rw [hsampleIdentity] at hcenterIdentity
  have hlaw :=
    map_log_det_sampleCorrelationMatrix_standard_eq_logBetaSumLaw_center h.2
  have hint :
      (∫ z : GaussianData m p,
        Real.log (sampleCorrelationMatrix z).det
          ∂standardGaussianDataMeasure m p) =
        ∫ x : ℝ, x ∂logBetaSumLaw m p := by
    have hmeas : Measurable (fun z : GaussianData m p ↦
        Real.log (sampleCorrelationMatrix z).det) :=
      measurable_det_sampleCorrelationMatrix.log
    rw [← hlaw]
    rw [integral_map hmeas.aemeasurable (by fun_prop)]
  have hnull : (∫ x : ℝ, x ∂logBetaSumLaw m p) =
      nullCenterDigammaSeries m p := by
    rw [← nullCenter_eq_nullCenterDigammaSeries h.2]
    rfl
  rw [← hnull, ← hint, hcenterIdentity]
  simp [logDetCenter]

/-- Paper-facing exact centering identity for Theorem 5.2. -/
theorem logDetCenter_eq_logDet_add_nullCenterDigammaSeries
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    logDetCenter m R =
      Real.log R.val.det + nullCenterDigammaSeries m p := by
  unfold logDetCenter
  rw [add_sub_assoc,
    W0LogDetMean_sub_mul_chiSquareLogMean_eq_nullCenterDigammaSeries h]

end
end GeneralRDecomposition
end LogdetLean

namespace LogdetLean.GeneralRDecomposition
noncomputable section
open MeasureTheory ProbabilityTheory

/-- Public actual-law bridge for the identity population. -/
theorem map_log_sampleCorrelation_identity_eq_logBetaSumLaw {m p : ℕ} (hp : p ≤ m) :
    (standardGaussianDataMeasure m p).map
      (fun z ↦ Real.log (sampleCorrelation (CorrelationMatrix.identity p) z).det) = logBetaSumLaw m p := by
  simp only [sampleCorrelation, correlateRows_identity_center]
  exact map_log_det_sampleCorrelationMatrix_standard_eq_logBetaSumLaw_center hp

end
end LogdetLean.GeneralRDecomposition
