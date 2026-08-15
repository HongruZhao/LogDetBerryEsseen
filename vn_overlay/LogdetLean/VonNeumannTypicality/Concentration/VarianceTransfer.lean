import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-!
# Variance transfer under uniform approximation

This file formalizes the variance comparison used in Corollary 4.  It is
independent of the Gaussian-state model and applies to any two square-
integrable real random variables on a probability space.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace LogdetLean.VonNeumannTypicality

noncomputable section

/-- If `X` and `Y` differ by at most `R` almost surely, then
`Var(X) ≤ 2 Var(Y) + 2 R²`.  This is the variance-transfer estimate used to
pass from the regularized statistic to the physical entropy. -/
theorem variance_le_two_variance_add_two_sq_of_uniform_approximation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (R : ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hR : 0 ≤ R)
    (hXY : ∀ᵐ ω ∂μ, |X ω - Y ω| ≤ R) :
    Var[X; μ] ≤ 2 * Var[Y; μ] + 2 * R ^ 2 := by
  have hD : MemLp (fun ω ↦ X ω - Y ω) 2 μ := by
    change MemLp (X - Y) 2 μ
    exact hX.sub hY
  have hC : MemLp (fun ω ↦ Y ω - μ[Y]) 2 μ :=
    hY.sub (memLp_const μ[Y])
  have hZ : MemLp (fun ω ↦ X ω - μ[Y]) 2 μ :=
    hX.sub (memLp_const μ[Y])
  have hpoint : ∀ᵐ ω ∂μ,
      (X ω - μ[Y]) ^ 2 ≤
        2 * (X ω - Y ω) ^ 2 + 2 * (Y ω - μ[Y]) ^ 2 := by
    filter_upwards with ω
    nlinarith [sq_nonneg ((X ω - Y ω) - (Y ω - μ[Y]))]
  have hdiffsq : ∀ᵐ ω ∂μ, (X ω - Y ω) ^ 2 ≤ R ^ 2 := by
    filter_upwards [hXY] with ω hω
    have hminus : 0 ≤ R - |X ω - Y ω| := sub_nonneg.mpr hω
    have hplus : 0 ≤ R + |X ω - Y ω| := add_nonneg hR (abs_nonneg _)
    have hprod := mul_nonneg hminus hplus
    nlinarith [sq_abs (X ω - Y ω)]
  have hdiffIntegral :
      (∫ ω, (X ω - Y ω) ^ 2 ∂μ) ≤ R ^ 2 := by
    calc
      (∫ ω, (X ω - Y ω) ^ 2 ∂μ)
          ≤ ∫ _ω, R ^ 2 ∂μ :=
        integral_mono_ae hD.integrable_sq (integrable_const (R ^ 2)) hdiffsq
      _ = R ^ 2 := by simp
  have hIntAdd :
      (∫ ω,
          (2 * (X ω - Y ω) ^ 2 + 2 * (Y ω - μ[Y]) ^ 2) ∂μ) =
        (∫ ω, 2 * (X ω - Y ω) ^ 2 ∂μ) +
          ∫ ω, 2 * (Y ω - μ[Y]) ^ 2 ∂μ :=
    integral_add (hD.integrable_sq.const_mul 2) (hC.integrable_sq.const_mul 2)
  calc
    Var[X; μ] = Var[fun ω ↦ X ω - μ[Y]; μ] := by
      symm
      exact variance_sub_const hX.aestronglyMeasurable μ[Y]
    _ ≤ ∫ ω, (X ω - μ[Y]) ^ 2 ∂μ :=
      variance_le_expectation_sq hZ.aestronglyMeasurable
    _ ≤ ∫ ω,
        (2 * (X ω - Y ω) ^ 2 + 2 * (Y ω - μ[Y]) ^ 2) ∂μ := by
      exact integral_mono_ae hZ.integrable_sq
        ((hD.integrable_sq.const_mul 2).add (hC.integrable_sq.const_mul 2)) hpoint
    _ = 2 * (∫ ω, (X ω - Y ω) ^ 2 ∂μ) +
        2 * (∫ ω, (Y ω - μ[Y]) ^ 2 ∂μ) := by
      rw [hIntAdd, integral_const_mul, integral_const_mul]
    _ ≤ 2 * R ^ 2 + 2 * Var[Y; μ] := by
      rw [variance_eq_integral hY.aemeasurable]
      gcongr
    _ = 2 * Var[Y; μ] + 2 * R ^ 2 := by ring

end

end LogdetLean.VonNeumannTypicality
