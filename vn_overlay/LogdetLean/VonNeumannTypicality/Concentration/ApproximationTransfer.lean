import LogdetLean.VonNeumannTypicality.WeakTypicality.TransferAlgebra
import Mathlib.MeasureTheory.Measure.Basic

/-!
# Uniform approximation and concentration-event transfer

This file formalizes the deterministic content of Equations (48)--(50).  The
probability model and the concentration estimate enter only through explicit
hypotheses.
-/

open MeasureTheory

namespace LogdetLean.VonNeumannTypicality

noncomputable section

/-- Equation (48) in scalar form.  A uniform pointwise error `R` and a mean
error `R` give a centered error at most `2R`. -/
theorem abs_sub_mean_le_abs_sub_approxMean_add_two_mul
    {x y mx my R : ℝ}
    (hxy : |x - y| ≤ R) (hm : |mx - my| ≤ R) :
    |x - mx| ≤ |y - my| + 2 * R := by
  calc
    |x - mx| = |(x - y) + (y - my) + (my - mx)| := by ring_nf
    _ ≤ |x - y| + |y - my| + |my - mx| := abs_add_three _ _ _
    _ ≤ R + |y - my| + R := by
      gcongr
      simpa [abs_sub_comm] using hm
    _ = |y - my| + 2 * R := by ring

/-- Event inclusion used in Equation (50). -/
theorem largeDeviation_subset_regularized_largeDeviation
    {Ω : Type*} (X Y : Ω → ℝ) {mx my R ε : ℝ}
    (hpoint : ∀ ω, |X ω - Y ω| ≤ R)
    (hmean : |mx - my| ≤ R)
    (hsmall : 2 * R ≤ ε * mx / 2) :
    {ω | ε * mx ≤ |X ω - mx|} ⊆
      {ω | ε * mx / 2 ≤ |Y ω - my|} := by
  intro ω hω
  change ε * mx ≤ |X ω - mx| at hω
  change ε * mx / 2 ≤ |Y ω - my|
  have hcenter := abs_sub_mean_le_abs_sub_approxMean_add_two_mul
    (hpoint ω) hmean
  linarith

/-- Probability form of the event transfer. -/
theorem measure_largeDeviation_le_regularized_largeDeviation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X Y : Ω → ℝ) {mx my R ε : ℝ}
    (hpoint : ∀ ω, |X ω - Y ω| ≤ R)
    (hmean : |mx - my| ≤ R)
    (hsmall : 2 * R ≤ ε * mx / 2) :
    μ {ω | ε * mx ≤ |X ω - mx|} ≤
      μ {ω | ε * mx / 2 ≤ |Y ω - my|} :=
  measure_mono <| largeDeviation_subset_regularized_largeDeviation
    X Y hpoint hmean hsmall

end

end LogdetLean.VonNeumannTypicality
