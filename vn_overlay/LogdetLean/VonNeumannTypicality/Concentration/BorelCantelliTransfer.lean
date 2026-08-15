import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Topology.Instances.Real

/-!
# First Borel--Cantelli transfer for the manuscript

The first Borel--Cantelli lemma requires summability only; no independence
assumption is used.  These statements formalize the almost-sure consequence
of the manuscript's summable concentration tails.
-/

open Filter MeasureTheory
open scoped ENNReal

namespace LogdetLean.VonNeumannTypicality

noncomputable section

/-- If the upper-deviation events have summable probabilities, then almost
every sample eventually avoids them. -/
theorem ae_eventually_abs_sub_lt_of_tsum_measure_ne_top
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (center : ℕ → ℝ) (ε : ℝ)
    (hsum : (∑' N, μ {ω | ε ≤ |X N ω - center N|}) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ᶠ N in atTop, |X N ω - center N| < ε := by
  have hAE := MeasureTheory.ae_eventually_notMem
    (μ := μ) (s := fun N ↦ {ω | ε ≤ |X N ω - center N|}) hsum
  filter_upwards [hAE] with ω hω
  filter_upwards [hω] with N hN
  change ¬ ε ≤ |X N ω - center N| at hN
  exact lt_of_not_ge hN

/-- Relative-error form used for weak typicality and its almost-sure
strengthening. -/
theorem ae_eventually_relative_error_lt_of_tsum_measure_ne_top
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (normalizer : ℕ → ℝ) (ε : ℝ)
    (hsum : (∑' N,
      μ {ω | ε ≤ |X N ω / normalizer N - 1|}) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ᶠ N in atTop,
      |X N ω / normalizer N - 1| < ε :=
  ae_eventually_abs_sub_lt_of_tsum_measure_ne_top μ
    (fun N ω ↦ X N ω / normalizer N) (fun _ ↦ 1) ε hsum

/-- Subpolynomial-deviation form.  For any fixed exponent and threshold,
summability of the corresponding tails yields an almost-sure eventual bound.
This is the precise fixed-parameter Borel--Cantelli content of Equation (52). -/
theorem ae_eventually_abs_centered_lt_mul_rpow_of_tsum_measure_ne_top
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (center : ℕ → ℝ) (a ε : ℝ)
    (hsum : (∑' N,
      μ {ω | ε * (N : ℝ) ^ a ≤ |X N ω - center N|}) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ᶠ N in atTop,
      |X N ω - center N| < ε * (N : ℝ) ^ a :=
  ae_eventually_abs_sub_lt_of_tsum_measure_ne_top μ X center ε
    (by simpa only using hsum)

end

end LogdetLean.VonNeumannTypicality
