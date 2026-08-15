import LogdetLean.VonNeumannTypicality.WeakTypicality.CutoffProbabilityTransfer
import LogdetLean.VonNeumannTypicality.Entropy.VariableDimensionCutoff

/-!
# Weak typicality for varying subsystem dimensions

This is the paper-facing cutoff-removal theorem.  The subsystem spectrum at
ambient dimension `N` is indexed by `Fin (k N)` and only the physical bound
`k N ≤ N` is required.
-/

open Filter MeasureTheory

namespace LogdetLean.VonNeumannTypicality

noncomputable section

/-- Weak typicality of the inverse-square regularized statistic implies weak
typicality of the unregularized entropy for a varying subsystem dimension
`k N ≤ N`. -/
theorem weaklyTypical_entropySpectralStatistic_of_regularized_variableDimension
    {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (μ : (N : ℕ) → Measure (Ω N))
    [∀ N, IsProbabilityMeasure (μ N)]
    (s : ℝ) (k : ℕ → ℕ)
    (tau : (N : ℕ) → Ω N → Fin (k N) → ℝ) (m : ℕ → ℝ)
    (hk : ∀ N, k N ≤ N)
    (htau0 : ∀ N ω i, 0 ≤ tau N ω i)
    (htau1 : ∀ N ω i, tau N ω i ≤ 1)
    (hm : Tendsto m atTop atTop)
    (hregularized : WeaklyTypical μ
      (fun N ω ↦ regularizedEntropySpectralStatistic s
        (inverseSquareCutoff N) (tau N ω)) m) :
    WeaklyTypical μ
      (fun N ω ↦ entropySpectralStatistic s (tau N ω)) m := by
  let δ : ℕ → ℝ := fun N ↦ inverseSquareCutoffTotalError s N / m N
  have hmpos : ∀ᶠ N in atTop, 0 < m N :=
    hm.eventually (eventually_gt_atTop (0 : ℝ))
  have hδ : Tendsto δ atTop (nhds 0) :=
    (tendsto_inverseSquareCutoffTotalError s).div_atTop hm
  have happrox : ∀ᶠ N in atTop, ∀ ω,
      |entropySpectralStatistic s (tau N ω) -
          regularizedEntropySpectralStatistic s (inverseSquareCutoff N)
            (tau N ω)| ≤ δ N * m N := by
    filter_upwards [eventually_ge_atTop 1, hmpos] with N hN hmN
    intro ω
    have hprofile : 0 ≤ entropyProfile s (1 - inverseSquareCutoff N) :=
      entropyProfile_nonneg
        (by
          have := inverseSquareCutoff_le_one hN
          linarith)
        (by linarith [inverseSquareCutoff_nonneg N])
    have hkreal : (k N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk N
    have hbound := abs_entropySpectralStatistic_sub_regularized_le
      (s := s) (η := inverseSquareCutoff N) (τ := tau N ω)
      (by
        unfold inverseSquareCutoff
        exact inv_pos.mpr (sq_pos_of_pos (by exact_mod_cast hN)))
      (inverseSquareCutoff_le_one hN)
      (htau0 N ω) (htau1 N ω)
    calc
      |entropySpectralStatistic s (tau N ω) -
          regularizedEntropySpectralStatistic s (inverseSquareCutoff N)
            (tau N ω)|
          ≤ (k N : ℝ) * entropyProfile s (1 - inverseSquareCutoff N) := hbound
      _ ≤ inverseSquareCutoffTotalError s N := by
        exact mul_le_mul_of_nonneg_right hkreal hprofile
      _ = δ N * m N := by
        dsimp [δ]
        field_simp
  exact weaklyTypical_of_uniform_approximation μ _ _ m δ
    hmpos hδ happrox hregularized

end

end LogdetLean.VonNeumannTypicality
