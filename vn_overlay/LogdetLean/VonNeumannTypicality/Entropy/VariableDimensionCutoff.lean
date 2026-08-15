import LogdetLean.VonNeumannTypicality.Entropy.CutoffRate

/-!
# Removing the entropy cutoff for varying subsystem dimensions

The paper uses a subsystem size `k N`, not a fixed copy of `N`.  This file
removes the cutoff for spectra indexed by `Fin (k N)` under the natural bound
`k N ≤ N`.  It closes the dimensional mismatch in the earlier generic
`Fin N` transfer theorem.
-/

open Filter

namespace LogdetLean.VonNeumannTypicality

noncomputable section

/-- Uniform cutoff removal for a triangular family of spectra with varying
length `k N ≤ N`. -/
theorem tendsto_abs_entropySpectralStatistic_sub_regularized_inverseSquareCutoff_variableDimension
    (s : ℝ) (k : ℕ → ℕ) (tau : (N : ℕ) → Fin (k N) → ℝ)
    (hk : ∀ N, k N ≤ N)
    (htau0 : ∀ N i, 0 ≤ tau N i) (htau1 : ∀ N i, tau N i ≤ 1) :
    Tendsto
      (fun N : ℕ ↦
        |entropySpectralStatistic s (tau N) -
          regularizedEntropySpectralStatistic s (inverseSquareCutoff N) (tau N)|)
      atTop (nhds 0) := by
  have hupper := tendsto_nat_mul_entropyProfile_inverseSquareCutoff s
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) ?_ hupper
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hprofile : 0 ≤ entropyProfile s (1 - inverseSquareCutoff N) :=
    entropyProfile_nonneg
      (by
        have := inverseSquareCutoff_le_one hN
        linarith)
      (by linarith [inverseSquareCutoff_nonneg N])
  have hkreal : (k N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk N
  calc
    |entropySpectralStatistic s (tau N) -
        regularizedEntropySpectralStatistic s (inverseSquareCutoff N) (tau N)|
        ≤ (k N : ℝ) * entropyProfile s (1 - inverseSquareCutoff N) :=
      abs_entropySpectralStatistic_sub_regularized_le
        (by
          unfold inverseSquareCutoff
          exact inv_pos.mpr (sq_pos_of_pos (by exact_mod_cast hN)))
        (inverseSquareCutoff_le_one hN) (htau0 N) (htau1 N)
    _ ≤ (N : ℝ) * entropyProfile s (1 - inverseSquareCutoff N) :=
      mul_le_mul_of_nonneg_right hkreal hprofile

/-- Signed form of variable-dimensional cutoff removal. -/
theorem tendsto_entropySpectralStatistic_sub_regularized_inverseSquareCutoff_variableDimension
    (s : ℝ) (k : ℕ → ℕ) (tau : (N : ℕ) → Fin (k N) → ℝ)
    (hk : ∀ N, k N ≤ N)
    (htau0 : ∀ N i, 0 ≤ tau N i) (htau1 : ∀ N i, tau N i ≤ 1) :
    Tendsto
      (fun N : ℕ ↦
        entropySpectralStatistic s (tau N) -
          regularizedEntropySpectralStatistic s (inverseSquareCutoff N) (tau N))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  simpa [Function.comp_def] using
    tendsto_abs_entropySpectralStatistic_sub_regularized_inverseSquareCutoff_variableDimension
      s k tau hk htau0 htau1

/-- The variable-dimensional cutoff error is negligible relative to every
positive normalizer diverging to infinity. -/
theorem tendsto_entropySpectralStatistic_cutoff_error_div_normalizer_variableDimension
    (s : ℝ) (k : ℕ → ℕ) (tau : (N : ℕ) → Fin (k N) → ℝ)
    (normalizer : ℕ → ℝ)
    (hk : ∀ N, k N ≤ N)
    (htau0 : ∀ N i, 0 ≤ tau N i) (htau1 : ∀ N i, tau N i ≤ 1)
    (hnorm : Tendsto normalizer atTop atTop) :
    Tendsto
      (fun N : ℕ ↦
        (entropySpectralStatistic s (tau N) -
          regularizedEntropySpectralStatistic s (inverseSquareCutoff N) (tau N)) /
          normalizer N)
      atTop (nhds 0) :=
  (tendsto_entropySpectralStatistic_sub_regularized_inverseSquareCutoff_variableDimension
    s k tau hk htau0 htau1).div_atTop hnorm

end

end LogdetLean.VonNeumannTypicality
