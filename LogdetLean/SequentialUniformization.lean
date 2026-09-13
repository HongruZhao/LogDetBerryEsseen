import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic

/-!
# From sequential control to a supremum over an expanding parameter set

This module records a small diagonal-selection principle used by the sharp
sample-correlation theorem.  Suppose `f p m` is nonnegative and uniformly
bounded for `p ≤ m`.  If `f p (m p) → 0` for every eventually admissible
choice `m=m(p)`, then the supremum over all `m ≥ p` also tends to zero.

The proof is elementary.  If the supremum failed to be eventually small,
then at every bad index we could choose a value within a factor two of it.
Those choices form one admissible sequence, contradicting the assumed
sequential convergence.  The result is proved here from the defining
properties of `sSup`; it is not imported from an external source.
-/

namespace LogdetLean

open Filter Set

noncomputable section

/-- Values of `f p m` obtained from parameters in the tail `m ≥ p`. -/
def admissibleTailValues (f : ℕ → ℕ → ℝ) (p : ℕ) : Set ℝ :=
  {x | ∃ m, p ≤ m ∧ x = f p m}

/-- Supremum of `f p m` over the expanding tail `m ≥ p`. -/
def admissibleTailSup (f : ℕ → ℕ → ℝ) (p : ℕ) : ℝ :=
  sSup (admissibleTailValues f p)

theorem admissibleTailValues_nonempty (f : ℕ → ℕ → ℝ) (p : ℕ) :
    (admissibleTailValues f p).Nonempty := by
  exact ⟨f p p, p, le_rfl, rfl⟩

theorem admissibleTailValues_bddAbove
    {f : ℕ → ℕ → ℝ} {C : ℝ}
    (hupper : ∀ p m, p ≤ m → f p m ≤ C) (p : ℕ) :
    BddAbove (admissibleTailValues f p) := by
  refine ⟨C, ?_⟩
  rintro x ⟨m, hpm, rfl⟩
  exact hupper p m hpm

theorem admissibleTailSup_nonneg
    {f : ℕ → ℕ → ℝ} {C : ℝ}
    (hnonneg : ∀ p m, p ≤ m → 0 ≤ f p m)
    (hupper : ∀ p m, p ≤ m → f p m ≤ C) (p : ℕ) :
    0 ≤ admissibleTailSup f p := by
  unfold admissibleTailSup
  exact le_csSup_of_le (admissibleTailValues_bddAbove hupper p)
    ⟨p, le_rfl, rfl⟩ (hnonneg p p le_rfl)

/-- Sequential convergence for every eventually admissible parameter choice
implies convergence of the supremum over all `m ≥ p`.

The common upper bound is needed only to make the real `sSup` well behaved.
In the Kolmogorov application one may take `C=1`. -/
theorem tendsto_admissibleTailSup_zero_of_all_sequences
    {f : ℕ → ℕ → ℝ} {C : ℝ}
    (hnonneg : ∀ p m, p ≤ m → 0 ≤ f p m)
    (hupper : ∀ p m, p ≤ m → f p m ≤ C)
    (hseq : ∀ m : ℕ → ℕ,
      (∀ᶠ p in atTop, p ≤ m p) →
        Tendsto (fun p ↦ f p (m p)) atTop (nhds 0)) :
    Tendsto (admissibleTailSup f) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hevent : ∀ᶠ p in atTop, admissibleTailSup f p < ε := by
    by_contra hnot
    have hfreq : ∃ᶠ p in atTop, ¬ admissibleTailSup f p < ε :=
      (not_eventually.mp hnot)
    have hexists (p : ℕ) (hp : ε / 2 < admissibleTailSup f p) :
        ∃ m, p ≤ m ∧ ε / 2 < f p m := by
      have hne := admissibleTailValues_nonempty f p
      obtain ⟨x, hx, hlt⟩ := exists_lt_of_lt_csSup hne hp
      rcases hx with ⟨m, hpm, rfl⟩
      exact ⟨m, hpm, hlt⟩
    let m : ℕ → ℕ := fun p ↦
      if hp : ε / 2 < admissibleTailSup f p then
        Classical.choose (hexists p hp)
      else p
    have hm_adm : ∀ p, p ≤ m p := by
      intro p
      dsimp [m]
      split_ifs with hp
      · exact (Classical.choose_spec (hexists p hp)).1
      · exact le_rfl
    have hm_limit := hseq m (Filter.Eventually.of_forall hm_adm)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hm_limit (ε / 2) (by positivity)
    have hfreqN : ∃ᶠ p in atTop, ¬ admissibleTailSup f p < ε ∧ N ≤ p :=
      hfreq.and_eventually (eventually_ge_atTop N)
    obtain ⟨p, hpbad, hpN⟩ := hfreqN.exists
    have hhalfsup : ε / 2 < admissibleTailSup f p := by
      have hsup : ε ≤ admissibleTailSup f p := le_of_not_gt hpbad
      linarith
    have hm_large : ε / 2 < f p (m p) := by
      dsimp [m]
      rw [dif_pos hhalfsup]
      exact (Classical.choose_spec (hexists p hhalfsup)).2
    have hsmall := hN p hpN
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnonneg p (m p) (hm_adm p))] at hsmall
    linarith
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hevent)
  refine ⟨N, fun p hp ↦ ?_⟩
  rw [dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg (admissibleTailSup_nonneg hnonneg hupper p)]
  exact hN p hp

end

end LogdetLean
