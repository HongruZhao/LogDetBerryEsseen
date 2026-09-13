import LogdetLean.NullRegimeAsymptotics
import Mathlib.Tactic

/-!
# Finite endpoint bounds for the dilute null regime

This module isolates the elementary Taylor-free inequalities needed when
`p/m -> 0`.  They are kept separate from `NullRegimeAsymptotics.lean` so
downstream users of the fixed-gap API do not depend on the dilute proof.
-/

namespace LogdetLean

open Filter Real Set
open scoped BigOperators Topology

noncomputable section

/-- Reverse the gap-indexed elementary sum so that the summation variable is
the distance `q=r+1` from the common upper shape `m`. -/
theorem nullGapPowerDifference_eq_reverse_range (s m p : ℕ)
    (h : Admissible m p) :
    nullGapPowerDifference s m p =
      ∑ r ∈ Finset.range (p - 1),
        (1 / (((m - r - 1 : ℕ) : ℝ) ^ s) - 1 / (m : ℝ) ^ s) := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  unfold nullGapPowerDifference
  apply Finset.sum_bij (fun k _hk ↦ m - k - 1)
  · intro k hk
    have hkb := Finset.mem_Ico.mp hk
    exact Finset.mem_range.mpr (by omega)
  · intro k₁ hk₁ k₂ hk₂ heq
    have h₁ := (Finset.mem_Ico.mp hk₁).2
    have h₂ := (Finset.mem_Ico.mp hk₂).2
    omega
  · intro r hr
    have hrb := Finset.mem_range.mp hr
    refine ⟨m - r - 1, ?_, ?_⟩
    · exact Finset.mem_Ico.mpr (by omega)
    · omega
  · intro k hk
    have hklt := (Finset.mem_Ico.mp hk).2
    congr 3
    have heq : m - (m - k - 1) - 1 = k := by omega
    exact_mod_cast heq.symm

private theorem twice_sum_range_succ_cast (n : ℕ) :
    2 * (∑ r ∈ Finset.range n, (((r + 1 : ℕ) : ℝ))) =
      (n : ℝ) * ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      push_cast at ih ⊢
      nlinarith

private theorem inv_difference_one_bounds {m p r : ℕ}
    (h : Admissible m p) (hr : r ∈ Finset.range (p - 1)) :
    ((r + 1 : ℕ) : ℝ) / (m : ℝ) ^ 2 ≤
        1 / (((m - r - 1 : ℕ) : ℝ)) - 1 / (m : ℝ) ∧
      1 / (((m - r - 1 : ℕ) : ℝ)) - 1 / (m : ℝ) ≤
        ((r + 1 : ℕ) : ℝ) /
          ((m : ℝ) * (((m - p + 1 : ℕ) : ℝ))) := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hrr : r < p - 1 := Finset.mem_range.mp hr
  have hrm : r + 1 < m := by omega
  have hres : 0 < m - r - 1 := by omega
  have hmNat : 0 < m := by omega
  have hm : 0 < (m : ℝ) := Nat.cast_pos.mpr hmNat
  have hresR : 0 < (((m - r - 1 : ℕ) : ℝ)) := Nat.cast_pos.mpr hres
  have hdpos : 0 < m - p + 1 := by omega
  have hdR : 0 < (((m - p + 1 : ℕ) : ℝ)) := Nat.cast_pos.mpr hdpos
  have hcast : (((m - r - 1 : ℕ) : ℝ)) = (m : ℝ) - (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m - r), Nat.cast_sub (by omega : r ≤ m)]
    norm_num
  have hqcast : (((r + 1 : ℕ) : ℝ)) = (r : ℝ) + 1 := by norm_num
  have hid :
      1 / (((m - r - 1 : ℕ) : ℝ)) - 1 / (m : ℝ) =
        ((r + 1 : ℕ) : ℝ) /
          ((m : ℝ) * (((m - r - 1 : ℕ) : ℝ))) := by
    rw [hcast, hqcast]
    field_simp [hm.ne', (show (m : ℝ) - (r : ℝ) - 1 ≠ 0 by
      simpa [hcast] using hresR.ne')]
    ring
  rw [hid]
  constructor
  · apply (div_le_div_iff₀ (sq_pos_of_pos hm) (mul_pos hm hresR)).2
    have hle : (((m - r - 1 : ℕ) : ℝ)) ≤ (m : ℝ) := by
      exact_mod_cast (Nat.sub_le m (r + 1))
    have hq : 0 ≤ (((r + 1 : ℕ) : ℝ)) := by positivity
    have hden : (m : ℝ) * (((m - r - 1 : ℕ) : ℝ)) ≤ (m : ℝ) ^ 2 := by
      nlinarith
    exact mul_le_mul_of_nonneg_left hden hq
  · apply (div_le_div_iff₀ (mul_pos hm hresR) (mul_pos hm hdR)).2
    have hdle : m - p + 1 ≤ m - r - 1 := by omega
    have hdleR : (((m - p + 1 : ℕ) : ℝ)) ≤
        (((m - r - 1 : ℕ) : ℝ)) := by exact_mod_cast hdle
    have hq : 0 ≤ (((r + 1 : ℕ) : ℝ)) := by positivity
    have hden : (m : ℝ) * (((m - p + 1 : ℕ) : ℝ)) ≤
        (m : ℝ) * (((m - r - 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hdleR hm.le
    exact mul_le_mul_of_nonneg_left hden hq

/-- Finite two-sided bounds for `nullVLeading` in the dilute scaling. -/
theorem nullVLeading_dilute_bounds {m p : ℕ} (h : Admissible m p) :
    (p : ℝ) * ((p : ℝ) - 1) / (m : ℝ) ^ 2 ≤ nullVLeading m p ∧
      nullVLeading m p ≤
        (p : ℝ) * ((p : ℝ) - 1) /
          ((m : ℝ) * (((m - p + 1 : ℕ) : ℝ))) := by
  have hp : 2 ≤ p := h.1
  rw [nullVLeading, nullGapPowerDifference_eq_reverse_range 1 m p h]
  simp only [pow_one]
  constructor
  · calc
      (p : ℝ) * ((p : ℝ) - 1) / (m : ℝ) ^ 2 =
          2 * ∑ r ∈ Finset.range (p - 1),
            (((r + 1 : ℕ) : ℝ) / (m : ℝ) ^ 2) := by
        rw [← Finset.sum_div, ← mul_div_assoc]
        have hs := twice_sum_range_succ_cast (p - 1)
        rw [Nat.cast_sub (by omega : 1 ≤ p)] at hs
        rw [hs]
        ring
      _ ≤ 2 * ∑ r ∈ Finset.range (p - 1),
          (1 / (((m - r - 1 : ℕ) : ℝ)) - 1 / (m : ℝ)) := by
        gcongr with r hr
        exact (inv_difference_one_bounds h hr).1
  · calc
      2 * ∑ r ∈ Finset.range (p - 1),
          (1 / (((m - r - 1 : ℕ) : ℝ)) - 1 / (m : ℝ)) ≤
          2 * ∑ r ∈ Finset.range (p - 1),
            (((r + 1 : ℕ) : ℝ) /
              ((m : ℝ) * (((m - p + 1 : ℕ) : ℝ)))) := by
        gcongr with r hr
        exact (inv_difference_one_bounds h hr).2
      _ = (p : ℝ) * ((p : ℝ) - 1) /
          ((m : ℝ) * (((m - p + 1 : ℕ) : ℝ))) := by
        rw [← Finset.sum_div, ← mul_div_assoc]
        have hs := twice_sum_range_succ_cast (p - 1)
        rw [Nat.cast_sub (by omega : 1 ≤ p)] at hs
        rw [hs]
        ring

private theorem inv_difference_two_bounds {m p r : ℕ}
    (h : Admissible m p) (hr : r ∈ Finset.range (p - 1)) :
    2 * ((r + 1 : ℕ) : ℝ) / (m : ℝ) ^ 3 ≤
        1 / (((m - r - 1 : ℕ) : ℝ) ^ 2) - 1 / (m : ℝ) ^ 2 ∧
      1 / (((m - r - 1 : ℕ) : ℝ) ^ 2) - 1 / (m : ℝ) ^ 2 ≤
        2 * ((r + 1 : ℕ) : ℝ) /
          ((m : ℝ) * (((m - p + 1 : ℕ) : ℝ)) ^ 2) := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hrr : r < p - 1 := Finset.mem_range.mp hr
  have hrm : r + 1 < m := by omega
  have hres : 0 < m - r - 1 := by omega
  have hmNat : 0 < m := by omega
  have hm : 0 < (m : ℝ) := Nat.cast_pos.mpr hmNat
  have hresR : 0 < (((m - r - 1 : ℕ) : ℝ)) := Nat.cast_pos.mpr hres
  have hdpos : 0 < m - p + 1 := by omega
  have hdR : 0 < (((m - p + 1 : ℕ) : ℝ)) := Nat.cast_pos.mpr hdpos
  have hres_le_m : (((m - r - 1 : ℕ) : ℝ)) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.sub_le m (r + 1))
  have hd_le_res : (((m - p + 1 : ℕ) : ℝ)) ≤
      (((m - r - 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show m - p + 1 ≤ m - r - 1 by omega)
  have hd_le_m : (((m - p + 1 : ℕ) : ℝ)) ≤ (m : ℝ) :=
    hd_le_res.trans hres_le_m
  have hdiff := inv_difference_one_bounds h hr
  have hdiff_nonneg : 0 ≤
      1 / (((m - r - 1 : ℕ) : ℝ)) - 1 / (m : ℝ) := by
    exact hdiff.1.trans' (by positivity)
  have hfactor_lower :
      2 / (m : ℝ) ≤
        1 / (((m - r - 1 : ℕ) : ℝ)) + 1 / (m : ℝ) := by
    have hinv : 1 / (m : ℝ) ≤ 1 / (((m - r - 1 : ℕ) : ℝ)) :=
      one_div_le_one_div_of_le hresR hres_le_m
    calc
      2 / (m : ℝ) = 1 / (m : ℝ) + 1 / (m : ℝ) := by ring
      _ ≤ 1 / (((m - r - 1 : ℕ) : ℝ)) + 1 / (m : ℝ) :=
        add_le_add hinv le_rfl
  have hfactor_upper :
      1 / (((m - r - 1 : ℕ) : ℝ)) + 1 / (m : ℝ) ≤
        2 / (((m - p + 1 : ℕ) : ℝ)) := by
    have h₁ : 1 / (((m - r - 1 : ℕ) : ℝ)) ≤
        1 / (((m - p + 1 : ℕ) : ℝ)) :=
      one_div_le_one_div_of_le hdR hd_le_res
    have h₂ : 1 / (m : ℝ) ≤
        1 / (((m - p + 1 : ℕ) : ℝ)) :=
      one_div_le_one_div_of_le hdR hd_le_m
    calc
      1 / (((m - r - 1 : ℕ) : ℝ)) + 1 / (m : ℝ) ≤
          1 / (((m - p + 1 : ℕ) : ℝ)) +
            1 / (((m - p + 1 : ℕ) : ℝ)) := add_le_add h₁ h₂
      _ = 2 / (((m - p + 1 : ℕ) : ℝ)) := by ring
  have hid :
      1 / (((m - r - 1 : ℕ) : ℝ) ^ 2) - 1 / (m : ℝ) ^ 2 =
        (1 / (((m - r - 1 : ℕ) : ℝ)) - 1 / (m : ℝ)) *
          (1 / (((m - r - 1 : ℕ) : ℝ)) + 1 / (m : ℝ)) := by ring
  rw [hid]
  constructor
  · have hmul := mul_le_mul hdiff.1 hfactor_lower
        (by positivity : 0 ≤ 2 / (m : ℝ)) hdiff_nonneg
    calc
      2 * ((r + 1 : ℕ) : ℝ) / (m : ℝ) ^ 3 =
          (((r + 1 : ℕ) : ℝ) / (m : ℝ) ^ 2) * (2 / (m : ℝ)) := by ring
      _ ≤ (1 / (((m - r - 1 : ℕ) : ℝ)) - 1 / (m : ℝ)) *
          (1 / (((m - r - 1 : ℕ) : ℝ)) + 1 / (m : ℝ)) := hmul
  · have hmul := mul_le_mul hdiff.2 hfactor_upper
        (by positivity : 0 ≤
          1 / (((m - r - 1 : ℕ) : ℝ)) + 1 / (m : ℝ))
        (by positivity : 0 ≤
          ((r + 1 : ℕ) : ℝ) /
            ((m : ℝ) * (((m - p + 1 : ℕ) : ℝ))))
    calc
      (1 / (((m - r - 1 : ℕ) : ℝ)) - 1 / (m : ℝ)) *
          (1 / (((m - r - 1 : ℕ) : ℝ)) + 1 / (m : ℝ)) ≤
          (((r + 1 : ℕ) : ℝ) /
            ((m : ℝ) * (((m - p + 1 : ℕ) : ℝ)))) *
              (2 / (((m - p + 1 : ℕ) : ℝ))) := hmul
      _ = 2 * ((r + 1 : ℕ) : ℝ) /
          ((m : ℝ) * (((m - p + 1 : ℕ) : ℝ)) ^ 2) := by ring

/-- Finite two-sided bounds for `nullALeading` in the dilute scaling. -/
theorem nullALeading_dilute_bounds {m p : ℕ} (h : Admissible m p) :
    4 * (p : ℝ) * ((p : ℝ) - 1) / (m : ℝ) ^ 3 ≤ nullALeading m p ∧
      nullALeading m p ≤
        4 * (p : ℝ) * ((p : ℝ) - 1) /
          ((m : ℝ) * (((m - p + 1 : ℕ) : ℝ)) ^ 2) := by
  have hp : 2 ≤ p := h.1
  rw [nullALeading, nullGapPowerDifference_eq_reverse_range 2 m p h]
  constructor
  · calc
      4 * (p : ℝ) * ((p : ℝ) - 1) / (m : ℝ) ^ 3 =
          4 * ∑ r ∈ Finset.range (p - 1),
            (2 * ((r + 1 : ℕ) : ℝ) / (m : ℝ) ^ 3) := by
        rw [← Finset.sum_div]
        rw [← Finset.mul_sum]
        have hs := twice_sum_range_succ_cast (p - 1)
        rw [Nat.cast_sub (by omega : 1 ≤ p)] at hs
        rw [hs]
        ring
      _ ≤ 4 * ∑ r ∈ Finset.range (p - 1),
          (1 / (((m - r - 1 : ℕ) : ℝ) ^ 2) - 1 / (m : ℝ) ^ 2) := by
        gcongr with r hr
        exact (inv_difference_two_bounds h hr).1
  · calc
      4 * ∑ r ∈ Finset.range (p - 1),
          (1 / (((m - r - 1 : ℕ) : ℝ) ^ 2) - 1 / (m : ℝ) ^ 2) ≤
          4 * ∑ r ∈ Finset.range (p - 1),
            (2 * ((r + 1 : ℕ) : ℝ) /
              ((m : ℝ) * (((m - p + 1 : ℕ) : ℝ)) ^ 2)) := by
        gcongr with r hr
        exact (inv_difference_two_bounds h hr).2
      _ = 4 * (p : ℝ) * ((p : ℝ) - 1) /
          ((m : ℝ) * (((m - p + 1 : ℕ) : ℝ)) ^ 2) := by
        rw [← Finset.sum_div]
        rw [← Finset.mul_sum]
        have hs := twice_sum_range_succ_cast (p - 1)
        rw [Nat.cast_sub (by omega : 1 ≤ p)] at hs
        rw [hs]
        ring

end

end LogdetLean
