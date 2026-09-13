import LogdetLean.NullAUniformAsymptotics
import LogdetLean.NullDiluteBounds
import Mathlib.Tactic

/-!
# Uniform variance asymptotics

The key finite observation is a left/right Riemann-sum comparison for
`log(m/d)`.  It preserves the cancellation in
`log(m/d) - (m-d)/m`, so the proof remains relative-error sharp even when
`m` is much larger than `p²`.
-/

namespace LogdetLean

noncomputable section

open Filter Real
open scoped Topology BigOperators

/-- The positive elementary quantity
`H = log(m/(m-p)) - p/m`. -/
def nullHScale (m p : ℕ) : ℝ :=
  Real.log ((m : ℝ) / ((m - p : ℕ) : ℝ)) -
    (p : ℝ) / (m : ℝ)

/-- The variance scale `2H`. -/
def nullVUniformScale (m p : ℕ) : ℝ := 2 * nullHScale m p

private theorem inv_succ_le_log_ratio_le_inv
    {k : ℕ} (hk : 1 ≤ k) :
    1 / (((k + 1 : ℕ) : ℝ)) ≤
        Real.log ((((k + 1 : ℕ) : ℝ) / (k : ℝ))) ∧
      Real.log ((((k + 1 : ℕ) : ℝ) / (k : ℝ))) ≤
        1 / (k : ℝ) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by positivity
  have hksR : (0 : ℝ) < (((k + 1 : ℕ) : ℝ)) := by positivity
  have hx : 0 < (((k + 1 : ℕ) : ℝ) / (k : ℝ)) :=
    div_pos hksR hkR
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos hx
    calc
      1 / (((k + 1 : ℕ) : ℝ)) =
          1 - ((((k + 1 : ℕ) : ℝ) / (k : ℝ)))⁻¹ := by
        push_cast
        field_simp [hkR.ne']
        ring
      _ ≤ Real.log ((((k + 1 : ℕ) : ℝ) / (k : ℝ))) := h
  · have h := Real.log_le_sub_one_of_pos hx
    calc
      Real.log ((((k + 1 : ℕ) : ℝ) / (k : ℝ))) ≤
          (((k + 1 : ℕ) : ℝ) / (k : ℝ)) - 1 := h
      _ = 1 / (k : ℝ) := by
        push_cast
        field_simp [hkR.ne']
        ring

private theorem sum_log_ratio_Ico_eq_log_div
    {d m : ℕ} (hd : 1 ≤ d) (hdm : d ≤ m) :
    (∑ k ∈ Finset.Ico d m,
      Real.log ((((k + 1 : ℕ) : ℝ) / (k : ℝ)))) =
        Real.log ((m : ℝ) / (d : ℝ)) := by
  have hdR : (d : ℝ) ≠ 0 := by positivity
  have hmR : (m : ℝ) ≠ 0 := by
    exact_mod_cast (show m ≠ 0 by omega)
  calc
    (∑ k ∈ Finset.Ico d m,
        Real.log ((((k + 1 : ℕ) : ℝ) / (k : ℝ)))) =
        ∑ k ∈ Finset.Ico d m,
          (Real.log (((k + 1 : ℕ) : ℝ)) - Real.log (k : ℝ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkpos : 0 < k := by have := (Finset.mem_Ico.mp hk).1; omega
      rw [Real.log_div (by positivity) (by positivity)]
    _ = Real.log (m : ℝ) - Real.log (d : ℝ) := by
      rw [Finset.sum_Ico_eq_sub _ hdm]
      have hmSum :
          (∑ k ∈ Finset.range m,
            (Real.log (((k + 1 : ℕ) : ℝ)) - Real.log (k : ℝ))) =
            Real.log (m : ℝ) := by
        calc
          (∑ k ∈ Finset.range m,
              (Real.log (((k + 1 : ℕ) : ℝ)) - Real.log (k : ℝ))) =
              Real.log (m : ℝ) - Real.log (0 : ℝ) := by
            simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] using
              (Finset.sum_range_sub (fun k : ℕ ↦ Real.log (k : ℝ)) m)
          _ = Real.log (m : ℝ) := by rw [Real.log_zero, sub_zero]
      have hdSum :
          (∑ k ∈ Finset.range d,
            (Real.log (((k + 1 : ℕ) : ℝ)) - Real.log (k : ℝ))) =
            Real.log (d : ℝ) := by
        calc
          (∑ k ∈ Finset.range d,
              (Real.log (((k + 1 : ℕ) : ℝ)) - Real.log (k : ℝ))) =
              Real.log (d : ℝ) - Real.log (0 : ℝ) := by
            simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] using
              (Finset.sum_range_sub (fun k : ℕ ↦ Real.log (k : ℝ)) d)
          _ = Real.log (d : ℝ) := by rw [Real.log_zero, sub_zero]
      rw [hmSum, hdSum]
    _ = Real.log ((m : ℝ) / (d : ℝ)) := by
      rw [Real.log_div hmR hdR]

private theorem sum_inv_succ_Ico_eq
    {d m : ℕ} (hdm : d < m) :
    (∑ k ∈ Finset.Ico d m, 1 / (((k + 1 : ℕ) : ℝ))) =
      (∑ k ∈ Finset.Ico (d + 1) m, 1 / (k : ℝ)) +
        1 / (m : ℝ) := by
  have hreindex :
      (∑ k ∈ Finset.Ico d m, 1 / (((k + 1 : ℕ) : ℝ))) =
        ∑ k ∈ Finset.Ico (d + 1) (m + 1), 1 / (k : ℝ) := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    have hlen : m + 1 - (d + 1) = m - d := by omega
    rw [hlen]
    apply Finset.sum_congr rfl
    intro k hk
    congr 2
    omega
  rw [hreindex]
  have hsplit := Finset.sum_Ico_succ_top
    (show d + 1 ≤ m by omega) (fun k : ℕ ↦ 1 / (k : ℝ))
  linarith

private theorem sum_inv_Ico_eq_bot_add
    {d m : ℕ} (hd : d < m) :
    (∑ k ∈ Finset.Ico d m, 1 / (k : ℝ)) =
      1 / (d : ℝ) + ∑ k ∈ Finset.Ico (d + 1) m, 1 / (k : ℝ) := by
  have hsplit := Finset.sum_Ico_sub_bot
    (fun k : ℕ ↦ 1 / (k : ℝ)) hd
  linarith

private theorem sum_inv_Ico_eq_harmonic_sub
    {d m : ℕ} (hdm : d < m) :
    (∑ k ∈ Finset.Ico (d + 1) m, 1 / (k : ℝ)) =
      (harmonic (m - 1) : ℝ) - (harmonic d : ℝ) := by
  rw [harmonic_eq_sum_Icc, harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  have hsub : Finset.Icc 1 d ⊆ Finset.Icc 1 (m - 1) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  rw [← Finset.sum_sdiff_eq_sub hsub]
  apply Finset.sum_congr
  · ext k
    simp only [Finset.mem_Ico, Finset.mem_sdiff, Finset.mem_Icc]
    omega
  · intro k hk
    simp only [one_div]

/-- Finite cancellation-preserving comparison between the harmonic leading
sum and `H`. -/
theorem nullVLeading_half_log_comparison
    {m p : ℕ} (h : Admissible m p) (hd : 1 ≤ m - p) :
    0 ≤ nullHScale m p - nullVLeading m p / 2 ∧
      nullHScale m p - nullVLeading m p / 2 ≤
        (p : ℝ) / ((m : ℝ) * ((m - p : ℕ) : ℝ)) := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hdpos : 1 ≤ m - p := hd
  have hdm : m - p < m := by omega
  have hlog := sum_log_ratio_Ico_eq_log_div hd (Nat.le_of_lt hdm)
  have hlowerSum :
      (∑ k ∈ Finset.Ico (m - p) m,
        1 / (((k + 1 : ℕ) : ℝ))) ≤
      ∑ k ∈ Finset.Ico (m - p) m,
        Real.log ((((k + 1 : ℕ) : ℝ) / (k : ℝ))) := by
    apply Finset.sum_le_sum
    intro k hk
    exact (inv_succ_le_log_ratio_le_inv (by
      have := (Finset.mem_Ico.mp hk).1; omega)).1
  have hupperSum :
      (∑ k ∈ Finset.Ico (m - p) m,
        Real.log ((((k + 1 : ℕ) : ℝ) / (k : ℝ)))) ≤
      ∑ k ∈ Finset.Ico (m - p) m, 1 / (k : ℝ) := by
    apply Finset.sum_le_sum
    intro k hk
    exact (inv_succ_le_log_ratio_le_inv (by
      have := (Finset.mem_Ico.mp hk).1; omega)).2
  rw [hlog] at hlowerSum hupperSum
  rw [sum_inv_succ_Ico_eq hdm] at hlowerSum
  rw [sum_inv_Ico_eq_bot_add hdm] at hupperSum
  rw [sum_inv_Ico_eq_harmonic_sub hdm] at hlowerSum hupperSum
  have hgap_eq :
      nullHScale m p - nullVLeading m p / 2 =
        Real.log ((m : ℝ) / ((m - p : ℕ) : ℝ)) -
          ((harmonic (m - 1) : ℝ) - (harmonic (m - p) : ℝ)) -
          1 / (m : ℝ) := by
    rw [nullVLeading_eq_harmonic_sub h]
    unfold nullHScale
    ring
  constructor
  · rw [hgap_eq]
    linarith
  · have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    have hdR : (0 : ℝ) < ((m - p : ℕ) : ℝ) := by exact_mod_cast hdpos
    have hid : 1 / ((m - p : ℕ) : ℝ) - 1 / (m : ℝ) =
        (p : ℝ) / ((m : ℝ) * ((m - p : ℕ) : ℝ)) := by
      field_simp [hmR.ne', hdR.ne']
      rw [Nat.cast_sub hpm]
      ring
    rw [hgap_eq]
    rw [← hid]
    linarith

/-- The elementary scale `H` is strictly positive throughout the nonsingular
domain `m > p`. -/
theorem nullHScale_pos {m p : ℕ} (h : Admissible m p) (hd : 1 ≤ m - p) :
    0 < nullHScale m p := by
  have hp : 2 ≤ p := h.1
  have hm : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hpR : 0 < (p : ℝ) := by positivity
  have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp1R : 0 < (p : ℝ) - 1 := by linarith
  have hlower := (nullVLeading_dilute_bounds h).1
  have hlead : 0 < nullVLeading m p := by
    exact lt_of_lt_of_le (div_pos (mul_pos hpR hp1R) (sq_pos_of_pos hm)) hlower
  have hcomp := (nullVLeading_half_log_comparison h hd).1
  linarith

/-- The variance scale `2H` is strictly positive. -/
theorem nullVUniformScale_pos {m p : ℕ} (h : Admissible m p)
    (hd : 1 ≤ m - p) : 0 < nullVUniformScale m p := by
  unfold nullVUniformScale
  positivity [nullHScale_pos h hd]

/-- The leading harmonic sum differs from `2H` by a uniformly negligible
relative amount.  This finite estimate retains both gap and dimension terms. -/
theorem abs_nullVLeading_sub_uniformScale_relative_le
    {m p : ℕ} (h : Admissible m p) (hd : 1 ≤ m - p) :
    |nullVLeading m p - nullVUniformScale m p| ≤
      nullVUniformScale m p *
        (4 / ((m - p : ℕ) : ℝ) + 4 / (p : ℝ)) := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  let d : ℕ := m - p
  have hdN : 1 ≤ d := hd
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hpR : 0 < (p : ℝ) := by positivity
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hdN
  have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp1R : 0 < (p : ℝ) - 1 := by linarith
  have hcomp := nullVLeading_half_log_comparison h hd
  have hlower := (nullVLeading_dilute_bounds h).1
  have hscaleLower :
      (p : ℝ) * ((p : ℝ) - 1) / (m : ℝ) ^ 2 ≤
        nullVUniformScale m p := by
    unfold nullVUniformScale
    linarith
  have hsmall :
      2 * ((p : ℝ) / ((m : ℝ) * (d : ℝ))) ≤
        ((p : ℝ) * ((p : ℝ) - 1) / (m : ℝ) ^ 2) *
          (4 / (d : ℝ) + 4 / (p : ℝ)) := by
    have hmEq : (m : ℝ) = (p : ℝ) + (d : ℝ) := by
      dsimp [d]
      rw [Nat.cast_sub hpm]
      ring
    field_simp [hmR.ne', hpR.ne', hdR.ne']
    rw [hmEq]
    have hcoef : 2 * (p : ℝ) ≤ 4 * ((p : ℝ) - 1) := by linarith
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ (p : ℝ) + (d : ℝ)))
  have hrate : 0 ≤ 4 / (d : ℝ) + 4 / (p : ℝ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hscaleLower hrate
  have habs :
      |nullVLeading m p - nullVUniformScale m p| =
        2 * (nullHScale m p - nullVLeading m p / 2) := by
    unfold nullVUniformScale
    rw [abs_of_nonpos]
    · ring
    · linarith
  rw [habs]
  change
    2 * (nullHScale m p - nullVLeading m p / 2) ≤
      nullVUniformScale m p * (4 / (d : ℝ) + 4 / (p : ℝ))
  exact (mul_le_mul_of_nonneg_left hcomp.2 (by norm_num)).trans (hsmall.trans hscaled)

/-- Uniform finite relative error between the exact variance and its harmonic
leading sum.  The proof splits at `m-p = p`, using the hard-edge tail estimate
on one side and the endpoint estimate on the dilute side. -/
theorem abs_nullVSeries_sub_nullVLeading_relative_le
    {m p : ℕ} (h : Admissible m p) (hd : 1 ≤ m - p) :
    |nullVSeries m p - nullVLeading m p| ≤
      nullVUniformScale m p *
        (32 / ((m - p : ℕ) : ℝ) + 20 / (p : ℝ)) := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  let d : ℕ := m - p
  have hdN : 1 ≤ d := hd
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hpR : 0 < (p : ℝ) := by positivity
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hdN
  have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp1R : 0 < (p : ℝ) - 1 := by linarith
  have hlower := (nullVLeading_dilute_bounds h).1
  have hcomp := (nullVLeading_half_log_comparison h hd).1
  have hscaleLower :
      (p : ℝ) * ((p : ℝ) - 1) / (m : ℝ) ^ 2 ≤
        nullVUniformScale m p := by
    unfold nullVUniformScale
    linarith
  have hrate : 0 ≤ 32 / (d : ℝ) + 20 / (p : ℝ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hscaleLower hrate
  by_cases hdp : d ≤ p
  · have hbase := abs_nullVSeries_sub_nullVLeading_growingGap_le h hd
    change |nullVSeries m p - nullVLeading m p| ≤
      4 / (d : ℝ) + 4 * ((p : ℝ) - 1) / (m : ℝ) ^ 2 at hbase
    have hmle : m ≤ 2 * p := by dsimp [d] at hdp; omega
    have hmleR : (m : ℝ) ≤ 2 * (p : ℝ) := by exact_mod_cast hmle
    have halg :
        4 / (d : ℝ) + 4 * ((p : ℝ) - 1) / (m : ℝ) ^ 2 ≤
          ((p : ℝ) * ((p : ℝ) - 1) / (m : ℝ) ^ 2) *
            (32 / (d : ℝ) + 20 / (p : ℝ)) := by
      have hsq : (m : ℝ) ^ 2 ≤ 4 * (p : ℝ) ^ 2 := by
        have hfac := mul_nonneg (sub_nonneg.mpr hmleR)
          (add_nonneg hmR.le (by positivity : 0 ≤ 2 * (p : ℝ)))
        nlinarith
      have hpminus : 0 ≤ (p : ℝ) - 2 := by linarith
      have hpp := mul_nonneg hpR.le hpminus
      have hdpnonneg : 0 ≤ (d : ℝ) * ((p : ℝ) - 1) :=
        mul_nonneg hdR.le hp1R.le
      field_simp [hmR.ne', hpR.ne', hdR.ne']
      nlinarith
    exact hbase.trans (halg.trans hscaled)
  · have hpd : p ≤ d := by omega
    have hbase := abs_nullVSeries_sub_nullVLeading_endpoint_le h
    change |nullVSeries m p - nullVLeading m p| ≤
      4 * ((p : ℝ) - 1) / ((d + 1 : ℕ) : ℝ) ^ 2 +
        4 * ((p : ℝ) - 1) / (m : ℝ) ^ 2 at hbase
    have hmle : m ≤ 2 * (d + 1) := by dsimp [d] at hpd ⊢; omega
    have hmleR : (m : ℝ) ≤ 2 * ((d + 1 : ℕ) : ℝ) := by exact_mod_cast hmle
    have hdsR : 0 < ((d + 1 : ℕ) : ℝ) := by positivity
    have hfirst :
        4 * ((p : ℝ) - 1) / ((d + 1 : ℕ) : ℝ) ^ 2 ≤
          16 * ((p : ℝ) - 1) / (m : ℝ) ^ 2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hdsR) (sq_pos_of_pos hmR)).2
      have hsq : (m : ℝ) ^ 2 ≤ 4 * ((d + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
      nlinarith
    have halg :
        16 * ((p : ℝ) - 1) / (m : ℝ) ^ 2 +
            4 * ((p : ℝ) - 1) / (m : ℝ) ^ 2 ≤
          ((p : ℝ) * ((p : ℝ) - 1) / (m : ℝ) ^ 2) *
            (32 / (d : ℝ) + 20 / (p : ℝ)) := by
      have hnonneg : 0 ≤
          ((p : ℝ) * ((p : ℝ) - 1) / (m : ℝ) ^ 2) *
            (32 / (d : ℝ)) := by positivity
      calc
        16 * ((p : ℝ) - 1) / (m : ℝ) ^ 2 +
            4 * ((p : ℝ) - 1) / (m : ℝ) ^ 2 =
            ((p : ℝ) * ((p : ℝ) - 1) / (m : ℝ) ^ 2) *
              (20 / (p : ℝ)) := by field_simp [hpR.ne']; ring
        _ ≤ ((p : ℝ) * ((p : ℝ) - 1) / (m : ℝ) ^ 2) *
              (32 / (d : ℝ) + 20 / (p : ℝ)) := by
          ring_nf at hnonneg ⊢
          linarith
    exact hbase.trans ((add_le_add hfirst le_rfl).trans (halg.trans hscaled))

/-- One finite all-regime bound for the relative variance error. -/
theorem abs_nullVSeries_div_uniformScale_sub_one_le
    {m p : ℕ} (h : Admissible m p) (hd : 1 ≤ m - p) :
    |nullVSeries m p / nullVUniformScale m p - 1| ≤
      36 / ((m - p : ℕ) : ℝ) + 24 / (p : ℝ) := by
  have hspos := nullVUniformScale_pos h hd
  have hseries := abs_nullVSeries_sub_nullVLeading_relative_le h hd
  have hleading := abs_nullVLeading_sub_uniformScale_relative_le h hd
  have htri :
      |nullVSeries m p - nullVUniformScale m p| ≤
        nullVUniformScale m p *
          (36 / ((m - p : ℕ) : ℝ) + 24 / (p : ℝ)) := by
    calc
      |nullVSeries m p - nullVUniformScale m p| ≤
          |nullVSeries m p - nullVLeading m p| +
            |nullVLeading m p - nullVUniformScale m p| := by
        calc
          |nullVSeries m p - nullVUniformScale m p| =
              |(nullVSeries m p - nullVLeading m p) +
                (nullVLeading m p - nullVUniformScale m p)| := by ring_nf
          _ ≤ |nullVSeries m p - nullVLeading m p| +
                |nullVLeading m p - nullVUniformScale m p| := abs_add_le _ _
      _ ≤ nullVUniformScale m p *
            (32 / ((m - p : ℕ) : ℝ) + 20 / (p : ℝ)) +
          nullVUniformScale m p *
            (4 / ((m - p : ℕ) : ℝ) + 4 / (p : ℝ)) :=
        add_le_add hseries hleading
      _ = nullVUniformScale m p *
          (36 / ((m - p : ℕ) : ℝ) + 24 / (p : ℝ)) := by ring
  rw [div_sub_one hspos.ne', abs_div, abs_of_pos hspos]
  exact (div_le_iff₀ hspos).2 (by simpa [mul_comm] using htri)

/-- Uniform variance equivalent in every growing-gap array. -/
theorem tendsto_growingGap_nullVSeries_div_uniformScale
    {mseq pseq : ℕ → ℕ}
    (hp : Tendsto pseq atTop atTop)
    (hadm : ∀ᶠ n in atTop, Admissible (mseq n) (pseq n))
    (hgap : Tendsto (fun n ↦ mseq n - pseq n) atTop atTop) :
    Tendsto (fun n ↦ nullVSeries (mseq n) (pseq n) /
      nullVUniformScale (mseq n) (pseq n)) atTop (nhds 1) := by
  have hpR : Tendsto (fun n ↦ (pseq n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hp
  have hdR : Tendsto (fun n ↦ ((mseq n - pseq n : ℕ) : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hgap
  have herr : Tendsto (fun n ↦
      36 / ((mseq n - pseq n : ℕ) : ℝ) + 24 / (pseq n : ℝ))
      atTop (nhds 0) := by
    simpa using (hdR.const_div_atTop 36).add (hpR.const_div_atTop 24)
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero'
  · filter_upwards with n
    exact dist_nonneg
  · filter_upwards [hadm, hgap.eventually (eventually_ge_atTop 1)] with n hn hd
    simpa [Real.dist_eq] using
      abs_nullVSeries_div_uniformScale_sub_one_le hn hd
  · exact herr

/-- In a fixed positive gap, the elementary scale satisfies
`H(p+d,p) ~ log p`. -/
theorem tendsto_fixedGap_nullHScale_div_log (d : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun p : ℕ ↦
      nullHScale (p + d) p / Real.log (p : ℝ)) atTop (nhds 1) := by
  have hpR : Tendsto (fun p : ℕ ↦ (p : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlogp : Tendsto (fun p : ℕ ↦ Real.log (p : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hpR
  have hinvlog : Tendsto (fun p : ℕ ↦ 1 / Real.log (p : ℝ))
      atTop (nhds 0) := hlogp.const_div_atTop 1
  have hdiff : Tendsto (fun p : ℕ ↦
      Real.log ((p : ℝ) + (d : ℝ)) - Real.log (p : ℝ))
      atTop (nhds 0) :=
    (Real.tendsto_log_comp_add_sub_log (d : ℝ)).comp hpR
  have hlogRatio : Tendsto (fun p : ℕ ↦
      Real.log (((p + d : ℕ) : ℝ)) / Real.log (p : ℝ))
      atTop (nhds 1) := by
    have hsum : Tendsto (fun p : ℕ ↦
        1 + (Real.log ((p : ℝ) + (d : ℝ)) - Real.log (p : ℝ)) *
          (1 / Real.log (p : ℝ))) atTop (nhds 1) := by
      simpa only [mul_zero, add_zero] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ))
          atTop (nhds 1)).add (hdiff.mul hinvlog))
    apply hsum.congr'
    filter_upwards [eventually_ge_atTop 2] with p hp2
    have hlogpos : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp2)
    rw [Nat.cast_add]
    field_simp [hlogpos.ne']
    ring
  have hlogD : Tendsto (fun p : ℕ ↦
      Real.log (d : ℝ) / Real.log (p : ℝ)) atTop (nhds 0) := by
    have hh :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ Real.log (d : ℝ))
        atTop (nhds (Real.log (d : ℝ)))).mul hinvlog
    convert hh using 1 <;> simp [div_eq_mul_inv]
  have hdp : Tendsto (fun p : ℕ ↦ (d : ℝ) / (p : ℝ))
      atTop (nhds 0) := hpR.const_div_atTop (d : ℝ)
  have hfrac : Tendsto (fun p : ℕ ↦
      (p : ℝ) / (((p + d : ℕ) : ℝ))) atTop (nhds 1) := by
    have hden : Tendsto (fun p : ℕ ↦ 1 + (d : ℝ) / (p : ℝ))
        atTop (nhds 1) := by
      simpa only [add_zero] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ))
          atTop (nhds 1)).add hdp)
    have hinv := hden.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    have hinv' : Tendsto (fun p : ℕ ↦
        (1 + (d : ℝ) / (p : ℝ))⁻¹) atTop (nhds 1) := by
      simpa only [inv_one] using hinv
    apply hinv'.congr'
    filter_upwards [eventually_ge_atTop 1] with p hp1
    rw [Nat.cast_add]
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
    field_simp [hp0]
  have hfracSmall : Tendsto (fun p : ℕ ↦
      ((p : ℝ) / (((p + d : ℕ) : ℝ))) / Real.log (p : ℝ))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hfrac.mul hinvlog
  have hlim : Tendsto (fun p : ℕ ↦
      Real.log (((p + d : ℕ) : ℝ)) / Real.log (p : ℝ) -
        Real.log (d : ℝ) / Real.log (p : ℝ) -
        ((p : ℝ) / (((p + d : ℕ) : ℝ))) / Real.log (p : ℝ))
      atTop (nhds 1) := by
    simpa only [sub_zero] using (hlogRatio.sub hlogD).sub hfracSmall
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 2] with p hp2
  have hpd : p + d - p = d := by omega
  have hpdp : (0 : ℝ) < ((p + d : ℕ) : ℝ) := by positivity
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  unfold nullHScale
  rw [hpd, Real.log_div hpdp.ne' hdR.ne']
  ring

/-- Two-sequence fixed-gap wrapper for the `V/(2H)` equivalent. -/
theorem tendsto_fixedGap_nullVSeries_div_uniformScale
    (mseq pseq : ℕ → ℕ) (d : ℕ) (hd : 1 ≤ d)
    (hp : Tendsto pseq atTop atTop)
    (hgap : ∀ᶠ n in atTop, mseq n = pseq n + d) :
    Tendsto (fun n ↦ nullVSeries (mseq n) (pseq n) /
      nullVUniformScale (mseq n) (pseq n)) atTop (nhds 1) := by
  have hV := tendsto_fixedGap_nullVSeries_div_log_of_eventually_eq
    mseq pseq d hp hgap
  have hHbase := (tendsto_fixedGap_nullHScale_div_log d hd).comp hp
  have hH : Tendsto (fun n ↦
      nullVUniformScale (mseq n) (pseq n) / Real.log (pseq n : ℝ))
      atTop (nhds 2) := by
    have hmul : Tendsto (fun n ↦
        2 * (nullHScale (pseq n + d) (pseq n) /
          Real.log (pseq n : ℝ))) atTop (nhds 2) := by
      simpa only [mul_one, Function.comp_apply] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (2 : ℝ))
          atTop (nhds 2)).mul hHbase)
    apply hmul.congr'
    filter_upwards [hgap] with n hn
    unfold nullVUniformScale
    rw [hn]
    ring
  have hquot : Tendsto
      ((fun n ↦ nullVSeries (mseq n) (pseq n) / Real.log (pseq n : ℝ)) /
        (fun n ↦ nullVUniformScale (mseq n) (pseq n) /
          Real.log (pseq n : ℝ))) atTop (nhds 1) := by
    simpa only [div_self (by norm_num : (2 : ℝ) ≠ 0)] using
      hV.div hH (by norm_num : (2 : ℝ) ≠ 0)
  apply hquot.congr'
  filter_upwards [hp.eventually (eventually_ge_atTop 2), hgap] with n hn hmn
  have hlogpos : 0 < Real.log (pseq n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hscalePos : 0 < nullVUniformScale (mseq n) (pseq n) := by
    apply nullVUniformScale_pos
    · rw [hmn]
      exact ⟨hn, by omega⟩
    · rw [hmn]
      omega
  change
    (nullVSeries (mseq n) (pseq n) / Real.log (pseq n : ℝ)) /
        (nullVUniformScale (mseq n) (pseq n) / Real.log (pseq n : ℝ)) =
      nullVSeries (mseq n) (pseq n) /
        nullVUniformScale (mseq n) (pseq n)
  field_simp [hlogpos.ne', hscalePos.ne']

/-- Uniform variance equivalent along every admissible nonsquare array with
`p → ∞`.  This is equation `(V-H)` in the manuscript. -/
theorem tendsto_nullVSeries_div_uniformScale
    {mseq pseq : ℕ → ℕ}
    (hp : Tendsto pseq atTop atTop)
    (hadm : ∀ᶠ n in atTop, Admissible (mseq n) (pseq n))
    (hgapPos : ∀ᶠ n in atTop, 1 ≤ mseq n - pseq n) :
    Tendsto (fun n ↦ nullVSeries (mseq n) (pseq n) /
      nullVUniformScale (mseq n) (pseq n)) atTop (nhds 1) := by
  refine Filter.tendsto_of_subseq_tendsto (fun ns hns ↦ ?_)
  have hpns : Tendsto (pseq ∘ ns) atTop atTop := hp.comp hns
  obtain ⟨θ, hθ, hpmono⟩ := Filter.strictMono_subseq_of_tendsto_atTop hpns
  let pp : ℕ → ℕ := (pseq ∘ ns) ∘ θ
  let mm : ℕ → ℕ := (mseq ∘ ns) ∘ θ
  have hpp : StrictMono pp := by simpa [pp, Function.comp_apply] using hpmono
  have hadm' : ∀ᶠ n in atTop, Admissible (mm n) (pp n) := by
    have hh := hθ.tendsto_atTop.eventually (hns.eventually hadm)
    simpa [mm, pp, Function.comp_apply] using hh
  have hgapPos' : ∀ᶠ n in atTop, 1 ≤ mm n - pp n := by
    have hh := hθ.tendsto_atTop.eventually (hns.eventually hgapPos)
    simpa [mm, pp, Function.comp_apply] using hh
  let q : ℕ → ℕ := fun n ↦ mm n - pp n
  obtain ⟨φ, hφ, hcases⟩ := exists_cofinal_subsequence_const_or_atTop q
  let ppp : ℕ → ℕ := pp ∘ φ
  let mmm : ℕ → ℕ := mm ∘ φ
  have hppp : Tendsto ppp atTop atTop := (hpp.comp hφ).tendsto_atTop
  have hadm'' : ∀ᶠ n in atTop, Admissible (mmm n) (ppp n) := by
    have hh := hφ.tendsto_atTop.eventually hadm'
    simpa [mmm, ppp, Function.comp_apply] using hh
  have hgapPos'' : ∀ᶠ n in atTop, 1 ≤ mmm n - ppp n := by
    have hh := hφ.tendsto_atTop.eventually hgapPos'
    simpa [mmm, ppp, Function.comp_apply] using hh
  refine ⟨θ ∘ φ, ?_⟩
  have htarget : Tendsto (fun n ↦
      nullVSeries (mmm n) (ppp n) /
        nullVUniformScale (mmm n) (ppp n)) atTop (nhds 1) := by
    rcases hcases with ⟨d, hconst⟩ | hgapTop
    · have hd : 1 ≤ d := by
        have he := hgapPos''.exists
        obtain ⟨n, hn⟩ := he
        have hq := hconst n
        dsimp [mmm, ppp, Function.comp_apply] at hn
        dsimp [q, mmm, ppp, Function.comp_apply] at hq
        omega
      have hgapEq : ∀ᶠ n in atTop, mmm n = ppp n + d := by
        filter_upwards [hadm''] with n hn
        have hq := hconst n
        have hle := hn.2
        dsimp [q, mmm, ppp, Function.comp_apply] at hq hle ⊢
        omega
      exact tendsto_fixedGap_nullVSeries_div_uniformScale
        mmm ppp d hd hppp hgapEq
    · have hgap' : Tendsto (fun n ↦ mmm n - ppp n) atTop atTop := by
        change Tendsto (q ∘ φ) atTop atTop
        exact hgapTop
      exact tendsto_growingGap_nullVSeries_div_uniformScale hppp hadm'' hgap'
  simpa [mmm, ppp, mm, pp, Function.comp_apply, Function.comp_def] using htarget

end

end LogdetLean
