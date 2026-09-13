import LogdetLean.NullRegimeAsymptotics
import LogdetLean.HardEdgeTailAsymptotics
import LogdetLean.NullSharpSupremum
import Mathlib.Tactic

/-!
# Uniform third-cumulant asymptotics

This module proves the two uniform third-cumulant evaluations used in the
paper.  The finite argument keeps the cancellation in the power difference
before estimating it; this is what makes the result valid in both dense and
ultra-dilute regimes.
-/

namespace LogdetLean

noncomputable section

open Filter Real
open scoped Topology

/-- The elementary growing-gap scale `4p²/(d m²)`. -/
def nullAGrowingScale (m p : ℕ) : ℝ :=
  4 * (p : ℝ) ^ 2 /
    (((m - p : ℕ) : ℝ) * (m : ℝ) ^ 2)

/-- The all-gap scale `(p/m)² A_{m-p}` from the manuscript. -/
def nullAUniformScale (m p : ℕ) : ℝ :=
  ((p : ℝ) / (m : ℝ)) ^ 2 * hardEdgeAConstant (m - p)

/-- A simple finite sandwich for the cancellation-preserving quadratic
power difference. -/
theorem nullGapPowerDifference_two_sandwich
    {m p : ℕ} (h : Admissible m p) (hd : 1 ≤ m - p) :
    ((p : ℝ) - 1) ^ 2 /
        ((m : ℝ) ^ 2 * (((m - p : ℕ) : ℝ) + 1)) ≤
      nullGapPowerDifference 2 m p ∧
    nullGapPowerDifference 2 m p ≤
      (p : ℝ) ^ 2 / (((m - p : ℕ) : ℝ) * (m : ℝ) ^ 2) := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hm : 0 < m := by omega
  have hdpos : 0 < m - p := by omega
  have hmNat : 0 < m := by omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmNat
  have hdR : (0 : ℝ) < ((m - p : ℕ) : ℝ) := by positivity
  have hm1 : 0 < m - 1 := by omega
  have hm1R : (0 : ℝ) < (((m - 1 : ℕ) : ℝ)) := by exact_mod_cast hm1
  have hmpR : (0 : ℝ) < (m : ℝ) - (p : ℝ) := by
    rw [← Nat.cast_sub hpm]
    exact_mod_cast hdpos
  have hmMinusR : (0 : ℝ) < (m : ℝ) - 1 := by
    have hm2 : 2 ≤ m := hp.trans hpm
    have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    linarith
  have hdp1R : (0 : ℝ) < (m : ℝ) - (p : ℝ) + 1 := by
    exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr (by exact_mod_cast hpm)) zero_lt_one
  have hb := nullGapPowerDifference_two_bounds h hd
  constructor
  · calc
      ((p : ℝ) - 1) ^ 2 /
          ((m : ℝ) ^ 2 * (((m - p : ℕ) : ℝ) + 1)) =
          1 / (((m - p + 1 : ℕ) : ℝ)) - 1 / (m : ℝ) -
            ((p : ℝ) - 1) / (m : ℝ) ^ 2 := by
        rw [Nat.cast_add, Nat.cast_one]
        rw [Nat.cast_sub hpm]
        field_simp [hmR.ne', hdp1R.ne']
        ring
      _ ≤ nullGapPowerDifference 2 m p := hb.1
  · calc
      nullGapPowerDifference 2 m p ≤
          1 / (((m - p : ℕ) : ℝ)) -
            1 / (((m - 1 : ℕ) : ℝ)) -
            ((p : ℝ) - 1) / (m : ℝ) ^ 2 := hb.2
      _ ≤ (p : ℝ) ^ 2 /
          (((m - p : ℕ) : ℝ) * (m : ℝ) ^ 2) := by
        rw [Nat.cast_sub hpm, Nat.cast_sub (by omega : 1 ≤ m)]
        simp only [Nat.cast_one]
        calc
          1 / ((m : ℝ) - p) - 1 / ((m : ℝ) - 1) -
              ((p : ℝ) - 1) / (m : ℝ) ^ 2 =
              (p : ℝ) ^ 2 / (((m : ℝ) - p) * (m : ℝ) ^ 2) -
                1 / ((m : ℝ) ^ 2 * ((m : ℝ) - 1)) := by
            field_simp [hmpR.ne', hmMinusR.ne', hmR.ne']
            ring
          _ ≤ (p : ℝ) ^ 2 /
              (((m : ℝ) - p) * (m : ℝ) ^ 2) :=
            sub_le_self _ (by
              exact one_div_nonneg.mpr
                (mul_nonneg (sq_nonneg _) hmMinusR.le))

/-- Relative finite error of the elementary leading third-cumulant sum. -/
theorem abs_nullALeading_sub_growingScale_le
    {m p : ℕ} (h : Admissible m p) (hd : 1 ≤ m - p) :
    |nullALeading m p - nullAGrowingScale m p| ≤
      nullAGrowingScale m p *
        (2 / (p : ℝ) + 1 / ((m - p : ℕ) : ℝ)) := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hmNat : 0 < m := by omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmNat
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hdR : (0 : ℝ) < ((m - p : ℕ) : ℝ) := by positivity
  have hdp1R : (0 : ℝ) < ((m - p : ℕ) : ℝ) + 1 := by positivity
  have hs := nullGapPowerDifference_two_sandwich h hd
  have hleadUpper : nullALeading m p ≤ nullAGrowingScale m p := by
    unfold nullALeading nullAGrowingScale
    calc
      4 * nullGapPowerDifference 2 m p ≤
          4 * ((p : ℝ) ^ 2 /
            (((m - p : ℕ) : ℝ) * (m : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hs.2 (by norm_num)
      _ = 4 * (p : ℝ) ^ 2 /
          (((m - p : ℕ) : ℝ) * (m : ℝ) ^ 2) := by ring
  have hleadLower :
      4 * (((p : ℝ) - 1) ^ 2 /
          ((m : ℝ) ^ 2 * (((m - p : ℕ) : ℝ) + 1))) ≤
        nullALeading m p := by
    unfold nullALeading
    exact mul_le_mul_of_nonneg_left hs.1 (by norm_num)
  rw [abs_of_nonpos (sub_nonpos.mpr hleadUpper)]
  have hfinite :
      nullAGrowingScale m p -
          4 * (((p : ℝ) - 1) ^ 2 /
            ((m : ℝ) ^ 2 * (((m - p : ℕ) : ℝ) + 1))) ≤
        nullAGrowingScale m p *
          (2 / (p : ℝ) + 1 / ((m - p : ℕ) : ℝ)) := by
    unfold nullAGrowingScale
    field_simp [hmR.ne', hpR.ne', hdR.ne', hdp1R.ne']
    nlinarith
  linarith

/-- The polygamma remainder is uniformly small relative to the growing-gap
scale.  The proof uses the dense estimate when `d ≤ p` and the endpoint
estimate when `p ≤ d`. -/
theorem abs_nullASeries_sub_nullALeading_relative_le
    {m p : ℕ} (h : Admissible m p) (hd : 1 ≤ m - p) :
    |nullASeries m p - nullALeading m p| ≤
      nullAGrowingScale m p *
        (16 / ((m - p : ℕ) : ℝ) + 20 / (p : ℝ)) := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hmNat : 0 < m := by omega
  have hdNat : 0 < m - p := by omega
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmNat
  have hdR : (0 : ℝ) < ((m - p : ℕ) : ℝ) := by exact_mod_cast hdNat
  have hsecond :
      16 * ((p : ℝ) - 1) / (m : ℝ) ^ 3 ≤
        nullAGrowingScale m p * (4 / (p : ℝ)) := by
    have hdp : ((m - p : ℕ) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast (Nat.sub_le m p)
    have hpone : (p : ℝ) - 1 ≤ (p : ℝ) := by linarith
    have hprod : ((m - p : ℕ) : ℝ) * ((p : ℝ) - 1) ≤
        (m : ℝ) * (p : ℝ) :=
      mul_le_mul hdp hpone (by linarith [hp2R]) (by positivity)
    unfold nullAGrowingScale
    field_simp [hpR.ne', hmR.ne', hdR.ne']
    nlinarith
  rcases le_total (m - p) p with hdle | hple
  · have hmleNat : m ≤ 2 * p := by omega
    have hmle : (m : ℝ) ≤ 2 * (p : ℝ) := by exact_mod_cast hmleNat
    have hsq : (m : ℝ) ^ 2 ≤ 4 * (p : ℝ) ^ 2 := by nlinarith
    have hfirst : 16 / ((m - p : ℕ) : ℝ) ^ 2 ≤
        nullAGrowingScale m p *
          (16 / ((m - p : ℕ) : ℝ)) := by
      unfold nullAGrowingScale
      field_simp [hpR.ne', hmR.ne', hdR.ne']
      nlinarith
    have hbase := abs_nullASeries_sub_nullALeading_growingGap_le h hd
    calc
      |nullASeries m p - nullALeading m p| ≤
          16 / ((m - p : ℕ) : ℝ) ^ 2 +
            16 * ((p : ℝ) - 1) / (m : ℝ) ^ 3 := hbase
      _ ≤ nullAGrowingScale m p *
            (16 / ((m - p : ℕ) : ℝ)) +
          nullAGrowingScale m p * (4 / (p : ℝ)) :=
        add_le_add hfirst hsecond
      _ ≤ nullAGrowingScale m p *
          (16 / ((m - p : ℕ) : ℝ) + 20 / (p : ℝ)) := by
        have hscale : 0 ≤ nullAGrowingScale m p := by
          unfold nullAGrowingScale
          positivity
        have hfour : 4 / (p : ℝ) ≤ 20 / (p : ℝ) := by
          exact div_le_div_of_nonneg_right (by norm_num) hpR.le
        rw [mul_add]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hfour hscale)
  · have hmleNat : m ≤ 2 * (m - p) := by omega
    have hmle : (m : ℝ) ≤ 2 * ((m - p : ℕ) : ℝ) := by
      exact_mod_cast hmleNat
    have hsq : (m : ℝ) ^ 2 ≤
        4 * ((m - p : ℕ) : ℝ) ^ 2 := by nlinarith
    have hpone : (p : ℝ) - 1 ≤ (p : ℝ) := by linarith
    have hdpone : ((m - p : ℕ) : ℝ) ≤
        ((m - p + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_succ (m - p))
    have hfirstA :
        16 * ((p : ℝ) - 1) / (((m - p + 1 : ℕ) : ℝ) ^ 3) ≤
          16 * (p : ℝ) / ((m - p : ℕ) : ℝ) ^ 3 := by
      gcongr
    have hfirstB : 16 * (p : ℝ) / ((m - p : ℕ) : ℝ) ^ 3 ≤
        nullAGrowingScale m p * (16 / (p : ℝ)) := by
      unfold nullAGrowingScale
      field_simp [hpR.ne', hmR.ne', hdR.ne']
      nlinarith
    have hbase := abs_nullASeries_sub_nullALeading_endpoint_le h
    calc
      |nullASeries m p - nullALeading m p| ≤
          16 * ((p : ℝ) - 1) / (((m - p + 1 : ℕ) : ℝ) ^ 3) +
            16 * ((p : ℝ) - 1) / (m : ℝ) ^ 3 := hbase
      _ ≤ nullAGrowingScale m p * (16 / (p : ℝ)) +
          nullAGrowingScale m p * (4 / (p : ℝ)) :=
        add_le_add (hfirstA.trans hfirstB) hsecond
      _ = nullAGrowingScale m p * (20 / (p : ℝ)) := by ring
      _ ≤ nullAGrowingScale m p *
          (16 / ((m - p : ℕ) : ℝ) + 20 / (p : ℝ)) := by
        have hscale : 0 ≤ nullAGrowingScale m p := by
          unfold nullAGrowingScale
          positivity
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) hscale

/-- Uniform finite relative error for `A_{m,p}` at every positive gap. -/
theorem abs_nullASeries_div_growingScale_sub_one_le
    {m p : ℕ} (h : Admissible m p) (hd : 1 ≤ m - p) :
    |nullASeries m p / nullAGrowingScale m p - 1| ≤
      17 / ((m - p : ℕ) : ℝ) + 22 / (p : ℝ) := by
  have hp : 2 ≤ p := h.1
  have hm : 0 < m := by omega
  have hscale : 0 < nullAGrowingScale m p := by
    unfold nullAGrowingScale
    positivity
  have htri : |nullASeries m p - nullAGrowingScale m p| ≤
      |nullASeries m p - nullALeading m p| +
        |nullALeading m p - nullAGrowingScale m p| := by
    calc
      |nullASeries m p - nullAGrowingScale m p| =
          |(nullASeries m p - nullALeading m p) +
            (nullALeading m p - nullAGrowingScale m p)| := by ring_nf
      _ ≤ |nullASeries m p - nullALeading m p| +
          |nullALeading m p - nullAGrowingScale m p| := abs_add_le _ _
  have hrem := abs_nullASeries_sub_nullALeading_relative_le h hd
  have hlead := abs_nullALeading_sub_growingScale_le h hd
  have habs : |nullASeries m p - nullAGrowingScale m p| ≤
      nullAGrowingScale m p *
        (17 / ((m - p : ℕ) : ℝ) + 22 / (p : ℝ)) := by
    calc
      |nullASeries m p - nullAGrowingScale m p| ≤
          |nullASeries m p - nullALeading m p| +
            |nullALeading m p - nullAGrowingScale m p| := htri
      _ ≤ nullAGrowingScale m p *
            (16 / ((m - p : ℕ) : ℝ) + 20 / (p : ℝ)) +
          nullAGrowingScale m p *
            (2 / (p : ℝ) + 1 / ((m - p : ℕ) : ℝ)) :=
        add_le_add hrem hlead
      _ = nullAGrowingScale m p *
          (17 / ((m - p : ℕ) : ℝ) + 22 / (p : ℝ)) := by ring
  rw [show nullASeries m p / nullAGrowingScale m p - 1 =
      (nullASeries m p - nullAGrowingScale m p) /
        nullAGrowingScale m p by field_simp]
  rw [abs_div, abs_of_pos hscale]
  exact (div_le_iff₀ hscale).2 (by simpa [mul_comm] using habs)

/-- Uniform growing-gap equivalent
`A_{m,p} ~ 4p²/((m-p)m²)` along arbitrary two-sequences. -/
theorem tendsto_growingGap_nullASeries_div_growingScale
    {mseq pseq : ℕ → ℕ}
    (hp : Tendsto pseq atTop atTop)
    (hadm : ∀ᶠ n in atTop, Admissible (mseq n) (pseq n))
    (hgap : Tendsto (fun n ↦ mseq n - pseq n) atTop atTop) :
    Tendsto (fun n ↦ nullASeries (mseq n) (pseq n) /
      nullAGrowingScale (mseq n) (pseq n)) atTop (nhds 1) := by
  have hpR : Tendsto (fun n ↦ (pseq n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hp
  have hdR : Tendsto (fun n ↦ ((mseq n - pseq n : ℕ) : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hgap
  have herr : Tendsto (fun n ↦
      17 / ((mseq n - pseq n : ℕ) : ℝ) +
        22 / (pseq n : ℝ)) atTop (nhds 0) := by
    simpa using (hdR.const_div_atTop 17).add (hpR.const_div_atTop 22)
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero'
  · filter_upwards with n
    exact dist_nonneg
  · filter_upwards [hadm,
      hgap.eventually (eventually_ge_atTop 1)] with n hn hd
    simpa [Real.dist_eq] using
      abs_nullASeries_div_growingScale_sub_one_le hn hd
  · exact herr

/-- In a growing gap, the elementary and all-gap scales are asymptotically
equivalent because `d A_d → 4`. -/
theorem tendsto_growingGap_growingScale_div_uniformScale
    {mseq pseq : ℕ → ℕ}
    (_hp : Tendsto pseq atTop atTop)
    (hadm : ∀ᶠ n in atTop, Admissible (mseq n) (pseq n))
    (hgap : Tendsto (fun n ↦ mseq n - pseq n) atTop atTop) :
    Tendsto (fun n ↦ nullAGrowingScale (mseq n) (pseq n) /
      nullAUniformScale (mseq n) (pseq n)) atTop (nhds 1) := by
  have htail := tendsto_gap_mul_hardEdgeAConstant.comp hgap
  have hquot : Tendsto (fun n ↦
      4 / (((mseq n - pseq n : ℕ) : ℝ) *
        hardEdgeAConstant (mseq n - pseq n))) atTop (nhds 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (4 : ℝ))
      atTop (nhds 4)).div htail (by norm_num)
    have heq :
        (fun _ : ℕ ↦ (4 : ℝ)) /
          ((fun d : ℕ ↦ (d : ℝ) * hardEdgeAConstant d) ∘
            (fun n ↦ mseq n - pseq n)) =
          (fun n ↦ 4 / (((mseq n - pseq n : ℕ) : ℝ) *
            hardEdgeAConstant (mseq n - pseq n))) := by
      funext n
      rfl
    rw [heq] at h
    simpa using h
  apply hquot.congr'
  filter_upwards [hadm, hgap.eventually (eventually_ge_atTop 1)] with n hn hd
  have hpN : 0 < pseq n := by have := hn.1; omega
  have hmN : 0 < mseq n := by have := hn.1; have := hn.2; omega
  have hdN : 0 < mseq n - pseq n := by omega
  have hpR : (pseq n : ℝ) ≠ 0 := by exact_mod_cast hpN.ne'
  have hmR : (mseq n : ℝ) ≠ 0 := by exact_mod_cast hmN.ne'
  have hdR : ((mseq n - pseq n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hdN.ne'
  have hA : hardEdgeAConstant (mseq n - pseq n) ≠ 0 :=
    (hardEdgeAConstant_pos _).ne'
  unfold nullAGrowingScale nullAUniformScale
  field_simp [hpR, hmR, hdR, hA]

/-- The manuscript's uniform `A`-equivalent on the growing-gap branch. -/
theorem tendsto_growingGap_nullASeries_div_uniformScale
    {mseq pseq : ℕ → ℕ}
    (hp : Tendsto pseq atTop atTop)
    (hadm : ∀ᶠ n in atTop, Admissible (mseq n) (pseq n))
    (hgap : Tendsto (fun n ↦ mseq n - pseq n) atTop atTop) :
    Tendsto (fun n ↦ nullASeries (mseq n) (pseq n) /
      nullAUniformScale (mseq n) (pseq n)) atTop (nhds 1) := by
  have hA := tendsto_growingGap_nullASeries_div_growingScale hp hadm hgap
  have hs := tendsto_growingGap_growingScale_div_uniformScale hp hadm hgap
  have hmul := hA.mul hs
  have hmul' : Tendsto (fun n ↦
      nullASeries (mseq n) (pseq n) /
          nullAGrowingScale (mseq n) (pseq n) *
        (nullAGrowingScale (mseq n) (pseq n) /
          nullAUniformScale (mseq n) (pseq n))) atTop (nhds 1) := by
    simpa using hmul
  apply hmul'.congr'
  filter_upwards [hadm, hgap.eventually (eventually_ge_atTop 1)] with n hn hd
  have hpN : 0 < pseq n := by have := hn.1; omega
  have hmN : 0 < mseq n := by have := hn.1; have := hn.2; omega
  have hdN : 0 < mseq n - pseq n := by omega
  have hpR : (0 : ℝ) < (pseq n : ℝ) := by exact_mod_cast hpN
  have hmR : (0 : ℝ) < (mseq n : ℝ) := by exact_mod_cast hmN
  have hdR : (0 : ℝ) < ((mseq n - pseq n : ℕ) : ℝ) := by
    exact_mod_cast hdN
  have hg : nullAGrowingScale (mseq n) (pseq n) ≠ 0 := by
    exact (by unfold nullAGrowingScale; positivity :
      0 < nullAGrowingScale (mseq n) (pseq n)).ne'
  have hu : nullAUniformScale (mseq n) (pseq n) ≠ 0 := by
    unfold nullAUniformScale
    exact mul_ne_zero
      (pow_ne_zero 2 (div_ne_zero hpR.ne' hmR.ne'))
      (hardEdgeAConstant_pos _).ne'
  field_simp [hg, hu]

/-- The manuscript's uniform `A`-equivalent on every fixed-gap branch. -/
theorem tendsto_fixedGap_nullASeries_div_uniformScale
    {mseq pseq : ℕ → ℕ} (d : ℕ)
    (hp : Tendsto pseq atTop atTop)
    (hgap : ∀ᶠ n in atTop, mseq n = pseq n + d) :
    Tendsto (fun n ↦ nullASeries (mseq n) (pseq n) /
      nullAUniformScale (mseq n) (pseq n)) atTop (nhds 1) := by
  have hA := tendsto_fixedGap_nullASeries_of_eventually_eq mseq pseq d hp hgap
  have hpR : Tendsto (fun n ↦ (pseq n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hp
  have hdp : Tendsto (fun n ↦ (d : ℝ) / (pseq n : ℝ))
      atTop (nhds 0) := hpR.const_div_atTop (d : ℝ)
  have hratioBase : Tendsto (fun n ↦
      1 / (1 + (d : ℝ) / (pseq n : ℝ))) atTop (nhds 1) := by
    have hadd := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ))
      atTop (nhds 1)).add hdp
    have hinv := hadd.inv₀ (by norm_num : (1 + 0 : ℝ) ≠ 0)
    simpa using hinv
  have hratio : Tendsto (fun n ↦
      (pseq n : ℝ) / ((pseq n + d : ℕ) : ℝ)) atTop (nhds 1) := by
    apply hratioBase.congr'
    filter_upwards [hp.eventually (eventually_ge_atTop 1)] with n hn
    have hp0 : (pseq n : ℝ) ≠ 0 := by exact_mod_cast (show pseq n ≠ 0 by omega)
    rw [Nat.cast_add]
    field_simp [hp0]
  have hscaleFixed : Tendsto (fun n ↦
      ((pseq n : ℝ) / ((pseq n + d : ℕ) : ℝ)) ^ 2 *
        hardEdgeAConstant d) atTop (nhds (hardEdgeAConstant d)) := by
    have hpow := hratio.pow 2
    simpa using hpow.mul_const (hardEdgeAConstant d)
  have hscale : Tendsto (fun n ↦ nullAUniformScale (mseq n) (pseq n))
      atTop (nhds (hardEdgeAConstant d)) := by
    apply hscaleFixed.congr'
    filter_upwards [hgap] with n hn
    unfold nullAUniformScale
    rw [hn]
    simp only [Nat.add_sub_cancel_left]
  have hquot := hA.div hscale (hardEdgeAConstant_pos d).ne'
  have heq :
      (fun n ↦ nullASeries (mseq n) (pseq n)) /
          (fun n ↦ nullAUniformScale (mseq n) (pseq n)) =
        (fun n ↦ nullASeries (mseq n) (pseq n) /
          nullAUniformScale (mseq n) (pseq n)) := by
    funext n
    rfl
  rw [heq] at hquot
  simpa only [div_self (hardEdgeAConstant_pos d).ne'] using hquot

/-- Uniform third-cumulant equivalent along every admissible array with
`p → ∞`.  This is equation `(A-uniform)` of the manuscript. -/
theorem tendsto_nullASeries_div_uniformScale
    {mseq pseq : ℕ → ℕ}
    (hp : Tendsto pseq atTop atTop)
    (hadm : ∀ᶠ n in atTop, Admissible (mseq n) (pseq n)) :
    Tendsto (fun n ↦ nullASeries (mseq n) (pseq n) /
      nullAUniformScale (mseq n) (pseq n)) atTop (nhds 1) := by
  refine Filter.tendsto_of_subseq_tendsto (fun ns hns ↦ ?_)
  have hpns : Tendsto (pseq ∘ ns) atTop atTop := hp.comp hns
  obtain ⟨θ, hθ, hpmono⟩ := Filter.strictMono_subseq_of_tendsto_atTop hpns
  let pp : ℕ → ℕ := (pseq ∘ ns) ∘ θ
  let mm : ℕ → ℕ := (mseq ∘ ns) ∘ θ
  have hpp : StrictMono pp := by simpa [pp, Function.comp_apply] using hpmono
  have hadm' : ∀ᶠ n in atTop, Admissible (mm n) (pp n) := by
    have h := hθ.tendsto_atTop.eventually (hns.eventually hadm)
    simpa [mm, pp, Function.comp_apply] using h
  let q : ℕ → ℕ := fun n ↦ mm n - pp n
  obtain ⟨φ, hφ, hcases⟩ := exists_cofinal_subsequence_const_or_atTop q
  let ppp : ℕ → ℕ := pp ∘ φ
  let mmm : ℕ → ℕ := mm ∘ φ
  have hppp : Tendsto ppp atTop atTop := (hpp.comp hφ).tendsto_atTop
  have hadm'' : ∀ᶠ n in atTop, Admissible (mmm n) (ppp n) := by
    have h := hφ.tendsto_atTop.eventually hadm'
    simpa [mmm, ppp, Function.comp_apply] using h
  refine ⟨θ ∘ φ, ?_⟩
  have htarget : Tendsto (fun n ↦
      nullASeries (mmm n) (ppp n) /
        nullAUniformScale (mmm n) (ppp n)) atTop (nhds 1) := by
    rcases hcases with ⟨d, hconst⟩ | hgapTop
    · have hgapEq : ∀ᶠ n in atTop, mmm n = ppp n + d := by
        filter_upwards [hadm''] with n hn
        have hq := hconst n
        have hle := hn.2
        dsimp [q, mmm, ppp, Function.comp_apply] at hq hle ⊢
        omega
      exact tendsto_fixedGap_nullASeries_div_uniformScale d hppp hgapEq
    · have hgap' : Tendsto (fun n ↦ mmm n - ppp n) atTop atTop := by
        change Tendsto (q ∘ φ) atTop atTop
        exact hgapTop
      exact tendsto_growingGap_nullASeries_div_uniformScale hppp hadm'' hgap'
  simpa [mm, pp, mmm, ppp, Function.comp_apply] using htarget

end

end LogdetLean
