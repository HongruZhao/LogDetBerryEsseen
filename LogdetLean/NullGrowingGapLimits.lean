import LogdetLean.NullRegimeAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Growing-gap limits for the null log-determinant

This file consumes the exact finite comparison inequalities from
`NullRegimeAsymptotics.lean`.  Its first theorem is the divergent-gap
exclusion needed by the sharp constrained supremum: along every admissible
two-sequence with `p → ∞` and `m-p → ∞`,

`(log p)^(3/2) * nullLambdaSeries m p → 0`.

The proof uses three elementary finite cases (dilute, dense with a large
gap, and dense with a small gap), exactly as in Appendix D of the manuscript.
-/

namespace LogdetLean

open Filter Real Set
open scoped Topology

noncomputable section

private theorem rpow_three_halves_eq_mul_sqrt {x : ℝ} (hx : 0 < x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by ring,
    Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- A coarse but uniform `O(1/(m-p))` upper bound for the exact positive
third-cumulant magnitude.  It is used only when the gap diverges. -/
theorem nullASeries_le_thirtySix_div_gap {m p : ℕ}
    (h : Admissible m p) (hd : 1 ≤ m - p) :
    nullASeries m p ≤ 36 / ((m - p : ℕ) : ℝ) := by
  let d : ℕ := m - p
  have hp2 : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hdR : 0 < (d : ℝ) := by
    have hdN : 0 < d := by dsimp [d]; omega
    exact_mod_cast hdN
  have hmR : 0 < (m : ℝ) := by
    exact_mod_cast (show 0 < m by omega)
  have hdmR : (d : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (show d ≤ m by simp [d])
  have hpR : (p : ℝ) ≤ (m : ℝ) := by exact_mod_cast h.2
  have hmOne : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (show 1 ≤ m by omega)
  have hS2 := (nullGapPowerDifference_two_bounds h hd).2
  have hS2upper : nullGapPowerDifference 2 m p ≤ 1 / (d : ℝ) := by
    have hm1pos : 0 < m - 1 := by omega
    have hterm1 : 0 ≤ 1 / (((m - 1 : ℕ) : ℝ)) := by positivity
    have hterm2 : 0 ≤ ((p : ℝ) - 1) / (m : ℝ) ^ 2 := by
      have hpOne : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (show 1 ≤ p by omega)
      positivity
    have : nullGapPowerDifference 2 m p ≤ 1 / (((m - p : ℕ) : ℝ)) := by
      linarith [hS2]
    simpa only [d] using this
  have hALeading : nullALeading m p ≤ 4 / (d : ℝ) := by
    calc
      nullALeading m p = 4 * nullGapPowerDifference 2 m p := rfl
      _ ≤ 4 * (1 / (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hS2upper (by norm_num)
      _ = 4 / (d : ℝ) := by ring
  have hdiff := abs_nullASeries_sub_nullALeading_growingGap_le h hd
  have hdiff' : nullASeries m p - nullALeading m p ≤
      16 / (d : ℝ) ^ 2 + 16 * ((p : ℝ) - 1) / (m : ℝ) ^ 3 := by
    exact (le_abs_self _).trans (by simpa only [d] using hdiff)
  have hinvSq : 16 / (d : ℝ) ^ 2 ≤ 16 / (d : ℝ) := by
    have hdOne : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    apply (div_le_div_iff₀ (sq_pos_of_pos hdR) hdR).2
    nlinarith
  have hpTerm : 16 * ((p : ℝ) - 1) / (m : ℝ) ^ 3 ≤
      16 / (d : ℝ) := by
    have hpred : (p : ℝ) - 1 ≤ (m : ℝ) := by linarith
    have hfirst : ((p : ℝ) - 1) / (m : ℝ) ^ 3 ≤
        (m : ℝ) / (m : ℝ) ^ 3 := by
      exact div_le_div_of_nonneg_right hpred (by positivity)
    have hmSq : (d : ℝ) ≤ (m : ℝ) ^ 2 := by
      nlinarith
    have hsecond : (m : ℝ) / (m : ℝ) ^ 3 ≤ 1 / (d : ℝ) := by
      apply (div_le_div_iff₀ (pow_pos hmR 3) hdR).2
      nlinarith
    calc
      16 * ((p : ℝ) - 1) / (m : ℝ) ^ 3 =
          16 * (((p : ℝ) - 1) / (m : ℝ) ^ 3) := by ring
      _ ≤ 16 * (1 / (d : ℝ)) :=
        mul_le_mul_of_nonneg_left (hfirst.trans hsecond) (by norm_num)
      _ = 16 / (d : ℝ) := by ring
  have hmain : nullASeries m p ≤
      4 / (d : ℝ) + 16 / (d : ℝ) + 16 / (d : ℝ) := by
    calc
      nullASeries m p ≤ nullALeading m p +
          (16 / (d : ℝ) ^ 2 +
            16 * ((p : ℝ) - 1) / (m : ℝ) ^ 3) := by linarith
      _ ≤ 4 / (d : ℝ) +
          (16 / (d : ℝ) + 16 / (d : ℝ)) := by
        exact add_le_add hALeading (add_le_add hinvSq hpTerm)
      _ = 4 / (d : ℝ) + 16 / (d : ℝ) + 16 / (d : ℝ) := by ring
  simpa only [d, show 4 / ((m - p : ℕ) : ℝ) +
      16 / ((m - p : ℕ) : ℝ) + 16 / ((m - p : ℕ) : ℝ) =
      36 / ((m - p : ℕ) : ℝ) by ring] using hmain

/-- In the dilute half `2p ≤ m`, the analytic scale is at least a
constant multiple of `sqrt(p(p-1))`, giving a `1/p` skewness bound. -/
theorem nullLambdaSeries_le_twelve_div_sqrt_ppred_of_two_mul_le
    {m p : ℕ} (h : Admissible m p) (hhalf : 2 * p ≤ m) :
    nullLambdaSeries m p ≤
      12 / Real.sqrt ((p : ℝ) * ((p : ℝ) - 1)) := by
  let q : ℝ := ((m - p + 1 : ℕ) : ℝ)
  let P : ℝ := (p : ℝ) * ((p : ℝ) - 1)
  have hp2 : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hm : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hP : 0 < P := by
    dsimp [P]
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    exact mul_pos (by linarith) (by linarith)
  have hq : 0 < q := by dsimp [q]; positivity
  have hqm : (m : ℝ) / 2 ≤ q := by
    dsimp [q]
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hpm]
    have hhR : (2 : ℝ) * (p : ℝ) ≤ (m : ℝ) := by exact_mod_cast hhalf
    linarith
  have hratio : (1 / 16 : ℝ) ≤ q ^ 2 / (4 * (m : ℝ) ^ 2) := by
    have hsq : (m : ℝ) ^ 2 ≤ 4 * q ^ 2 := by
      nlinarith [sq_nonneg (q - (m : ℝ) / 2)]
    field_simp [hm.ne']
    nlinarith
  have hV := nullVSeries_lower_p_mul_pred_div_m_sq h
  have hV' : P / (m : ℝ) ^ 2 ≤ nullVSeries m p := by
    simpa only [P] using hV
  have hDeltaSq : P / 16 ≤ (nullAnalyticScale m p) ^ 2 := by
    rw [nullAnalyticScale_sq_eq_residual_sq_mul_V h]
    change P / 16 ≤ (q ^ 2 / 4) * nullVSeries m p
    have hfirst : P / 16 ≤ (q ^ 2 / 4) * (P / (m : ℝ) ^ 2) := by
      have hmul := mul_le_mul_of_nonneg_left hratio hP.le
      calc
        P / 16 = P * (1 / 16) := by ring
        _ ≤ P * (q ^ 2 / (4 * (m : ℝ) ^ 2)) := hmul
        _ = (q ^ 2 / 4) * (P / (m : ℝ) ^ 2) := by ring
    exact hfirst.trans (mul_le_mul_of_nonneg_left hV' (by positivity))
  have hsqrtP : 0 < Real.sqrt P := Real.sqrt_pos.2 hP
  have hDelta : 0 < nullAnalyticScale m p := nullAnalyticScale_pos h
  have hDeltaLower : Real.sqrt P / 4 ≤ nullAnalyticScale m p := by
    have hsqrtSq := Real.sq_sqrt hP.le
    nlinarith [sq_nonneg (nullAnalyticScale m p + Real.sqrt P / 4)]
  have hfrac : 3 / nullAnalyticScale m p ≤ 12 / Real.sqrt P := by
    apply (div_le_div_iff₀ hDelta hsqrtP).2
    nlinarith
  exact (nullLambdaSeries_le_three_div_analyticScale h).trans (by simpa [P] using hfrac)

/-- On the dense side, if the gap is larger than `sqrt p`, the variance is
bounded below by a constant and the exact skewness is `O(p^(-1/2))`. -/
theorem nullLambdaSeries_le_2304_div_sqrt_p_of_dense_largeGap
    {m p : ℕ} (h : Admissible m p) (hd : 1 ≤ m - p)
    (hdense : m < 2 * p) (hlarge : p < (m - p) ^ 2) :
    nullLambdaSeries m p ≤ 2304 / Real.sqrt (p : ℝ) := by
  let d : ℕ := m - p
  let P : ℝ := (p : ℝ) * ((p : ℝ) - 1)
  have hp2 : 2 ≤ p := h.1
  have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr (by omega)
  have hm : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hdR : 0 < (d : ℝ) := by
    have : 0 < d := by dsimp [d]; omega
    exact_mod_cast this
  have hP : 0 < P := by
    dsimp [P]
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    exact mul_pos (by linarith) (by linarith)
  have hmDense : (m : ℝ) < 2 * (p : ℝ) := by exact_mod_cast hdense
  have hmSq : (m : ℝ) ^ 2 ≤ 4 * (p : ℝ) ^ 2 := by nlinarith
  have hpSq : (p : ℝ) ^ 2 ≤ 2 * P := by
    dsimp [P]
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    nlinarith
  have hratio : (1 / 16 : ℝ) ≤ P / (m : ℝ) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hm)).2
    nlinarith
  have hVlower : (1 / 16 : ℝ) ≤ nullVSeries m p :=
    hratio.trans (by simpa only [P] using nullVSeries_lower_p_mul_pred_div_m_sq h)
  have hVpos : 0 < nullVSeries m p := nullVSeries_pos h
  have hsqrtV : (1 / 4 : ℝ) ≤ Real.sqrt (nullVSeries m p) := by
    have hs := Real.sq_sqrt hVpos.le
    nlinarith [Real.sqrt_nonneg (nullVSeries m p)]
  have hden : (1 / 64 : ℝ) ≤
      (Real.sqrt (nullVSeries m p)) ^ (3 : ℕ) := by
    nlinarith [Real.sqrt_nonneg (nullVSeries m p),
      sq_nonneg (Real.sqrt (nullVSeries m p) - 1 / 4)]
  have hA := nullASeries_le_thirtySix_div_gap h hd
  have hlambdaGap : nullLambdaSeries m p ≤ 2304 / (d : ℝ) := by
    rw [nullLambdaSeries_eq, nullVSeries_rpow_three_halves h]
    have hdenPos : 0 < (Real.sqrt (nullVSeries m p)) ^ (3 : ℕ) := by positivity
    calc
      nullASeries m p / (Real.sqrt (nullVSeries m p)) ^ (3 : ℕ) ≤
          (36 / (d : ℝ)) /
            (Real.sqrt (nullVSeries m p)) ^ (3 : ℕ) :=
        div_le_div_of_nonneg_right (by simpa only [d] using hA) hdenPos.le
      _ ≤ (36 / (d : ℝ)) / (1 / 64 : ℝ) := by
        exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
      _ = 2304 / (d : ℝ) := by ring
  have hlargeR : (p : ℝ) < (d : ℝ) ^ 2 := by
    exact_mod_cast (by simpa only [d] using hlarge)
  have hsqrtp : Real.sqrt (p : ℝ) < (d : ℝ) := by
    have hs := Real.sq_sqrt hp.le
    nlinarith [Real.sqrt_nonneg (p : ℝ)]
  exact hlambdaGap.trans (by
    exact div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 hp)
      hsqrtp.le)

/-- In the dense near-hard-edge case `d^2 ≤ p`, the logarithmic variance
lower bound cancels the sharp `(log p)^(3/2)` normalization, leaving `O(1/d)`.
-/
theorem scaled_nullLambdaSeries_le_648_div_gap_of_dense_smallGap
    {m p : ℕ} (h : Admissible m p) (hd : 1 ≤ m - p)
    (hdense : m < 2 * p) (hsmall : (m - p) ^ 2 ≤ p)
    (hlog : (6 : ℝ) ≤ Real.log (p : ℝ)) :
    Real.log (p : ℝ) ^ (3 / 2 : ℝ) * nullLambdaSeries m p ≤
      648 / ((m - p : ℕ) : ℝ) := by
  let d : ℕ := m - p
  let q : ℝ := ((d + 1 : ℕ) : ℝ)
  let pr : ℝ := (p : ℝ)
  let mr : ℝ := (m : ℝ)
  let L : ℝ := Real.log pr
  have hp2 : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hdN : 1 ≤ d := by simpa only [d] using hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hp : 0 < pr := by dsimp [pr]; positivity
  have hm : 0 < mr := by
    dsimp [mr]
    exact_mod_cast (show 0 < m by omega)
  have hq : 0 < q := by dsimp [q]; positivity
  have hL : 0 < L := by dsimp [L, pr]; linarith
  have hqLe : q ^ 2 ≤ 4 * pr := by
    have hqNat : d + 1 ≤ 2 * d := by omega
    have hqR : q ≤ 2 * (d : ℝ) := by
      dsimp [q]
      exact_mod_cast hqNat
    have hsmallR : (d : ℝ) ^ 2 ≤ pr := by
      dsimp [pr]
      exact_mod_cast (by simpa only [d] using hsmall)
    nlinarith [sq_nonneg (q - 2 * (d : ℝ))]
  have hpmR : pr ≤ mr := by dsimp [pr, mr]; exact_mod_cast hpm
  have hratioSq : pr / 4 ≤ (mr / q) ^ 2 := by
    rw [div_pow]
    apply (le_div_iff₀ (sq_pos_of_pos hq)).2
    have hmul := mul_le_mul_of_nonneg_left hqLe hp.le
    nlinarith [sq_nonneg (mr - pr)]
  have hratioPos : 0 < mr / q := div_pos hm hq
  have hlogRatio : L - 3 ≤ 2 * Real.log (mr / q) := by
    have hpFour : 0 < pr / 4 := by positivity
    have hmono :=
      (Real.strictMonoOn_log.le_iff_le hpFour (sq_pos_of_pos hratioPos)).2 hratioSq
    rw [Real.log_div hp.ne' (by norm_num : (4 : ℝ) ≠ 0), Real.log_pow] at hmono
    norm_num at hmono
    have hlog4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    dsimp [L]
    linarith
  have hfrac : (pr - 1) / mr ≤ 1 := by
    apply (div_le_one hm).2
    linarith
  have hVlog := nullVSeries_log_lower h
  have hVlower : L / 6 ≤ nullVSeries m p := by
    have hbase : L - 5 ≤ nullVSeries m p := by
      have hVlog' : 2 * (Real.log (mr / q) - (pr - 1) / mr) ≤
          nullVSeries m p := by
        simpa [mr, pr, q, d] using hVlog
      linarith
    linarith
  have hVpos : 0 < nullVSeries m p := nullVSeries_pos h
  have hsqrtL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hsqrtV : Real.sqrt L / 3 ≤ Real.sqrt (nullVSeries m p) := by
    have hsqL := Real.sq_sqrt hL.le
    have hsqV := Real.sq_sqrt hVpos.le
    nlinarith [Real.sqrt_nonneg (nullVSeries m p), Real.sqrt_nonneg L]
  have hden : (L * Real.sqrt L) / 18 ≤
      nullVSeries m p ^ (3 / 2 : ℝ) := by
    rw [rpow_three_halves_eq_mul_sqrt hVpos]
    have hmul := mul_le_mul hVlower hsqrtV (by positivity) hVpos.le
    nlinarith
  have hA := nullASeries_le_thirtySix_div_gap h hd
  rw [nullLambdaSeries_eq, rpow_three_halves_eq_mul_sqrt hL]
  have hdenPos : 0 < nullVSeries m p ^ (3 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hVpos _
  have hsmallDen : 0 < (L * Real.sqrt L) / 18 := by positivity
  calc
    L * Real.sqrt L *
        (nullASeries m p / nullVSeries m p ^ (3 / 2 : ℝ)) ≤
      L * Real.sqrt L *
        ((36 / (d : ℝ)) / nullVSeries m p ^ (3 / 2 : ℝ)) := by
        gcongr
    _ ≤ L * Real.sqrt L * ((36 / (d : ℝ)) /
        ((L * Real.sqrt L) / 18)) := by
      gcongr
    _ = 648 / (d : ℝ) := by field_simp [hdR.ne', hL.ne', hsqrtL.ne']; ring
    _ = 648 / ((m - p : ℕ) : ℝ) := by rfl

/-- A single finite envelope covering the three cases used in the
divergent-gap exclusion. -/
theorem scaled_nullLambdaSeries_le_growingGap_envelope
    {m p : ℕ} (h : Admissible m p) (hd : 1 ≤ m - p)
    (hlog : (6 : ℝ) ≤ Real.log (p : ℝ)) :
    Real.log (p : ℝ) ^ (3 / 2 : ℝ) * nullLambdaSeries m p ≤
      2304 * (Real.log (p : ℝ) ^ (3 / 2 : ℝ) /
        Real.sqrt (p : ℝ)) + 648 / ((m - p : ℕ) : ℝ) := by
  have hpN : 0 < p := by
    have hp2 := h.1
    omega
  have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr hpN
  have hdN : 0 < m - p := lt_of_lt_of_le Nat.zero_lt_one hd
  have hdR : 0 < ((m - p : ℕ) : ℝ) := Nat.cast_pos.mpr hdN
  have hlogNonneg : 0 ≤ Real.log (p : ℝ) := by linarith
  have hscale : 0 ≤ Real.log (p : ℝ) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg hlogNonneg _
  have hgapTerm : 0 ≤ 648 / ((m - p : ℕ) : ℝ) :=
    div_nonneg (by norm_num) hdR.le
  by_cases hdilute : 2 * p ≤ m
  · have hlam := nullLambdaSeries_le_twelve_div_sqrt_ppred_of_two_mul_le h hdilute
    have hP : (p : ℝ) ≤ (p : ℝ) * ((p : ℝ) - 1) := by
      have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h.1
      nlinarith
    have hsqrt : Real.sqrt (p : ℝ) ≤
        Real.sqrt ((p : ℝ) * ((p : ℝ) - 1)) := Real.sqrt_le_sqrt hP
    have hdenP : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 hp
    have hfrac : 12 / Real.sqrt ((p : ℝ) * ((p : ℝ) - 1)) ≤
        2304 / Real.sqrt (p : ℝ) := by
      calc
        12 / Real.sqrt ((p : ℝ) * ((p : ℝ) - 1)) ≤
            12 / Real.sqrt (p : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) hdenP hsqrt
        _ ≤ 2304 / Real.sqrt (p : ℝ) :=
          div_le_div_of_nonneg_right (by norm_num) hdenP.le
    calc
      Real.log (p : ℝ) ^ (3 / 2 : ℝ) * nullLambdaSeries m p ≤
          Real.log (p : ℝ) ^ (3 / 2 : ℝ) *
            (12 / Real.sqrt ((p : ℝ) * ((p : ℝ) - 1))) :=
        mul_le_mul_of_nonneg_left hlam hscale
      _ ≤ Real.log (p : ℝ) ^ (3 / 2 : ℝ) *
            (2304 / Real.sqrt (p : ℝ)) :=
        mul_le_mul_of_nonneg_left hfrac hscale
      _ = 2304 * (Real.log (p : ℝ) ^ (3 / 2 : ℝ) /
          Real.sqrt (p : ℝ)) := by ring
      _ ≤ _ := le_add_of_nonneg_right hgapTerm
  · have hdense : m < 2 * p := by omega
    by_cases hsmall : (m - p) ^ 2 ≤ p
    · calc
        Real.log (p : ℝ) ^ (3 / 2 : ℝ) * nullLambdaSeries m p ≤
            648 / ((m - p : ℕ) : ℝ) :=
          scaled_nullLambdaSeries_le_648_div_gap_of_dense_smallGap
            h hd hdense hsmall hlog
        _ ≤ 2304 * (Real.log (p : ℝ) ^ (3 / 2 : ℝ) /
              Real.sqrt (p : ℝ)) + 648 / ((m - p : ℕ) : ℝ) :=
          le_add_of_nonneg_left (mul_nonneg (by norm_num)
            (div_nonneg hscale (Real.sqrt_nonneg _)))
    · have hlarge : p < (m - p) ^ 2 := by omega
      have hlam := nullLambdaSeries_le_2304_div_sqrt_p_of_dense_largeGap
        h hd hdense hlarge
      calc
        Real.log (p : ℝ) ^ (3 / 2 : ℝ) * nullLambdaSeries m p ≤
            Real.log (p : ℝ) ^ (3 / 2 : ℝ) *
              (2304 / Real.sqrt (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hlam hscale
        _ = 2304 * (Real.log (p : ℝ) ^ (3 / 2 : ℝ) /
            Real.sqrt (p : ℝ)) := by ring
        _ ≤ _ := le_add_of_nonneg_right hgapTerm

/-- Divergent-gap exclusion in the exact two-sequence form used by the sharp
supremum theorem. -/
theorem tendsto_growingGap_nullLambda_logPow
    {mseq pseq : ℕ → ℕ}
    (hp : Tendsto pseq atTop atTop)
    (hadm : ∀ᶠ n in atTop, Admissible (mseq n) (pseq n))
    (hgap : Tendsto (fun n ↦ mseq n - pseq n) atTop atTop) :
    Tendsto (fun n ↦ Real.log (pseq n : ℝ) ^ (3 / 2 : ℝ) *
      nullLambdaSeries (mseq n) (pseq n)) atTop (nhds 0) := by
  have hpR : Tendsto (fun n ↦ (pseq n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hp
  have hlogSqrtReal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ (3 / 2 : ℝ) / Real.sqrt x)
      atTop (nhds 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop (3 / 2 : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hfirst : Tendsto (fun n ↦
      2304 * (Real.log (pseq n : ℝ) ^ (3 / 2 : ℝ) /
        Real.sqrt (pseq n : ℝ))) atTop (nhds 0) := by
    simpa using (hlogSqrtReal.comp hpR).const_mul 2304
  have hgapR : Tendsto (fun n ↦ ((mseq n - pseq n : ℕ) : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hgap
  have hsecond : Tendsto (fun n ↦
      648 / ((mseq n - pseq n : ℕ) : ℝ)) atTop (nhds 0) :=
    hgapR.const_div_atTop 648
  have henvelope := hfirst.add hsecond
  apply squeeze_zero'
  · exact hadm.mono fun n hn ↦ by
      have hpOne : 1 ≤ pseq n := le_trans (by norm_num) hn.1
      have hplog : 0 ≤ Real.log (pseq n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hpOne)
      exact mul_nonneg (Real.rpow_nonneg hplog _) (nullLambdaSeries_pos hn).le
  · have hlog : Tendsto (fun n ↦ Real.log (pseq n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp hpR
    filter_upwards [hadm, hgap.eventually (eventually_ge_atTop 1),
      hlog.eventually (eventually_ge_atTop 6)] with n hn hdN hlogN
    exact scaled_nullLambdaSeries_le_growingGap_envelope hn hdN hlogN
  · simpa using henvelope

/-- Strictly increasing dimension specialization, matching the interface of
the constrained-supremum assembly. -/
theorem tendsto_growingGap_nullLambda_logPow_of_strictMono
    {mseq pseq : ℕ → ℕ} (hp : StrictMono pseq)
    (hadm : ∀ᶠ n in atTop, Admissible (mseq n) (pseq n))
    (hgap : Tendsto (fun n ↦ mseq n - pseq n) atTop atTop) :
    Tendsto (fun n ↦ Real.log (pseq n : ℝ) ^ (3 / 2 : ℝ) *
      nullLambdaSeries (mseq n) (pseq n)) atTop (nhds 0) :=
  tendsto_growingGap_nullLambda_logPow hp.tendsto_atTop hadm hgap

end

end LogdetLean
