import LogdetLean.NullRegimeAsymptotics
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
# The large-gap asymptotic of the hard-edge third-cumulant constant

For the positive hard-edge constant
`hardEdgeAConstant d = ∑_{n≥0} (-ψ₂)((d+n+1)/2)`, this module proves the
explicit finite comparison

`4/(d+1) ≤ hardEdgeAConstant d ≤ 4/d + 8/d²`

for `d ≥ 1`, and hence the kernel-checked limit
`d * hardEdgeAConstant d → 4`.

The special-function input is the positive series representation of
`-ψ₂`, obtained in `PolygammaSeries.lean` by differentiating the DLMF
trigamma series 5.15.1 term by term.  The tail comparison itself is proved
here from integral tests; it is not imported from a paper.
-/

namespace LogdetLean
open Filter Real Set MeasureTheory
open scoped Topology
noncomputable section

private theorem shifted_inv_sq_tail_upper (d : ℕ) (hd : 1 ≤ d) :
    (∑' n : ℕ, 1 / (((n + d + 1 : ℕ) : ℝ)) ^ 2) ≤ 1 / (d : ℝ) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  let f : ℝ → ℝ := fun x ↦ x ^ (-2 : ℝ)
  have hanti : AntitoneOn f (Ici (d : ℝ)) := by
    exact (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
      (by norm_num : (-2 : ℝ) ≤ 0)).mono (fun x hx ↦ hdR.trans_le hx)
  have hint : IntegrableOn f (Ioi (d : ℝ)) := by
    exact integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hdR
  have hnonneg : ∀ t ∈ Ioi (d : ℝ), 0 ≤ f t := by
    intro t ht
    exact Real.rpow_nonneg (hdR.trans ht).le _
  have hmain := hanti.tsum_comp_add_le_integral d hint hnonneg
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hdR] at hmain
  norm_num [Real.rpow_neg_one] at hmain
  simpa [f, Real.rpow_neg_natCast, add_assoc] using hmain

private theorem shifted_inv_cube_tail_upper (d : ℕ) (hd : 1 ≤ d) :
    (∑' n : ℕ, 1 / (((n + d + 1 : ℕ) : ℝ)) ^ 3) ≤
      (1 / (d : ℝ) ^ 2) / 2 := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  let f : ℝ → ℝ := fun x ↦ x ^ (-3 : ℝ)
  have hanti : AntitoneOn f (Ici (d : ℝ)) := by
    exact (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
      (by norm_num : (-3 : ℝ) ≤ 0)).mono (fun x hx ↦ hdR.trans_le hx)
  have hint : IntegrableOn f (Ioi (d : ℝ)) := by
    exact integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hdR
  have hnonneg : ∀ t ∈ Ioi (d : ℝ), 0 ≤ f t := by
    intro t ht
    exact Real.rpow_nonneg (hdR.trans ht).le _
  have hmain := hanti.tsum_comp_add_le_integral d hint hnonneg
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hdR] at hmain
  norm_num [Real.rpow_neg_natCast] at hmain
  simpa [f, Real.rpow_neg_natCast, add_assoc] using hmain

private theorem summable_shifted_inv_pow (d r : ℕ) (hr : 1 < r) :
    Summable (fun n : ℕ ↦ 1 / (((n + d + 1 : ℕ) : ℝ)) ^ r) := by
  have hbase := Real.summable_one_div_nat_pow.mpr hr
  have hshift := (summable_nat_add_iff (d + 1)).2 hbase
  simpa [add_assoc, add_comm, add_left_comm] using hshift

theorem hardEdgeAConstant_tail_bounds (d : ℕ) (hd : 1 ≤ d) :
    4 / (((d + 1 : ℕ) : ℝ)) ≤ hardEdgeAConstant d ∧
      hardEdgeAConstant d ≤ 4 / (d : ℝ) + 8 / (d : ℝ) ^ 2 := by
  have hlowSum :
      1 / (((d + 1 : ℕ) : ℝ)) ≤
        ∑' n : ℕ, 1 / (((n + d + 1 : ℕ) : ℝ)) ^ 2 := by
    exact (by
      have hd1R : 0 < ((d + 1 : ℕ) : ℝ) := by positivity
      let f : ℝ → ℝ := fun x ↦ x ^ (-2 : ℝ)
      have hanti : AntitoneOn f (Ici ((d + 1 : ℕ) : ℝ)) := by
        exact (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
          (by norm_num : (-2 : ℝ) ≤ 0)).mono (fun x hx ↦ hd1R.trans_le hx)
      have hsummable : Summable (fun n : ℕ ↦ f n) := by
        exact Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)
      have hnonneg : ∀ t ∈ Ioi (((d + 1 : ℕ) : ℝ)), 0 ≤ f t := by
        intro t ht
        exact Real.rpow_nonneg (hd1R.trans ht).le _
      have hmain := hanti.integral_le_tsum_comp_add (d + 1) hsummable hnonneg
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hd1R] at hmain
      norm_num [Real.rpow_neg_one] at hmain
      simpa [f, Real.rpow_neg_natCast, add_assoc] using hmain)
  have hupp2 :
      (∑' n : ℕ, 1 / (((n + d + 1 : ℕ) : ℝ)) ^ 2) ≤ 1 / (d : ℝ) := by
    exact (by
      have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
      let f : ℝ → ℝ := fun x ↦ x ^ (-2 : ℝ)
      have hanti : AntitoneOn f (Ici (d : ℝ)) := by
        exact (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
          (by norm_num : (-2 : ℝ) ≤ 0)).mono (fun x hx ↦ hdR.trans_le hx)
      have hint : IntegrableOn f (Ioi (d : ℝ)) := by
        exact integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hdR
      have hnonneg : ∀ t ∈ Ioi (d : ℝ), 0 ≤ f t := by
        intro t ht
        exact Real.rpow_nonneg (hdR.trans ht).le _
      have hmain := hanti.tsum_comp_add_le_integral d hint hnonneg
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hdR] at hmain
      norm_num [Real.rpow_neg_one] at hmain
      simpa [f, Real.rpow_neg_natCast, add_assoc] using hmain)
  have hupp3 :
      (∑' n : ℕ, 1 / (((n + d + 1 : ℕ) : ℝ)) ^ 3) ≤
        (1 / (d : ℝ) ^ 2) / 2 := by
    have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    let f : ℝ → ℝ := fun x ↦ x ^ (-3 : ℝ)
    have hanti : AntitoneOn f (Ici (d : ℝ)) := by
      exact (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
        (by norm_num : (-3 : ℝ) ≤ 0)).mono (fun x hx ↦ hdR.trans_le hx)
    have hint : IntegrableOn f (Ioi (d : ℝ)) := by
      exact integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hdR
    have hnonneg : ∀ t ∈ Ioi (d : ℝ), 0 ≤ f t := by
      intro t ht
      exact Real.rpow_nonneg (hdR.trans ht).le _
    have hmain := hanti.tsum_comp_add_le_integral d hint hnonneg
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hdR] at hmain
    norm_num [Real.rpow_neg_natCast] at hmain
    simpa [f, Real.rpow_neg_natCast, add_assoc] using hmain
  have hs2 := summable_shifted_inv_pow d 2 (by norm_num)
  have hs3 := summable_shifted_inv_pow d 3 (by norm_num)
  have hs2' : Summable (fun n : ℕ ↦
      4 / (((n + d + 1 : ℕ) : ℝ)) ^ 2) := by
    exact (hs2.mul_left 4).congr (fun n ↦ by ring)
  have hs3' : Summable (fun n : ℕ ↦
      16 / (((n + d + 1 : ℕ) : ℝ)) ^ 3) := by
    exact (hs3.mul_left 16).congr (fun n ↦ by ring)
  have htermLower : ∀ n : ℕ,
      4 / (((n + d + 1 : ℕ) : ℝ)) ^ 2 ≤
        negPsiTwoSeries (((d + n + 1 : ℕ) : ℝ) / 2) := by
    intro n
    have hx : 0 < (((d + n + 1 : ℕ) : ℝ) / 2) := by positivity
    have h := one_div_sq_le_negPsiTwoSeries hx
    norm_num [div_pow] at h
    simpa only [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using h
  have htermUpper : ∀ n : ℕ,
      negPsiTwoSeries (((d + n + 1 : ℕ) : ℝ) / 2) ≤
        4 / (((n + d + 1 : ℕ) : ℝ)) ^ 2 +
          16 / (((n + d + 1 : ℕ) : ℝ)) ^ 3 := by
    intro n
    have hx : 0 < (((d + n + 1 : ℕ) : ℝ) / 2) := by positivity
    have h := negPsiTwoSeries_le_one_div_sq_add_two_div_cube hx
    norm_num [div_pow] at h
    convert h using 1
    all_goals simp only [Nat.cast_add, Nat.cast_one, add_assoc]
    all_goals field_simp
    all_goals ring
  constructor
  · calc
      4 / (((d + 1 : ℕ) : ℝ)) =
          4 * (1 / (((d + 1 : ℕ) : ℝ))) := by ring
      _ ≤ 4 * (∑' n : ℕ, 1 / (((n + d + 1 : ℕ) : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left hlowSum (by norm_num)
      _ ≤ hardEdgeAConstant d := by
        unfold hardEdgeAConstant
        rw [← tsum_mul_left]
        exact (hs2.mul_left 4).tsum_le_tsum
          (fun n ↦ by simpa only [div_eq_mul_inv, one_mul] using htermLower n)
          (summable_hardEdgeA_terms d)
  · unfold hardEdgeAConstant
    calc
      (∑' n : ℕ, negPsiTwoSeries (((d + n + 1 : ℕ) : ℝ) / 2)) ≤
          ∑' n : ℕ, (4 / (((n + d + 1 : ℕ) : ℝ)) ^ 2 +
            16 / (((n + d + 1 : ℕ) : ℝ)) ^ 3) := by
              exact (summable_hardEdgeA_terms d).tsum_le_tsum htermUpper
                (hs2'.add hs3')
      _ = 4 * (∑' n : ℕ, 1 / (((n + d + 1 : ℕ) : ℝ)) ^ 2) +
          16 * (∑' n : ℕ, 1 / (((n + d + 1 : ℕ) : ℝ)) ^ 3) := by
            rw [hs2'.tsum_add hs3']
            have h2 := hs2.tsum_mul_left 4
            have h3 := hs3.tsum_mul_left 16
            rw [← h2, ← h3]
            congr 1 <;> apply tsum_congr <;> intro n <;> ring
      _ ≤ 4 * (1 / (d : ℝ)) + 16 * ((1 / (d : ℝ) ^ 2) / 2) := by gcongr
      _ = 4 / (d : ℝ) + 8 / (d : ℝ) ^ 2 := by ring

theorem tendsto_gap_mul_hardEdgeAConstant :
    Tendsto (fun d : ℕ ↦ (d : ℝ) * hardEdgeAConstant d)
    atTop (nhds 4) := by
  have hden : Tendsto (fun d : ℕ ↦ ((d : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun d : ℕ ↦ 1 / ((d : ℝ) + 1)) atTop (nhds 0) := by
    simpa [one_div] using
      (tendsto_const_nhds.div_atTop hden :
        Tendsto (fun d : ℕ ↦ (1 : ℝ) / ((d : ℝ) + 1)) atTop (nhds 0))
  have hlower : Tendsto (fun d : ℕ ↦ 4 * (1 - 1 / ((d : ℝ) + 1)))
      atTop (nhds 4) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa using (hone.sub hinv).const_mul 4
  have hdR : Tendsto (fun d : ℕ ↦ (d : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun d : ℕ ↦ 4 + 8 / (d : ℝ))
      atTop (nhds 4) := by
    simpa using tendsto_const_nhds.add (hdR.const_div_atTop 8)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_ge_atTop 1] with d hd
    have hbounds := hardEdgeAConstant_tail_bounds d hd
    have hd0 : 0 ≤ (d : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hbounds.1 hd0
    have heq :
        4 * (1 - 1 / ((d : ℝ) + 1)) =
          (d : ℝ) * (4 / (((d + 1 : ℕ) : ℝ))) := by
      push_cast
      have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hd1]
      ring
    rw [heq]
    exact hmul
  · filter_upwards [eventually_ge_atTop 1] with d hd
    have hbounds := hardEdgeAConstant_tail_bounds d hd
    have hd0 : 0 ≤ (d : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hbounds.2 hd0
    have heq :
        (d : ℝ) * (4 / (d : ℝ) + 8 / (d : ℝ) ^ 2) =
          4 + 8 / (d : ℝ) := by
      have hdne : (d : ℝ) ≠ 0 := by positivity
      field_simp [hdne]
    rw [← heq]
    exact hmul

end
end LogdetLean
