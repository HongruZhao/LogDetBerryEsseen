import LogdetLean.NullSharpSupremum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Kernel-checked decimal certificate for the sharp null constant

The sharp supremum theorem is stated first, and primarily, with the exact
symbolic constant

`(4 * π^2 / 3 + 7 * realZetaThree) / (24 * √π)`.

This file adds a numerical certificate.  No floating-point computation enters
the proof.  The value `realZetaThree` is bounded by its first ten terms and two
explicit telescoping rational tails.  Bounds for `π` are the kernel-checked
20-decimal bounds `Real.pi_gt_d20` and `Real.pi_lt_d20` from mathlib.  Rational
arithmetic then proves that the exact constant lies strictly between
`0.50715638` and `0.50715639`.
-/

namespace LogdetLean

open Filter Real
open scoped BigOperators Topology

noncomputable section

/-! ## A rapidly accurate rational enclosure for zeta at three -/

/-- The lower telescoping profile for the tail of `∑ n⁻³`.

Its successive difference is at most `x⁻³`. -/
private def zetaThreeTailLowerProfile (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (1 / x ^ 2) +
    (1 / 2 : ℝ) * (1 / x ^ 3) +
    (1 / 4 : ℝ) * (1 / x ^ 4) -
    (1 / 12 : ℝ) * (1 / x ^ 6)

/-- The upper telescoping profile for the tail of `∑ n⁻³`.

It differs from the lower profile by only `1 / (12 x⁸)`. -/
private def zetaThreeTailUpperProfile (x : ℝ) : ℝ :=
  zetaThreeTailLowerProfile x +
    (1 / 12 : ℝ) * (1 / x ^ 8)

private theorem zetaThreeTailLowerProfile_step_le {x : ℝ} (hx : 0 < x) :
    zetaThreeTailLowerProfile x - zetaThreeTailLowerProfile (x + 1) ≤
      1 / x ^ 3 := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hx10 : x + 1 ≠ 0 := by linarith
  apply sub_nonpos.mp
  have hid :
      (zetaThreeTailLowerProfile x - zetaThreeTailLowerProfile (x + 1)) -
          1 / x ^ 3 =
        -((2 * x + 1) ^ 3) /
          (12 * x ^ 6 * (x + 1) ^ 6) := by
    unfold zetaThreeTailLowerProfile
    field_simp [hx0, hx10]
    <;> ring
  rw [hid]
  have hnum : 0 ≤ (2 * x + 1) ^ 3 :=
    pow_nonneg (by linarith : 0 ≤ 2 * x + 1) 3
  have hden : 0 ≤ 12 * x ^ 6 * (x + 1) ^ 6 := by positivity
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hnum) hden

private theorem zetaThreeTailUpperProfile_step_ge {x : ℝ} (hx : 0 < x) :
    1 / x ^ 3 ≤
      zetaThreeTailUpperProfile x - zetaThreeTailUpperProfile (x + 1) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hx10 : x + 1 ≠ 0 := by linarith
  apply sub_nonneg.mp
  have hid :
      (zetaThreeTailUpperProfile x - zetaThreeTailUpperProfile (x + 1)) -
          1 / x ^ 3 =
        (2 * x + 1) * (3 * x ^ 2 + 3 * x + 1) ^ 2 /
          (12 * x ^ 8 * (x + 1) ^ 8) := by
    unfold zetaThreeTailUpperProfile zetaThreeTailLowerProfile
    field_simp [hx0, hx10]
    <;> ring
  rw [hid]
  exact div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by positivity)

private theorem summable_shifted_inv_nat_pow (N q : ℕ) (hq : 1 < q) :
    Summable (fun k : ℕ ↦ 1 / ((((k + N : ℕ) : ℝ)) ^ q)) := by
  have hbase : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) ^ q)) :=
    Real.summable_one_div_nat_pow.mpr hq
  simpa only [Nat.cast_add] using (summable_nat_add_iff N).2 hbase

private theorem summable_zetaThreeTailLowerProfile_ten :
    Summable (fun k : ℕ ↦
      zetaThreeTailLowerProfile (((k + 10 : ℕ) : ℝ))) := by
  have h2 := summable_shifted_inv_nat_pow 10 2 (by norm_num)
  have h3 := summable_shifted_inv_nat_pow 10 3 (by norm_num)
  have h4 := summable_shifted_inv_nat_pow 10 4 (by norm_num)
  have h6 := summable_shifted_inv_nat_pow 10 6 (by norm_num)
  have h := (((h2.mul_left (1 / 2 : ℝ)).add
    (h3.mul_left (1 / 2 : ℝ))).add
    (h4.mul_left (1 / 4 : ℝ))).sub
    (h6.mul_left (1 / 12 : ℝ))
  exact h.congr fun k ↦ by
    unfold zetaThreeTailLowerProfile
    ring

private theorem summable_zetaThreeTailUpperProfile_ten :
    Summable (fun k : ℕ ↦
      zetaThreeTailUpperProfile (((k + 10 : ℕ) : ℝ))) := by
  have h8 := summable_shifted_inv_nat_pow 10 8 (by norm_num)
  exact summable_zetaThreeTailLowerProfile_ten.add
    ((h8.mul_left (1 / 12 : ℝ)).congr fun k ↦ by
      ring)

/-- Any summable sequence telescopes after taking its forward difference. -/
private theorem hasSum_forwardDifference (F : ℕ → ℝ) (hF : Summable F) :
    HasSum (fun k : ℕ ↦ F k - F (k + 1)) (F 0) := by
  have hshift : Summable (fun k : ℕ ↦ F (k + 1)) :=
    hF.comp_injective (fun _ _ h ↦ Nat.add_right_cancel h)
  have hsplit := hF.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hsplit
  have htsum :
      (∑' k : ℕ, (F k - F (k + 1))) = F 0 := by
    rw [hF.tsum_sub hshift]
    linarith
  rw [← htsum]
  exact (hF.sub hshift).hasSum

private theorem summable_realZetaThree_terms :
    Summable (fun n : ℕ ↦ 1 / ((n : ℝ) ^ 3)) :=
  Real.summable_one_div_nat_pow.mpr (by norm_num)

/-- Exact rational tail enclosure after the first ten terms. -/
theorem realZetaThree_tail_ten_bounds :
    (∑ n ∈ Finset.range 10, 1 / ((n : ℝ) ^ 3)) +
        zetaThreeTailLowerProfile 10 ≤ realZetaThree ∧
      realZetaThree ≤
        (∑ n ∈ Finset.range 10, 1 / ((n : ℝ) ^ 3)) +
          zetaThreeTailUpperProfile 10 := by
  let f : ℕ → ℝ := fun k ↦ 1 / ((((k + 10 : ℕ) : ℝ)) ^ 3)
  let lowerF : ℕ → ℝ := fun k ↦
    zetaThreeTailLowerProfile (((k + 10 : ℕ) : ℝ))
  let upperF : ℕ → ℝ := fun k ↦
    zetaThreeTailUpperProfile (((k + 10 : ℕ) : ℝ))
  have hf : Summable f := summable_shifted_inv_nat_pow 10 3 (by norm_num)
  have hlower : Summable lowerF := by
    simpa only [lowerF] using summable_zetaThreeTailLowerProfile_ten
  have hupper : Summable upperF := by
    simpa only [upperF] using summable_zetaThreeTailUpperProfile_ten
  have hlowerTel := hasSum_forwardDifference lowerF hlower
  have hupperTel := hasSum_forwardDifference upperF hupper
  have hlowerTail : lowerF 0 ≤ ∑' k : ℕ, f k := by
    calc
      lowerF 0 = ∑' k : ℕ, (lowerF k - lowerF (k + 1)) :=
        hlowerTel.tsum_eq.symm
      _ ≤ ∑' k : ℕ, f k :=
        hlowerTel.summable.tsum_le_tsum (fun k ↦ by
          have hx : 0 < ((((k + 10 : ℕ) : ℝ))) := by positivity
          simpa only [lowerF, f, Nat.cast_add, Nat.cast_one,
            add_assoc, add_comm, add_left_comm] using
            zetaThreeTailLowerProfile_step_le (x := (((k + 10 : ℕ) : ℝ))) hx)
          hf
  have hupperTail : (∑' k : ℕ, f k) ≤ upperF 0 := by
    calc
      (∑' k : ℕ, f k) ≤
          ∑' k : ℕ, (upperF k - upperF (k + 1)) :=
        hf.tsum_le_tsum (fun k ↦ by
          have hx : 0 < ((((k + 10 : ℕ) : ℝ))) := by positivity
          simpa only [upperF, f, Nat.cast_add, Nat.cast_one,
            add_assoc, add_comm, add_left_comm] using
            zetaThreeTailUpperProfile_step_ge (x := (((k + 10 : ℕ) : ℝ))) hx)
          hupperTel.summable
      _ = upperF 0 := hupperTel.tsum_eq
  have hsplit := summable_realZetaThree_terms.sum_add_tsum_nat_add 10
  have hsplit' :
      (∑ n ∈ Finset.range 10, 1 / ((n : ℝ) ^ 3)) +
          (∑' k : ℕ, f k) = realZetaThree := by
    simpa only [f, realZetaThree, Nat.cast_add] using hsplit
  constructor
  · rw [← hsplit']
    dsimp only [lowerF] at hlowerTail
    norm_num only [Nat.cast_ofNat] at hlowerTail
    linarith
  · rw [← hsplit']
    dsimp only [upperF] at hupperTail
    norm_num only [Nat.cast_ofNat] at hupperTail
    linarith

/-- Eight-decimal lower certificate for the defining zeta-three series. -/
theorem realZetaThree_gt_decimal8 :
    (120205690 : ℝ) / 100000000 < realZetaThree := by
  have htail := realZetaThree_tail_ten_bounds.1
  have hnum :
      (120205690 : ℝ) / 100000000 <
        (∑ n ∈ Finset.range 10, 1 / ((n : ℝ) ^ 3)) +
          zetaThreeTailLowerProfile 10 := by
    norm_num [zetaThreeTailLowerProfile]
  exact hnum.trans_le htail

/-- Eight-decimal upper certificate for the defining zeta-three series. -/
theorem realZetaThree_lt_decimal8 :
    realZetaThree < (120205691 : ℝ) / 100000000 := by
  have htail := realZetaThree_tail_ten_bounds.2
  have hnum :
      (∑ n ∈ Finset.range 10, 1 / ((n : ℝ) ^ 3)) +
          zetaThreeTailUpperProfile 10 <
        (120205691 : ℝ) / 100000000 := by
    norm_num [zetaThreeTailUpperProfile, zetaThreeTailLowerProfile]
  exact htail.trans_lt hnum

/-! ## Rational bounds for `√π` -/

private theorem sqrt_pi_gt_decimal8 :
    (177245385 : ℝ) / 100000000 < Real.sqrt Real.pi := by
  have hsquare : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
    Real.sq_sqrt (le_of_lt Real.pi_pos)
  have hrat :
      ((177245385 : ℝ) / 100000000) ^ 2 <
        (314159265358979323846 : ℝ) / 100000000000000000000 := by
    norm_num
  have hsqrt := Real.sqrt_nonneg Real.pi
  nlinarith [Real.pi_gt_d20]

private theorem sqrt_pi_lt_decimal8 :
    Real.sqrt Real.pi < (177245386 : ℝ) / 100000000 := by
  have hsquare : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
    Real.sq_sqrt (le_of_lt Real.pi_pos)
  have hrat :
      (314159265358979323847 : ℝ) / 100000000000000000000 <
        ((177245386 : ℝ) / 100000000) ^ 2 := by
    norm_num
  have hsqrt := Real.sqrt_nonneg Real.pi
  nlinarith [Real.pi_lt_d20]

/-! ## The certified decimal interval -/

/-- Kernel-checked lower endpoint for the sharp constrained constant. -/
theorem nullSharpSupremumConstant_gt_decimal8 :
    (50715638 : ℝ) / 100000000 < nullSharpSupremumConstant := by
  rw [nullSharpSupremumConstant_eq_closed]
  unfold squareAConstant
  have hsqrtPos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  rw [lt_div_iff₀ (mul_pos (by norm_num) hsqrtPos)]
  have hpiSq :
      ((314159265358979323846 : ℝ) / 100000000000000000000) ^ 2 <
        Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_d20, Real.pi_pos]
  calc
    (50715638 / 100000000 : ℝ) * (24 * Real.sqrt Real.pi) <
        (50715638 / 100000000 : ℝ) *
          (24 * ((177245386 : ℝ) / 100000000)) := by
      gcongr
      exact sqrt_pi_lt_decimal8
    _ < 4 *
          (((314159265358979323846 : ℝ) /
            100000000000000000000) ^ 2) / 3 +
          7 * ((120205690 : ℝ) / 100000000) := by
      norm_num
    _ < 4 * Real.pi ^ 2 / 3 + 7 * realZetaThree := by
      nlinarith [realZetaThree_gt_decimal8]

/-- Kernel-checked upper endpoint for the sharp constrained constant. -/
theorem nullSharpSupremumConstant_lt_decimal8 :
    nullSharpSupremumConstant < (50715639 : ℝ) / 100000000 := by
  rw [nullSharpSupremumConstant_eq_closed]
  unfold squareAConstant
  have hsqrtPos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  rw [div_lt_iff₀ (mul_pos (by norm_num) hsqrtPos)]
  have hpiSq :
      Real.pi ^ 2 <
        ((314159265358979323847 : ℝ) / 100000000000000000000) ^ 2 := by
    nlinarith [Real.pi_lt_d20, Real.pi_pos]
  calc
    4 * Real.pi ^ 2 / 3 + 7 * realZetaThree <
        4 *
          (((314159265358979323847 : ℝ) /
            100000000000000000000) ^ 2) / 3 +
          7 * ((120205691 : ℝ) / 100000000) := by
      nlinarith [realZetaThree_lt_decimal8]
    _ < (50715639 / 100000000 : ℝ) *
          (24 * ((177245385 : ℝ) / 100000000)) := by
      norm_num
    _ < (50715639 / 100000000 : ℝ) *
          (24 * Real.sqrt Real.pi) := by
      gcongr
      exact sqrt_pi_gt_decimal8

/-- The exact sharp constant lies in a rational interval of width `10⁻⁸`.
This formally certifies the displayed decimal `0.50715638…`, and hence also
the shorter notation `0.507156…`. -/
theorem nullSharpSupremumConstant_decimal8 :
    (50715638 : ℝ) / 100000000 < nullSharpSupremumConstant ∧
      nullSharpSupremumConstant < (50715639 : ℝ) / 100000000 :=
  ⟨nullSharpSupremumConstant_gt_decimal8,
    nullSharpSupremumConstant_lt_decimal8⟩

end

end LogdetLean
