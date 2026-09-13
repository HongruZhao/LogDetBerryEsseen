import LogdetLean.NullRegimeAsymptotics
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

/-!
# Evaluation of the square hard-edge constant

The square third-cumulant constant is evaluated from its defining positive
double series.  The proof groups pairs of natural indices along finite
antidiagonals and then splits the zeta series into its even and odd parts.
-/

namespace LogdetLean

open Filter Real Set
open scoped BigOperators Topology

noncomputable section

/-- Group an absolutely summable nonnegative kernel depending only on
`a+b` along the finite antidiagonals of `ℕ×ℕ`. -/
private theorem tsum_tsum_nat_add_eq
    (f : ℕ → ℝ) (hf0 : ∀ n, 0 ≤ f n)
    (hs : Summable (fun n : ℕ ↦ (n + 1 : ℝ) * f n)) :
    (∑' a : ℕ, ∑' b : ℕ, f (a + b)) =
      ∑' n : ℕ, (n + 1 : ℝ) * f n := by
  let F : (Σ n : ℕ, ↑(Finset.antidiagonal n)) → ℝ := fun z ↦ f z.1
  have hF0 : ∀ z, 0 ≤ F z := fun z ↦ hf0 z.1
  have hfiber (n : ℕ) : Summable (fun z : ↑(Finset.antidiagonal n) ↦ F ⟨n, z⟩) :=
    Summable.of_finite
  have hfiberSum (n : ℕ) :
      (∑' z : ↑(Finset.antidiagonal n), F ⟨n, z⟩) =
        (n + 1 : ℝ) * f n := by
    rw [tsum_fintype]
    simp [F, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
  have hF : Summable F := by
    apply (summable_sigma_of_nonneg hF0).2
    refine ⟨hfiber, ?_⟩
    simpa only [hfiberSum] using hs
  let e : (Σ n : ℕ, ↑(Finset.antidiagonal n)) ≃ ℕ × ℕ :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd
  have hprod : Summable (fun z : ℕ × ℕ ↦ f (z.1 + z.2)) := by
    rw [← e.summable_iff]
    convert hF using 1
    funext z
    dsimp [e, F]
    exact congrArg f (Finset.mem_antidiagonal.mp z.2.property)
  calc
    (∑' a : ℕ, ∑' b : ℕ, f (a + b)) =
        ∑' z : ℕ × ℕ, f (z.1 + z.2) :=
      (hprod.tsum_prod' fun a ↦
        (hprod.comp_injective (fun {_x _y} h ↦ congrArg Prod.snd h))).symm
    _ = ∑' z : (Σ n : ℕ, ↑(Finset.antidiagonal n)),
          f ((e z).1 + (e z).2) := (e.tsum_eq _).symm
    _ = ∑' z : (Σ n : ℕ, ↑(Finset.antidiagonal n)), F z := by
      apply tsum_congr
      intro z
      dsimp [e, F]
      exact congrArg f (Finset.mem_antidiagonal.mp z.2.property)
    _ = ∑' n : ℕ, ∑' z : ↑(Finset.antidiagonal n), F ⟨n, z⟩ := by
      exact hF.tsum_sigma' hfiber
    _ = ∑' n : ℕ, (n + 1 : ℝ) * f n := by
      apply tsum_congr
      exact hfiberSum

private theorem even_inv_sq_tsum :
    (∑' n : ℕ, 1 / (((2 * n : ℕ) : ℝ) ^ 2)) =
      (1 / 4 : ℝ) * (Real.pi ^ 2 / 6) := by
  calc
    (∑' n : ℕ, 1 / (((2 * n : ℕ) : ℝ) ^ 2)) =
        ∑' n : ℕ, (1 / 4 : ℝ) * (1 / ((n : ℝ) ^ 2)) := by
      apply tsum_congr
      intro n
      push_cast
      rw [mul_pow]
      norm_num
      ring
    _ = (1 / 4 : ℝ) * ∑' n : ℕ, 1 / ((n : ℝ) ^ 2) := by
      rw [tsum_mul_left]
    _ = (1 / 4 : ℝ) * (Real.pi ^ 2 / 6) := by
      rw [hasSum_zeta_two.tsum_eq]

set_option maxHeartbeats 800000 in
private theorem odd_inv_sq_tsum :
    (∑' n : ℕ, 1 / (((2 * n + 1 : ℕ) : ℝ) ^ 2)) =
      Real.pi ^ 2 / 8 := by
  have hs : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) ^ 2)) :=
    hasSum_zeta_two.summable
  have he : Summable (fun n : ℕ ↦ 1 / (((2 * n : ℕ) : ℝ) ^ 2)) :=
    hs.comp_injective (fun _ _ h ↦ by omega)
  have ho : Summable (fun n : ℕ ↦ 1 / (((2 * n + 1 : ℕ) : ℝ) ^ 2)) :=
    hs.comp_injective (fun _ _ h ↦ by omega)
  have hsplit :
      (∑' n : ℕ, 1 / (((2 * n : ℕ) : ℝ) ^ 2)) +
          (∑' n : ℕ, 1 / (((2 * n + 1 : ℕ) : ℝ) ^ 2)) =
        ∑' n : ℕ, 1 / ((n : ℝ) ^ 2) :=
    tsum_even_add_odd (f := fun n : ℕ ↦ 1 / ((n : ℝ) ^ 2)) he ho
  rw [hasSum_zeta_two.tsum_eq, even_inv_sq_tsum] at hsplit
  linarith

private theorem summable_inv_cube :
    Summable (fun n : ℕ ↦ 1 / ((n : ℝ) ^ 3)) :=
  Real.summable_one_div_nat_pow.mpr (by norm_num)

private theorem even_inv_cube_tsum :
    (∑' n : ℕ, 1 / (((2 * n : ℕ) : ℝ) ^ 3)) =
      (1 / 8 : ℝ) * realZetaThree := by
  calc
    (∑' n : ℕ, 1 / (((2 * n : ℕ) : ℝ) ^ 3)) =
        ∑' n : ℕ, (1 / 8 : ℝ) * (1 / ((n : ℝ) ^ 3)) := by
      apply tsum_congr
      intro n
      push_cast
      rw [mul_pow]
      norm_num
      ring
    _ = (1 / 8 : ℝ) * ∑' n : ℕ, 1 / ((n : ℝ) ^ 3) := by
      rw [tsum_mul_left]
    _ = (1 / 8 : ℝ) * realZetaThree := by
      rfl

set_option maxHeartbeats 800000 in
private theorem odd_inv_cube_tsum :
    (∑' n : ℕ, 1 / (((2 * n + 1 : ℕ) : ℝ) ^ 3)) =
      (7 / 8 : ℝ) * realZetaThree := by
  have he : Summable (fun n : ℕ ↦ 1 / (((2 * n : ℕ) : ℝ) ^ 3)) :=
    summable_inv_cube.comp_injective (fun _ _ h ↦ by omega)
  have ho : Summable (fun n : ℕ ↦ 1 / (((2 * n + 1 : ℕ) : ℝ) ^ 3)) :=
    summable_inv_cube.comp_injective (fun _ _ h ↦ by omega)
  have hsplit :
      (∑' n : ℕ, 1 / (((2 * n : ℕ) : ℝ) ^ 3)) +
          (∑' n : ℕ, 1 / (((2 * n + 1 : ℕ) : ℝ) ^ 3)) =
        ∑' n : ℕ, 1 / ((n : ℝ) ^ 3) :=
    tsum_even_add_odd (f := fun n : ℕ ↦ 1 / ((n : ℝ) ^ 3)) he ho
  rw [show (∑' n : ℕ, 1 / ((n : ℝ) ^ 3)) = realZetaThree by rfl,
    even_inv_cube_tsum] at hsplit
  linarith

private theorem shifted_inv_sq_tsum :
    (∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) =
      Real.pi ^ 2 / 6 := by
  have h := hasSum_zeta_two.summable.sum_add_tsum_nat_add 1
  rw [hasSum_zeta_two.tsum_eq] at h
  norm_num at h
  simpa only [Nat.cast_add, Nat.cast_one, one_div] using h

private theorem shifted_inv_cube_tsum :
    (∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) ^ 3)) =
      realZetaThree := by
  have h := summable_inv_cube.sum_add_tsum_nat_add 1
  norm_num at h
  simpa only [realZetaThree, Nat.cast_add, Nat.cast_one, one_div] using h

private theorem negPsiTwo_nat_succ_eq (a : ℕ) :
    negPsiTwoSeries (((a + 1 : ℕ) : ℝ)) =
      ∑' b : ℕ, 2 / (((a + b + 1 : ℕ) : ℝ) ^ 3) := by
  unfold negPsiTwoSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro b
  push_cast
  ring

private theorem summable_integer_antidiagonal :
    Summable (fun n : ℕ ↦
      (((n + 1 : ℕ) : ℝ)) *
        (2 / (((n + 1 : ℕ) : ℝ) ^ 3))) := by
  have hs0 : Summable (fun n : ℕ ↦
      1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 hasSum_zeta_two.summable
  have hs := hs0.mul_left 2
  refine hs.congr (fun n ↦ ?_)
  have hn : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  field_simp [hn.ne']

private theorem tsum_negPsiTwo_nat_succ :
    (∑' a : ℕ, negPsiTwoSeries (((a + 1 : ℕ) : ℝ))) =
      Real.pi ^ 2 / 3 := by
  let f : ℕ → ℝ := fun n ↦ 2 / (((n + 1 : ℕ) : ℝ) ^ 3)
  have hs : Summable (fun n : ℕ ↦ ((n : ℝ) + 1) * f n) := by
    simpa only [f, Nat.cast_add, Nat.cast_one] using
      summable_integer_antidiagonal
  have hgroup := tsum_tsum_nat_add_eq f (fun n ↦ by dsimp [f]; positivity) hs
  calc
    (∑' a : ℕ, negPsiTwoSeries (((a + 1 : ℕ) : ℝ))) =
        ∑' a : ℕ, ∑' b : ℕ, f (a + b) := by
      apply tsum_congr
      intro a
      rw [negPsiTwo_nat_succ_eq]
    _ = ∑' n : ℕ, ((n : ℝ) + 1) * f n := hgroup
    _ = ∑' n : ℕ, 2 * (1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
      apply tsum_congr
      intro n
      dsimp [f]
      have hn : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
      push_cast
      field_simp [hn.ne']
    _ = 2 * ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) ^ 2) := by
      rw [tsum_mul_left]
    _ = Real.pi ^ 2 / 3 := by rw [shifted_inv_sq_tsum]; ring

private theorem negPsiTwo_nat_half_eq (a : ℕ) :
    negPsiTwoSeries ((a : ℝ) + 1 / 2) =
      ∑' b : ℕ, 16 / (((2 * (a + b) + 1 : ℕ) : ℝ) ^ 3) := by
  unfold negPsiTwoSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro b
  have hx : 0 < (a : ℝ) + 1 / 2 + (b : ℝ) := by positivity
  have ho : 0 < (((2 * (a + b) + 1 : ℕ) : ℝ)) := by positivity
  field_simp [hx.ne', ho.ne']
  push_cast
  ring

private theorem summable_odd_inv_sq :
    Summable (fun n : ℕ ↦ 1 / (((2 * n + 1 : ℕ) : ℝ) ^ 2)) :=
  hasSum_zeta_two.summable.comp_injective (fun _ _ h ↦ by omega)

private theorem summable_odd_inv_cube :
    Summable (fun n : ℕ ↦ 1 / (((2 * n + 1 : ℕ) : ℝ) ^ 3)) :=
  summable_inv_cube.comp_injective (fun _ _ h ↦ by omega)

private theorem half_antidiagonal_factor (n : ℕ) :
    ((n : ℝ) + 1) *
        (16 / (((2 * n + 1 : ℕ) : ℝ) ^ 3)) =
      8 * (1 / (((2 * n + 1 : ℕ) : ℝ) ^ 2)) +
        8 * (1 / (((2 * n + 1 : ℕ) : ℝ) ^ 3)) := by
  have ho : 0 < (((2 * n + 1 : ℕ) : ℝ)) := by positivity
  field_simp [ho.ne']
  push_cast
  ring

private theorem summable_half_antidiagonal :
    Summable (fun n : ℕ ↦
      ((n : ℝ) + 1) *
        (16 / (((2 * n + 1 : ℕ) : ℝ) ^ 3))) := by
  have hs := (summable_odd_inv_sq.mul_left 8).add
    (summable_odd_inv_cube.mul_left 8)
  exact hs.congr (fun n ↦ (half_antidiagonal_factor n).symm)

private theorem tsum_negPsiTwo_nat_half :
    (∑' a : ℕ, negPsiTwoSeries ((a : ℝ) + 1 / 2)) =
      Real.pi ^ 2 + 7 * realZetaThree := by
  let f : ℕ → ℝ := fun n ↦
    16 / (((2 * n + 1 : ℕ) : ℝ) ^ 3)
  have hgroup := tsum_tsum_nat_add_eq f (fun n ↦ by dsimp [f]; positivity)
    summable_half_antidiagonal
  have hsplit :
      (∑' n : ℕ, (
        8 * (1 / (((2 * n + 1 : ℕ) : ℝ) ^ 2)) +
          8 * (1 / (((2 * n + 1 : ℕ) : ℝ) ^ 3)))) =
        (∑' n : ℕ, 8 * (1 / (((2 * n + 1 : ℕ) : ℝ) ^ 2))) +
          ∑' n : ℕ, 8 * (1 / (((2 * n + 1 : ℕ) : ℝ) ^ 3)) :=
    (summable_odd_inv_sq.mul_left 8).tsum_add
      (summable_odd_inv_cube.mul_left 8)
  calc
    (∑' a : ℕ, negPsiTwoSeries ((a : ℝ) + 1 / 2)) =
        ∑' a : ℕ, ∑' b : ℕ, f (a + b) := by
      apply tsum_congr
      intro a
      rw [negPsiTwo_nat_half_eq]
    _ = ∑' n : ℕ, ((n : ℝ) + 1) * f n := hgroup
    _ = ∑' n : ℕ, (
        8 * (1 / (((2 * n + 1 : ℕ) : ℝ) ^ 2)) +
          8 * (1 / (((2 * n + 1 : ℕ) : ℝ) ^ 3))) := by
      apply tsum_congr
      exact half_antidiagonal_factor
    _ = (∑' n : ℕ, 8 * (1 / (((2 * n + 1 : ℕ) : ℝ) ^ 2))) +
          ∑' n : ℕ, 8 * (1 / (((2 * n + 1 : ℕ) : ℝ) ^ 3)) := hsplit
    _ = 8 * (∑' n : ℕ, 1 / (((2 * n + 1 : ℕ) : ℝ) ^ 2)) +
          8 * (∑' n : ℕ, 1 / (((2 * n + 1 : ℕ) : ℝ) ^ 3)) := by
      rw [tsum_mul_left, tsum_mul_left]
    _ = Real.pi ^ 2 + 7 * realZetaThree := by
      rw [odd_inv_sq_tsum, odd_inv_cube_tsum]
      ring

/-- Exact evaluation of the square hard-edge third-cumulant constant.

The proof is entirely from the defining positive series: split the outer
index into even and odd terms, group the inner double sums on finite
antidiagonals, and use Euler's certified value of `ζ(2)`.  The quantity
`realZetaThree` remains its positive defining series, so no unproved closed
form for `ζ(3)` is used. -/
theorem hardEdgeAConstant_zero_eq_squareAConstant :
    hardEdgeAConstant 0 = squareAConstant := by
  let f : ℕ → ℝ := fun n ↦
    negPsiTwoSeries (((n + 1 : ℕ) : ℝ) / 2)
  have hs : Summable f := by
    simpa only [f, zero_add] using summable_hardEdgeA_terms 0
  have he : Summable (fun n : ℕ ↦ f (2 * n)) :=
    hs.comp_injective (fun _ _ h ↦ by omega)
  have ho : Summable (fun n : ℕ ↦ f (2 * n + 1)) :=
    hs.comp_injective (fun _ _ h ↦ by omega)
  have hsplit :
      (∑' n : ℕ, f (2 * n)) + (∑' n : ℕ, f (2 * n + 1)) =
        ∑' n : ℕ, f n :=
    tsum_even_add_odd (f := f) he ho
  have heval : (∑' n : ℕ, f (2 * n)) =
      Real.pi ^ 2 + 7 * realZetaThree := by
    calc
      (∑' n : ℕ, f (2 * n)) =
          ∑' n : ℕ, negPsiTwoSeries ((n : ℝ) + 1 / 2) := by
        apply tsum_congr
        intro n
        dsimp [f]
        congr 1
        push_cast
        ring
      _ = Real.pi ^ 2 + 7 * realZetaThree := tsum_negPsiTwo_nat_half
  have hoval : (∑' n : ℕ, f (2 * n + 1)) = Real.pi ^ 2 / 3 := by
    calc
      (∑' n : ℕ, f (2 * n + 1)) =
          ∑' n : ℕ, negPsiTwoSeries (((n + 1 : ℕ) : ℝ)) := by
        apply tsum_congr
        intro n
        dsimp [f]
        congr 1
        push_cast
        ring
      _ = Real.pi ^ 2 / 3 := tsum_negPsiTwo_nat_succ
  rw [heval, hoval] at hsplit
  have hdef : hardEdgeAConstant 0 = ∑' n : ℕ, f n := by
    unfold hardEdgeAConstant
    apply tsum_congr
    intro n
    simp only [f, zero_add]
  rw [hdef]
  unfold squareAConstant
  rw [← hsplit]
  ring

end

end LogdetLean
