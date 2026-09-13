import LogdetLean.HardEdgeConstant
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

/-!
# Refined null asymptotics

This module proves the additive square-edge variance constant from the exact
finite series.  The argument is equivalent to the even/odd trigamma
calculation in the manuscript, but is organized around the summable error

`psi_1(k/2) - 2/k`.

Its total mass is evaluated by splitting `k` into odd and even values and
grouping two positive tail kernels on finite antidiagonals.  No asymptotic
expansion of trigamma is assumed.
-/

namespace LogdetLean

open Filter Real Set
open scoped BigOperators Topology

noncomputable section

/-! ## Telescoping and antidiagonal helpers -/

private theorem hasSum_reciprocal_step (a : ℕ) :
    HasSum (fun b : ℕ ↦
      1 / ((a : ℝ) + (b : ℝ) + 1) -
        1 / ((a : ℝ) + (b : ℝ) + 2))
      (1 / ((a : ℝ) + 1)) := by
  let f : ℕ → ℝ := fun b ↦ 1 / ((a : ℝ) + (b : ℝ) + 1)
  have hnonneg : ∀ b, 0 ≤ f b - f (b + 1) := by
    intro b
    dsimp [f]
    push_cast
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hmain : HasSum (fun b ↦ f b - f (b + 1)) (f 0) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg]
    simp_rw [Finset.sum_range_sub']
    have hden : Tendsto (fun n : ℕ ↦ ((n + (a + 1) : ℕ) : ℝ))
        atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat (a + 1))
    have htail : Tendsto f atTop (nhds 0) := by
      dsimp [f]
      convert hden.const_div_atTop 1 using 1
      funext n
      push_cast
      congr 1
      ring
    have hconst : Tendsto (fun _ : ℕ ↦ f 0) atTop (nhds (f 0)) :=
      tendsto_const_nhds
    simpa using hconst.sub htail
  convert hmain using 1
  · funext b
    dsimp [f]
    push_cast
    ring
  · dsimp [f]
    norm_num

private theorem hasSum_odd_reciprocal_step (a : ℕ) :
    HasSum (fun b : ℕ ↦
      2 / (2 * ((a : ℝ) + (b : ℝ)) + 1) -
        2 / (2 * ((a : ℝ) + (b : ℝ)) + 3))
      (2 / (2 * (a : ℝ) + 1)) := by
  let f : ℕ → ℝ := fun b ↦ 2 / (2 * ((a : ℝ) + (b : ℝ)) + 1)
  have hnonneg : ∀ b, 0 ≤ f b - f (b + 1) := by
    intro b
    dsimp [f]
    push_cast
    rw [sub_nonneg]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have hmain : HasSum (fun b ↦ f b - f (b + 1)) (f 0) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg]
    simp_rw [Finset.sum_range_sub']
    have hdenNat : Tendsto (fun n : ℕ ↦ 2 * n + (2 * a + 1))
        atTop atTop := by
      have hle : (fun n : ℕ ↦ n) ≤ᶠ[atTop]
          (fun n : ℕ ↦ 2 * n + (2 * a + 1)) := by
        filter_upwards with n
        omega
      exact Filter.tendsto_atTop_mono' atTop
        (f₁ := fun n : ℕ ↦ n)
        (f₂ := fun n : ℕ ↦ 2 * n + (2 * a + 1))
        hle tendsto_id
    have hden : Tendsto
        (fun n : ℕ ↦ ((2 * n + (2 * a + 1) : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hdenNat
    have htail : Tendsto f atTop (nhds 0) := by
      dsimp [f]
      convert hden.const_div_atTop 2 using 1
      funext n
      push_cast
      congr 1
      ring
    have hconst : Tendsto (fun _ : ℕ ↦ f 0) atTop (nhds (f 0)) :=
      tendsto_const_nhds
    simpa using hconst.sub htail
  convert hmain using 1
  · funext b
    dsimp [f]
    push_cast
    congr 1
    ring
  · dsimp [f]
    norm_num

/-- Group a nonnegative summable kernel depending only on `a+b` along finite
antidiagonals.  The first conclusion is retained because it supplies the
summability of the outer trigamma-error sequences below. -/
private theorem summable_tsum_nat_add_and_tsum_eq
    (f : ℕ → ℝ) (hf0 : ∀ n, 0 ≤ f n)
    (hs : Summable (fun n : ℕ ↦ (n + 1 : ℝ) * f n)) :
    Summable (fun a : ℕ ↦ ∑' b : ℕ, f (a + b)) ∧
      (∑' a : ℕ, ∑' b : ℕ, f (a + b)) =
        ∑' n : ℕ, (n + 1 : ℝ) * f n := by
  let F : (Sigma fun n : ℕ ↦ ↑(Finset.antidiagonal n)) → ℝ :=
    fun z ↦ f z.1
  have hF0 : ∀ z, 0 ≤ F z := fun z ↦ hf0 z.1
  have hfiber (n : ℕ) :
      Summable (fun z : ↑(Finset.antidiagonal n) ↦ F ⟨n, z⟩) :=
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
  let e : (Sigma fun n : ℕ ↦ ↑(Finset.antidiagonal n)) ≃ ℕ × ℕ :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd
  have hprod : Summable (fun z : ℕ × ℕ ↦ f (z.1 + z.2)) := by
    rw [← e.summable_iff]
    convert hF using 1
    funext z
    dsimp [e, F]
    exact congrArg f (Finset.mem_antidiagonal.mp z.2.property)
  have houter : Summable (fun a : ℕ ↦ ∑' b : ℕ, f (a + b)) := by
    simpa using hprod.prod
  refine ⟨houter, ?_⟩
  calc
    (∑' a : ℕ, ∑' b : ℕ, f (a + b)) =
        ∑' z : ℕ × ℕ, f (z.1 + z.2) := hprod.tsum_prod.symm
    _ = ∑' z : (Sigma fun n : ℕ ↦ ↑(Finset.antidiagonal n)),
          f ((e z).1 + (e z).2) := (e.tsum_eq _).symm
    _ = ∑' z : (Sigma fun n : ℕ ↦ ↑(Finset.antidiagonal n)), F z := by
      apply tsum_congr
      intro z
      dsimp [e, F]
      exact congrArg f (Finset.mem_antidiagonal.mp z.2.property)
    _ = ∑' n : ℕ, ∑' z : ↑(Finset.antidiagonal n), F ⟨n, z⟩ := by
      exact hF.tsum_sigma' hfiber
    _ = ∑' n : ℕ, (n + 1 : ℝ) * f n := by
      apply tsum_congr
      exact hfiberSum

/-! ## The summable square-edge trigamma error -/

private def evenSquareErrorKernel (n : ℕ) : ℝ :=
  1 / (((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2))

private def oddSquareErrorKernel (n : ℕ) : ℝ :=
  8 / ((2 * (n : ℝ) + 1) ^ 2 * (2 * (n : ℝ) + 3))

private def evenSquareError (a : ℕ) : ℝ :=
  trigammaSeries ((a : ℝ) + 1) - 1 / ((a : ℝ) + 1)

private def oddSquareError (a : ℕ) : ℝ :=
  trigammaSeries ((a : ℝ) + 1 / 2) - 2 / (2 * (a : ℝ) + 1)

private theorem evenSquareError_eq_tsum (a : ℕ) :
    evenSquareError a = ∑' b : ℕ, evenSquareErrorKernel (a + b) := by
  have hx : 0 < (a : ℝ) + 1 := by positivity
  have htrig := summable_trigammaSeries_terms hx
  have htel := hasSum_reciprocal_step a
  unfold evenSquareError trigammaSeries
  rw [← htel.tsum_eq, ← htrig.tsum_sub htel.summable]
  apply tsum_congr
  intro b
  unfold evenSquareErrorKernel
  have h1 : 0 < (a : ℝ) + (b : ℝ) + 1 := by positivity
  have h2 : 0 < (a : ℝ) + (b : ℝ) + 2 := by positivity
  push_cast
  field_simp [h1.ne', h2.ne']
  ring

private theorem oddSquareError_eq_tsum (a : ℕ) :
    oddSquareError a = ∑' b : ℕ, oddSquareErrorKernel (a + b) := by
  have hx : 0 < (a : ℝ) + 1 / 2 := by positivity
  have htrig := summable_trigammaSeries_terms hx
  have htel := hasSum_odd_reciprocal_step a
  unfold oddSquareError trigammaSeries
  rw [← htel.tsum_eq, ← htrig.tsum_sub htel.summable]
  apply tsum_congr
  intro b
  unfold oddSquareErrorKernel
  have hr : 0 < 2 * ((a : ℝ) + (b : ℝ)) + 1 := by positivity
  have hr2 : 0 < 2 * ((a : ℝ) + (b : ℝ)) + 3 := by positivity
  push_cast
  field_simp [hr.ne', hr2.ne']
  ring

private theorem even_inv_sq_tsum_refined :
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

private theorem odd_inv_sq_tsum_refined :
    (∑' n : ℕ, 1 / (((2 * n + 1 : ℕ) : ℝ) ^ 2)) =
      Real.pi ^ 2 / 8 := by
  have hs : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) ^ 2)) :=
    hasSum_zeta_two.summable
  have he : Summable (fun n : ℕ ↦ 1 / (((2 * n : ℕ) : ℝ) ^ 2)) :=
    hs.comp_injective (fun _ _ h ↦ by omega)
  have ho : Summable
      (fun n : ℕ ↦ 1 / (((2 * n + 1 : ℕ) : ℝ) ^ 2)) :=
    hs.comp_injective (fun _ _ h ↦ by omega)
  have hsplit := tsum_even_add_odd
    (f := fun n : ℕ ↦ 1 / ((n : ℝ) ^ 2)) he ho
  rw [hasSum_zeta_two.tsum_eq, even_inv_sq_tsum_refined] at hsplit
  linarith

private theorem hasSum_evenSquareError_weighted :
    HasSum (fun n : ℕ ↦ (n + 1 : ℝ) * evenSquareErrorKernel n) 1 := by
  have h := hasSum_reciprocal_step 0
  convert h using 1
  · funext n
    unfold evenSquareErrorKernel
    norm_num
    have h1 : 0 < (n : ℝ) + 1 := by positivity
    have h2 : 0 < (n : ℝ) + 2 := by positivity
    field_simp [h1.ne', h2.ne']
    ring
  · norm_num

private theorem hasSum_odd_inv_sq_refined :
    HasSum (fun n : ℕ ↦ 1 / (((2 * n + 1 : ℕ) : ℝ) ^ 2))
      (Real.pi ^ 2 / 8) := by
  have hs : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) ^ 2)) :=
    hasSum_zeta_two.summable
  have ho : Summable
      (fun n : ℕ ↦ 1 / (((2 * n + 1 : ℕ) : ℝ) ^ 2)) :=
    hs.comp_injective (fun _ _ h ↦ by omega)
  rw [← odd_inv_sq_tsum_refined]
  exact ho.hasSum

private theorem hasSum_oddSquareError_weighted :
    HasSum (fun n : ℕ ↦ (n + 1 : ℝ) * oddSquareErrorKernel n)
      (1 + Real.pi ^ 2 / 4) := by
  have htel := (hasSum_odd_reciprocal_step 0).mul_left (1 / 2 : ℝ)
  have hsq := hasSum_odd_inv_sq_refined.mul_left 2
  have hadd := htel.add hsq
  let g : ℕ → ℝ := fun n ↦
    (1 / 2 : ℝ) *
        (2 / (2 * ((0 : ℝ) + (n : ℝ)) + 1) -
          2 / (2 * ((0 : ℝ) + (n : ℝ)) + 3)) +
      2 * (1 / (((2 * n + 1 : ℕ) : ℝ) ^ 2))
  have hg : (fun n : ℕ ↦ (n + 1 : ℝ) * oddSquareErrorKernel n) = g := by
    funext n
    unfold oddSquareErrorKernel
    dsimp [g]
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_mul,
      Nat.cast_ofNat, zero_add]
    have h1 : 0 < 2 * (n : ℝ) + 1 := by positivity
    have h3 : 0 < 2 * (n : ℝ) + 3 := by positivity
    field_simp [h1.ne', h3.ne']
    ring
  have hc : 1 + Real.pi ^ 2 / 4 =
      (1 / 2 : ℝ) * (2 / (2 * (0 : ℝ) + 1)) +
        2 * (Real.pi ^ 2 / 8) := by ring
  rw [hg, hc]
  simpa [g, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hadd

private theorem summable_evenSquareError : Summable evenSquareError := by
  have hgroup := summable_tsum_nat_add_and_tsum_eq evenSquareErrorKernel
    (fun n ↦ by unfold evenSquareErrorKernel; positivity)
    hasSum_evenSquareError_weighted.summable
  exact hgroup.1.congr fun a ↦ (evenSquareError_eq_tsum a).symm

private theorem tsum_evenSquareError :
    (∑' a : ℕ, evenSquareError a) = 1 := by
  have hgroup := summable_tsum_nat_add_and_tsum_eq evenSquareErrorKernel
    (fun n ↦ by unfold evenSquareErrorKernel; positivity)
    hasSum_evenSquareError_weighted.summable
  calc
    (∑' a : ℕ, evenSquareError a) =
        ∑' a : ℕ, ∑' b : ℕ, evenSquareErrorKernel (a + b) := by
      apply tsum_congr
      exact evenSquareError_eq_tsum
    _ = ∑' n : ℕ, (n + 1 : ℝ) * evenSquareErrorKernel n := hgroup.2
    _ = 1 := hasSum_evenSquareError_weighted.tsum_eq

private theorem summable_oddSquareError : Summable oddSquareError := by
  have hgroup := summable_tsum_nat_add_and_tsum_eq oddSquareErrorKernel
    (fun n ↦ by unfold oddSquareErrorKernel; positivity)
    hasSum_oddSquareError_weighted.summable
  exact hgroup.1.congr fun a ↦ (oddSquareError_eq_tsum a).symm

private theorem tsum_oddSquareError :
    (∑' a : ℕ, oddSquareError a) = 1 + Real.pi ^ 2 / 4 := by
  have hgroup := summable_tsum_nat_add_and_tsum_eq oddSquareErrorKernel
    (fun n ↦ by unfold oddSquareErrorKernel; positivity)
    hasSum_oddSquareError_weighted.summable
  calc
    (∑' a : ℕ, oddSquareError a) =
        ∑' a : ℕ, ∑' b : ℕ, oddSquareErrorKernel (a + b) := by
      apply tsum_congr
      exact oddSquareError_eq_tsum
    _ = ∑' n : ℕ, (n + 1 : ℝ) * oddSquareErrorKernel n := hgroup.2
    _ = 1 + Real.pi ^ 2 / 4 := hasSum_oddSquareError_weighted.tsum_eq

/-- The summable residual after removing the leading `2/k` term from
`psi_1(k/2)`, with the positive integer written as `k=n+1`. -/
def squareTrigammaError (n : ℕ) : ℝ :=
  trigammaSeries ((((n + 1 : ℕ) : ℝ)) / 2) -
    2 / (((n + 1 : ℕ) : ℝ))

/-- Elementary pointwise bounds for the square trigamma residual. -/
theorem squareTrigammaError_bounds (n : ℕ) :
    0 ≤ squareTrigammaError n ∧
      squareTrigammaError n ≤ 4 / (((n + 1 : ℕ) : ℝ) ^ 2) := by
  have hkR : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hx : 0 < (((n + 1 : ℕ) : ℝ)) / 2 := by positivity
  have hb := trigammaSeries_bounds hx
  have hlin : 1 / ((((n + 1 : ℕ) : ℝ)) / 2) =
      2 / (((n + 1 : ℕ) : ℝ)) := by
    field_simp [hkR.ne']
  have hsq : 1 / ((((n + 1 : ℕ) : ℝ)) / 2) ^ 2 =
      4 / (((n + 1 : ℕ) : ℝ) ^ 2) := by
    field_simp [hkR.ne'] <;> norm_num
  unfold squareTrigammaError
  constructor
  · rw [← hlin]
    exact sub_nonneg.mpr hb.1
  · rw [← hlin, ← hsq]
    linarith [hb.2]

private theorem squareTrigammaError_even (a : ℕ) :
    squareTrigammaError (2 * a) = oddSquareError a := by
  unfold squareTrigammaError oddSquareError
  push_cast
  congr 1 <;> ring

private theorem squareTrigammaError_odd (a : ℕ) :
    squareTrigammaError (2 * a + 1) = evenSquareError a := by
  unfold squareTrigammaError evenSquareError
  push_cast
  congr 1
  · ring
  · have ha : 0 < (a : ℝ) + 1 := by positivity
    field_simp [ha.ne']
    ring

/-- The square trigamma error is absolutely summable. -/
theorem summable_squareTrigammaError : Summable squareTrigammaError := by
  apply Summable.even_add_odd
  · exact summable_oddSquareError.congr fun a ↦ (squareTrigammaError_even a).symm
  · exact summable_evenSquareError.congr fun a ↦ (squareTrigammaError_odd a).symm

/-- Exact total mass of the square trigamma error.  This is the source of
the additive `2 + pi^2/4` correction to the leading harmonic sum. -/
theorem tsum_squareTrigammaError :
    (∑' n : ℕ, squareTrigammaError n) = 2 + Real.pi ^ 2 / 4 := by
  have he : Summable (fun a : ℕ ↦ squareTrigammaError (2 * a)) :=
    summable_oddSquareError.congr fun a ↦ (squareTrigammaError_even a).symm
  have ho : Summable (fun a : ℕ ↦ squareTrigammaError (2 * a + 1)) :=
    summable_evenSquareError.congr fun a ↦ (squareTrigammaError_odd a).symm
  have hsplit := tsum_even_add_odd (f := squareTrigammaError) he ho
  rw [show (∑' a : ℕ, squareTrigammaError (2 * a)) =
      ∑' a : ℕ, oddSquareError a by
        apply tsum_congr
        exact squareTrigammaError_even,
    show (∑' a : ℕ, squareTrigammaError (2 * a + 1)) =
      ∑' a : ℕ, evenSquareError a by
        apply tsum_congr
        exact squareTrigammaError_odd,
    tsum_oddSquareError, tsum_evenSquareError] at hsplit
  linarith

/-! ## Exact square variance decomposition -/

/-- At the square edge, subtracting the elementary harmonic leading term
leaves a partial sum of the summable trigamma errors, minus the repeated
common-shape endpoint error.  This is an exact finite identity. -/
theorem nullVSeries_sub_nullVLeading_square_eq (p : ℕ) (hp : 2 ≤ p) :
    nullVSeries p p - nullVLeading p p =
      (∑ n ∈ Finset.range (p - 1), squareTrigammaError n) -
        ((p : ℝ) - 1) * squareTrigammaError (p - 1) := by
  have hadm : Admissible p p := ⟨hp, le_rfl⟩
  rw [nullVSeries_eq_gap_sum hadm]
  unfold nullVLeading nullGapPowerDifference
  have hgap : p - p + 1 = 1 := by omega
  rw [hgap, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_Ico_eq_sum_range]
  simp only [pow_one]
  calc
    (∑ n ∈ Finset.range (p - 1),
        (trigammaSeries (((1 + n : ℕ) : ℝ) / 2) -
            trigammaSeries ((p : ℝ) / 2) -
          2 * (1 / (((1 + n : ℕ) : ℝ)) - 1 / (p : ℝ)))) =
        ∑ n ∈ Finset.range (p - 1),
          (squareTrigammaError n - squareTrigammaError (p - 1)) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hp1 : 1 ≤ p := by omega
      have hpn : p - 1 + 1 = p := Nat.sub_add_cancel hp1
      have hpnR : ((p - 1 : ℕ) : ℝ) + 1 = (p : ℝ) := by
        exact_mod_cast hpn
      unfold squareTrigammaError
      push_cast
      rw [hpnR]
      ring
    _ = (∑ n ∈ Finset.range (p - 1), squareTrigammaError n) -
          ((p : ℝ) - 1) * squareTrigammaError (p - 1) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
      simp only [nsmul_eq_mul]
      rw [Nat.cast_sub (by omega : 1 ≤ p)]
      norm_num

private theorem tendsto_nat_sub_one_atTop :
    Tendsto (fun p : ℕ ↦ p - 1) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop (b + 1)] with p hp
  omega

/-- The finite partial sum of square residuals converges to its exact total
mass. -/
theorem tendsto_squareTrigammaError_partialSum :
    Tendsto (fun p : ℕ ↦
      ∑ n ∈ Finset.range (p - 1), squareTrigammaError n)
      atTop (nhds (2 + Real.pi ^ 2 / 4)) := by
  have h := summable_squareTrigammaError.hasSum.tendsto_sum_nat.comp
    tendsto_nat_sub_one_atTop
  rw [tsum_squareTrigammaError] at h
  exact h

private theorem squareTrigammaEndpointCorrection_nonneg (p : ℕ)
    (hp : 1 ≤ p) :
    0 ≤ ((p : ℝ) - 1) * squareTrigammaError (p - 1) := by
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  exact mul_nonneg (sub_nonneg.mpr hpR)
    (squareTrigammaError_bounds (p - 1)).1

private theorem squareTrigammaEndpointCorrection_le (p : ℕ)
    (hp : 2 ≤ p) :
    ((p : ℝ) - 1) * squareTrigammaError (p - 1) ≤
      4 / (p : ℝ) := by
  have hp1 : 1 ≤ p := by omega
  have hpR : 0 < (p : ℝ) := Nat.cast_pos.mpr (by omega)
  have hpCast : (((p - 1 + 1 : ℕ) : ℝ)) = (p : ℝ) := by
    rw [Nat.sub_add_cancel hp1]
  have hcoeff : 0 ≤ (p : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
    linarith
  calc
    ((p : ℝ) - 1) * squareTrigammaError (p - 1) ≤
        ((p : ℝ) - 1) *
          (4 / (((p - 1 + 1 : ℕ) : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left (squareTrigammaError_bounds (p - 1)).2 hcoeff
    _ = (4 / (p : ℝ)) * (((p : ℝ) - 1) / (p : ℝ)) := by
      rw [hpCast]
      field_simp [hpR.ne']
    _ ≤ (4 / (p : ℝ)) * 1 := by
      apply mul_le_mul_of_nonneg_left
      · exact (div_le_one hpR).2 (by linarith)
      · positivity
    _ = 4 / (p : ℝ) := mul_one _

/-- The repeated common-shape endpoint residual vanishes. -/
theorem tendsto_squareTrigammaEndpointCorrection_zero :
    Tendsto (fun p : ℕ ↦
      ((p : ℝ) - 1) * squareTrigammaError (p - 1))
      atTop (nhds 0) := by
  have hbound : Tendsto (fun p : ℕ ↦ 4 / (p : ℝ))
      atTop (nhds 0) :=
    tendsto_natCast_atTop_atTop.const_div_atTop 4
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 1] with p hp
    exact squareTrigammaEndpointCorrection_nonneg p hp
  · filter_upwards [eventually_ge_atTop 2] with p hp
    exact squareTrigammaEndpointCorrection_le p hp
  · exact hbound

/-- Exact additive correction from the trigamma series to the elementary
square leading term. -/
theorem tendsto_square_nullVSeries_sub_nullVLeading :
    Tendsto (fun p : ℕ ↦ nullVSeries p p - nullVLeading p p)
      atTop (nhds (2 + Real.pi ^ 2 / 4)) := by
  have h := tendsto_squareTrigammaError_partialSum.sub
    tendsto_squareTrigammaEndpointCorrection_zero
  have h' : Tendsto (fun p : ℕ ↦
      (∑ n ∈ Finset.range (p - 1), squareTrigammaError n) -
        ((p : ℝ) - 1) * squareTrigammaError (p - 1))
      atTop (nhds (2 + Real.pi ^ 2 / 4)) := by
    simpa using h
  apply h'.congr'
  filter_upwards [eventually_ge_atTop 2] with p hp
  exact (nullVSeries_sub_nullVLeading_square_eq p hp).symm

/-! ## The harmonic leading term and the refined square limit -/

private theorem harmonic_pred_cast_eq_sub_inv (p : ℕ) (hp : 1 ≤ p) :
    (harmonic (p - 1) : ℝ) =
      (harmonic p : ℝ) - 1 / (p : ℝ) := by
  have hpEq : p - 1 + 1 = p := Nat.sub_add_cancel hp
  have hs := congrArg (fun q : ℚ ↦ (q : ℝ)) (harmonic_succ (p - 1))
  rw [hpEq] at hs
  norm_num only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast] at hs
  rw [one_div]
  linarith

private theorem tendsto_harmonic_pred_sub_log :
    Tendsto (fun p : ℕ ↦
      (harmonic (p - 1) : ℝ) - Real.log (p : ℝ))
      atTop (nhds Real.eulerMascheroniConstant) := by
  have hinv : Tendsto (fun p : ℕ ↦ 1 / (p : ℝ))
      atTop (nhds 0) := tendsto_natCast_atTop_atTop.const_div_atTop 1
  have h := Real.tendsto_harmonic_sub_log.sub hinv
  have h' : Tendsto (fun p : ℕ ↦
      ((harmonic p : ℝ) - Real.log (p : ℝ)) - 1 / (p : ℝ))
      atTop (nhds Real.eulerMascheroniConstant) := by simpa using h
  apply h'.congr'
  filter_upwards [eventually_ge_atTop 1] with p hp
  rw [harmonic_pred_cast_eq_sub_inv p hp]
  ring

private theorem tendsto_square_pred_fraction_one :
    Tendsto (fun p : ℕ ↦ ((p : ℝ) - 1) / (p : ℝ))
      atTop (nhds 1) := by
  have hinv : Tendsto (fun p : ℕ ↦ 1 / (p : ℝ))
      atTop (nhds 0) := tendsto_natCast_atTop_atTop.const_div_atTop 1
  have h : Tendsto (fun p : ℕ ↦ 1 - 1 / (p : ℝ))
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.sub hinv :
      Tendsto (fun p : ℕ ↦ (1 : ℝ) - 1 / (p : ℝ))
        atTop (nhds (1 - 0)))
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with p hp
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  field_simp [hpR]

/-- The elementary square leading variance has the exact additive harmonic
constant `2*EulerGamma-2`. -/
theorem tendsto_square_nullVLeading_sub_two_log :
    Tendsto (fun p : ℕ ↦
      nullVLeading p p - 2 * Real.log (p : ℝ))
      atTop (nhds (2 * Real.eulerMascheroniConstant - 2)) := by
  have h := (tendsto_harmonic_pred_sub_log.sub
    tendsto_square_pred_fraction_one).const_mul 2
  have h' : Tendsto (fun p : ℕ ↦
      2 * (((harmonic (p - 1) : ℝ) - Real.log (p : ℝ)) -
        ((p : ℝ) - 1) / (p : ℝ)))
      atTop (nhds (2 * Real.eulerMascheroniConstant - 2)) := by
    convert h using 1 <;> ring
  apply h'.congr'
  filter_upwards [eventually_ge_atTop 2] with p hp
  have hadm : Admissible p p := ⟨hp, le_rfl⟩
  have hv := nullVLeading_eq_harmonic_sub hadm
  simp only [Nat.sub_self, harmonic_zero, Rat.cast_zero, sub_zero] at hv
  rw [hv]
  ring

/-- Refined square-edge variance asymptotic:
`V_{p,p} - 2 log p -> 2*EulerGamma + pi^2/4`. -/
theorem tendsto_square_nullVSeries_sub_two_log :
    Tendsto (fun p : ℕ ↦
      nullVSeries p p - 2 * Real.log (p : ℝ))
      atTop
      (nhds (2 * Real.eulerMascheroniConstant + Real.pi ^ 2 / 4)) := by
  have h := tendsto_square_nullVSeries_sub_nullVLeading.add
    tendsto_square_nullVLeading_sub_two_log
  have h' : Tendsto (fun p : ℕ ↦
      (nullVSeries p p - nullVLeading p p) +
        (nullVLeading p p - 2 * Real.log (p : ℝ)))
      atTop
      (nhds ((2 + Real.pi ^ 2 / 4) +
        (2 * Real.eulerMascheroniConstant - 2))) := h
  convert h' using 1 <;> ring

/-! ## Finite hard-edge recurrence wrappers -/

/-- Iterating the one-step hard-edge recurrence gives an exact finite prefix
plus the remaining tail. -/
theorem hardEdgeAConstant_zero_eq_sum_add (d : ℕ) :
    hardEdgeAConstant 0 =
      (∑ k ∈ Finset.Icc 1 d,
        negPsiTwoSeries ((k : ℝ) / 2)) + hardEdgeAConstant d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [add_assoc, ← hardEdgeAConstant_eq_term_add_succ d]
      exact ih

/-- Manuscript sign convention for the same recurrence: the order-two
polygamma is the negative of `negPsiTwoSeries`. -/
theorem hardEdgeAConstant_eq_zero_add_negPsiTwoSum (d : ℕ) :
    hardEdgeAConstant d = hardEdgeAConstant 0 +
      ∑ k ∈ Finset.Icc 1 d,
        (-negPsiTwoSeries ((k : ℝ) / 2)) := by
  have h := hardEdgeAConstant_zero_eq_sum_add d
  rw [Finset.sum_neg_distrib]
  linarith

/-- Every positive hard-edge gap has strictly smaller third-cumulant
constant than the square edge. -/
theorem hardEdgeAConstant_lt_zero_of_pos {d : ℕ} (hd : 0 < d) :
    hardEdgeAConstant d < hardEdgeAConstant 0 :=
  hardEdgeAConstant_strictAnti hd

end

end LogdetLean
