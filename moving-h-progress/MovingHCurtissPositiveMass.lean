import LogdetLean.FiniteMeasureCurtissProgress
import LogdetLean.Coherence.MovingHCurtissVoidBridge
import LogdetLean.Coherence.MovingHDirectBonferroniAssembly
import Mathlib.Tactic

/-!
# Positive-mass reduction for the moving-H Curtiss boundary

The abstract finite-measure bridge splits into an elementary small-mass case
and a positive-mass transform-uniqueness case. In the actual moving-H model,
M3 and the literal one-edge approximation also imply a compact-window lower
bound for both the target void factor and the decorated finite-measure mass.
No spectral lower bound is introduced.
-/

namespace LogdetLean.Coherence

open Filter MeasureTheory ProbabilityTheory Set

noncomputable section

/-- The remaining abstract CDF statement after the elementary small-mass
branch has been removed. -/
def PaperFiniteMeasureGaussianPositiveMassCDFApproximation
    (nu : ℕ → ℝ → FiniteMeasure ℝ) (mass : ℕ → ℝ → ℝ) : Prop :=
  ∀ L : ℝ, 0 ≤ L → ∀ epsilon : ℝ, 0 < epsilon →
    ∀ᶠ p in atTop, ∀ z x : ℝ, |x| ≤ L → epsilon / 4 < mass p x →
      |(nu p x : Measure ℝ).real (Iic z) -
        standardNormalCDF z * mass p x| < epsilon

/-- A positive-mass CDF estimate plus the real-Laplace estimate proves the
full finite-measure CDF estimate. The small-mass case is discharged by the
import-light theorem `finiteMeasureCDFApproximation_of_small_mass`. -/
theorem paperFiniteMeasureGaussianCDFApproximation_of_positiveMass
    {nu : ℕ → ℝ → FiniteMeasure ℝ} {mass : ℕ → ℝ → ℝ}
    (hmass : ∀ p x, 0 ≤ mass p x ∧ mass p x ≤ 1)
    (hLaplace : PaperFiniteMeasureGaussianLaplaceApproximation nu mass)
    (hpositive :
      PaperFiniteMeasureGaussianPositiveMassCDFApproximation nu mass) :
    PaperFiniteMeasureGaussianCDFApproximation nu mass := by
  have hLaplace' :
      LogdetLean.FiniteMeasureGaussianLaplaceApproximation nu mass := by
    simpa [LogdetLean.FiniteMeasureGaussianLaplaceApproximation,
      PaperFiniteMeasureGaussianLaplaceApproximation] using hLaplace
  have hpositive' :
      LogdetLean.FiniteMeasureGaussianPositiveMassCDFApproximation
        nu mass standardNormalCDF := by
    simpa [LogdetLean.FiniteMeasureGaussianPositiveMassCDFApproximation,
      PaperFiniteMeasureGaussianPositiveMassCDFApproximation] using hpositive
  have hPhi : ∀ z, 0 ≤ standardNormalCDF z ∧ standardNormalCDF z ≤ 1 := by
    intro z
    exact ⟨ProbabilityTheory.cdf_nonneg _ _, ProbabilityTheory.cdf_le_one _ _⟩
  have hfull := LogdetLean.finiteMeasureGaussianCDFApproximation_of_positiveMass
    (fun p x ↦ (hmass p x).1) hPhi hLaplace' hpositive'
  simpa [PaperFiniteMeasureGaussianCDFApproximation] using hfull

/-- A narrower replacement for the original finite-measure Curtiss boundary.
It asks only for the positive-mass case. -/
def PaperFiniteMeasurePositiveMassCurtissBridge : Prop :=
  ∀ (nu : ℕ → ℝ → FiniteMeasure ℝ) (mass : ℕ → ℝ → ℝ),
    (∀ p x, 0 ≤ mass p x ∧ mass p x ≤ 1) →
    PaperFiniteMeasureGaussianLaplaceApproximation nu mass →
    PaperFiniteMeasureGaussianPositiveMassCDFApproximation nu mass

/-- The positive-mass Curtiss bridge implies the original bridge, because
all small-mass cases are already kernel-verified. -/
theorem paperFiniteMeasureCurtissBridge_of_positiveMass
    (hpositive : PaperFiniteMeasurePositiveMassCurtissBridge) :
    PaperFiniteMeasureCurtissBridge := by
  intro nu mass hmass hLaplace
  exact paperFiniteMeasureGaussianCDFApproximation_of_positiveMass
    hmass hLaplace (hpositive nu mass hmass hLaplace)

/-- Compact-window positive lower bound for the exact finite-p void factor.
This is a direct consequence of M3 and P1, with no additional spectral
assumption. -/
theorem eventually_exactVoidFactor_ge_pos_of_M3_P1
    (m : ℕ → ℕ) (R : (p : ℕ) → LogdetLean.CorrelationMatrix p)
    (hM3 : MovingMatrixM3 m R)
    (hP1 : PaperLiteralAggregateOneEdgeApproximation m R) :
    ∀ L : ℝ, 0 ≤ L → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ p in atTop, ∀ x : ℝ, |x| ≤ L →
        c ≤ Real.exp (-movingPaperExactExceedanceIntensity m R p x) := by
  intro L hL
  obtain ⟨B, _hB, hbound⟩ :=
    paperExactExceedanceIntensityCompactBound_of_M3_P1 m R hM3 hP1 L hL
  refine ⟨Real.exp (-B), Real.exp_pos _, ?_⟩
  filter_upwards [hbound] with p hp
  intro x hx
  exact Real.exp_le_exp.mpr (neg_le_neg (hp x hx))

/-- The same hypotheses, together with the decorated Laplace approximation,
show that the actual decorated finite measure also has mass uniformly
bounded away from zero. This justifies probability normalization on every
fixed compact height window. -/
theorem eventually_leadingVoidMeasure_mass_ge_pos_of_M3_P1_laplace
    (m : ℕ → ℕ) (R : (p : ℕ) → LogdetLean.CorrelationMatrix p)
    (hM3 : MovingMatrixM3 m R)
    (hP1 : PaperLiteralAggregateOneEdgeApproximation m R)
    (hLaplace : PaperLeadingVoidLaplaceApproximation m R) :
    ∀ L : ℝ, 0 ≤ L → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ p in atTop, ∀ x : ℝ, |x| ≤ L →
        c ≤ (movingPaperLeadingVoidMeasure m R p x : Measure ℝ).real univ := by
  intro L hL
  obtain ⟨c, hc, htarget⟩ :=
    eventually_exactVoidFactor_ge_pos_of_M3_P1 m R hM3 hP1 L hL
  let nu : ℕ → ℝ → FiniteMeasure ℝ := movingPaperLeadingVoidMeasure m R
  let mass : ℕ → ℝ → ℝ := fun p x ↦
    Real.exp (-movingPaperExactExceedanceIntensity m R p x)
  have hlapAbstract :
      LogdetLean.FiniteMeasureGaussianLaplaceApproximation nu mass := by
    intro L' U hL' hU epsilon hepsilon
    filter_upwards [hLaplace L' U hL' hU epsilon hepsilon] with p hp
    intro v x hv hx
    simpa [nu, mass, movingPaperLeadingVoidMeasure_laplace] using hp v x hv hx
  have hhalf : 0 < c / 2 := half_pos hc
  have hmassApprox :=
    LogdetLean.finiteMeasureGaussianMassApproximation_of_laplace
      hlapAbstract L hL (c / 2) hhalf
  refine ⟨c / 2, hhalf, ?_⟩
  filter_upwards [htarget, hmassApprox] with p hpTarget hpMass
  intro x hx
  have htargetX := hpTarget x hx
  have hmassX := hpMass x hx
  dsimp only [nu, mass] at hmassX
  have hlower := (abs_lt.mp hmassX).1
  linarith

end

end LogdetLean.Coherence
