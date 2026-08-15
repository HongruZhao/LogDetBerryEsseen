import LogdetLean.FiniteMeasureCurtissProgress
import LogdetLean.Coherence.MovingHCurtissVoidBridge
import LogdetLean.Coherence.MovingHDirectBonferroniAssembly
import Mathlib.Tactic

/-!
# Positive-mass reduction for the moving-H Curtiss boundary

On every compact height window, M3 and the literal one-edge approximation
bound the exact finite-p exceedance intensity. Consequently the target void
factor is uniformly bounded away from zero. With the decorated Laplace
approximation, the actual decorated finite measure is also uniformly bounded
away from zero. Thus the model-specific Curtiss step never needs to normalize
a measure whose mass tends to zero.
-/

namespace LogdetLean.Coherence

open Filter MeasureTheory ProbabilityTheory Set

noncomputable section

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
