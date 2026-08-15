import LogdetLean.Coherence.MovingHEasyConsequences
import LogdetLean.Coherence.MovingHMDPerturbationDischarge
import Mathlib.Tactic

/-!
# Axiom-free conditional endpoint for the moving-H theorem

The paper's finite-dimensional algebra, one-edge moderate-deviation analysis,
tail bookkeeping, and final CDF assembly are kernel checked elsewhere. The
remaining genuinely high-dimensional probability statement and the
finite-measure transform-to-CDF statement are kept here as explicit theorem
hypotheses rather than project axioms.

The strongest endpoint in this file uses only the two direct scalar
obligations consumed by the final CDF proof:

* `PaperDirectMaximumVoidApproximation`;
* `PaperDirectGaussianVoidDecoupling`.

A second endpoint reconstructs the former two-boundary route from a leading
void Laplace approximation and a finite-measure Curtiss bridge. The literal
one-edge approximation is not an external input: it is derived from M1--M3 by
`paperLiteralAggregateOneEdgeApproximation_of_M1_M3`.
-/

namespace LogdetLean.Coherence

open Filter MeasureTheory ProbabilityTheory Set

noncomputable section

/-- The remaining paper-specific high-dimensional Wishart input. It contains
only the unnormalized real-Laplace approximation of the leading logdet
coordinate on the literal maximum-void event. The one-edge intensity theorem
is already kernel verified from M1--M3 and is therefore not a field here. -/
structure PaperHighDimensionalWishartInput
    (m : ℕ → ℕ) (R : (p : ℕ) → LogdetLean.CorrelationMatrix p) : Prop where
  leadingVoidLaplace : PaperLeadingVoidLaplaceApproximation m R

/-- Zero real tilt in the unnormalized Laplace estimate is exactly the
ordinary maximum void probability. -/
theorem movingPaperLeadingVoidLaplaceTransform_zero_eq_countVoid
    (m : ℕ → ℕ) (R : (p : ℕ) → LogdetLean.CorrelationMatrix p)
    (p : ℕ) (x : ℝ) :
    movingPaperLeadingVoidLaplaceTransform m R p 0 x =
      (LogdetLean.standardGaussianDataMeasure (m p) p).real
        (movingPaperVoidEvent m R p x) := by
  unfold movingPaperLeadingVoidLaplaceTransform
  simp only [zero_mul, Real.exp_zero]
  rw [show (∫ w,
      if movingPaperExceedanceCount m R p x w = 0 then (1 : ℝ) else 0
      ∂LogdetLean.standardGaussianDataMeasure (m p) p) =
      ∫ w, (movingPaperVoidEvent m R p x).indicator (fun _ ↦ (1 : ℝ)) w
      ∂LogdetLean.standardGaussianDataMeasure (m p) p by
        apply integral_congr_ae
        filter_upwards [] with w
        by_cases hw : movingPaperExceedanceCount m R p x w = 0 <;>
          simp [movingPaperVoidEvent, Set.indicator, hw]]
  rw [integral_indicator (measurableSet_movingPaperVoidEvent m R p x),
    integral_const, measureReal_restrict_apply_univ]
  simp

/-- The unnormalized real-Laplace void approximation contains the scalar
maximum law at zero tilt. -/
theorem paperMaximumVoidApproximationExactIntensity_of_leadingLaplace
    (m : ℕ → ℕ) (R : (p : ℕ) → LogdetLean.CorrelationMatrix p)
    (hLaplace : PaperLeadingVoidLaplaceApproximation m R) :
    PaperMaximumVoidApproximationExactIntensity m R := by
  intro L hL epsilon hepsilon
  have hpTwo : ∀ᶠ p : ℕ in atTop, 2 ≤ p :=
    eventually_atTop.2 ⟨2, fun _ hp ↦ hp⟩
  filter_upwards [hLaplace L 1 hL (by norm_num) epsilon hepsilon, hpTwo]
    with p hp hp2
  intro x hx
  have hzero := hp 0 x (by norm_num) hx
  rw [movingPaperLeadingVoidLaplaceTransform_zero_eq_countVoid] at hzero
  norm_num at hzero
  rw [movingPaperMaximumCDF_eq_countVoid m R hp2 x]
  exact hzero

/-- Strongest axiom-free paper-facing endpoint. M1 is carried by the
`CorrelationMatrix` type. The two direct probability estimates are ordinary
hypotheses in the theorem type; there is no project axiom or opaque
certificate. -/
theorem paperTheorem_movingAccompanying_from_M1_M4_and_direct_components
    (m : ℕ → ℕ) (R : (p : ℕ) → LogdetLean.CorrelationMatrix p)
    (hdimension : MovingMatrixDimensionCondition m)
    (hM2 : MovingMatrixM2 m R)
    (hM3 : MovingMatrixM3 m R)
    (hMaximumVoid : PaperDirectMaximumVoidApproximation m R)
    (hGaussianVoid : PaperDirectGaussianVoidDecoupling m R) :
    MovingMatrixPaperTheorem m R := by
  exact paperTheorem_movingAccompanying_of_directCDFCore m R
    hdimension hM2 hM3 (movingMatrixM4_of_dimension m R hdimension)
      { maximumVoid := hMaximumVoid, gaussianVoid := hGaussianVoid }

/-- Structure-valued form of the same minimal conditional endpoint. -/
theorem paperTheorem_movingAccompanying_from_M1_M4_and_directCDFCore
    (m : ℕ → ℕ) (R : (p : ℕ) → LogdetLean.CorrelationMatrix p)
    (hdimension : MovingMatrixDimensionCondition m)
    (hM2 : MovingMatrixM2 m R)
    (hM3 : MovingMatrixM3 m R)
    (hcore : MovingMatrixPaperDirectCDFCore m R) :
    MovingMatrixPaperTheorem m R := by
  exact paperTheorem_movingAccompanying_of_directCDFCore m R
    hdimension hM2 hM3 (movingMatrixM4_of_dimension m R hdimension) hcore

/-- Complete direct CDF core from the two explicit analytic boundaries. P1
is discharged internally from M1--M3, and the nonlinear logdet remainder is
discharged from the dimension condition. -/
theorem movingMatrixPaperDirectCDFCore_of_explicitBoundaries
    (m : ℕ → ℕ) (R : (p : ℕ) → LogdetLean.CorrelationMatrix p)
    (hdimension : MovingMatrixDimensionCondition m)
    (hM2 : MovingMatrixM2 m R)
    (hM3 : MovingMatrixM3 m R)
    (hinput : PaperHighDimensionalWishartInput m R)
    (hCurtiss : PaperFiniteMeasureCurtissBridge) :
    MovingMatrixPaperDirectCDFCore m R := by
  have hP1 : PaperLiteralAggregateOneEdgeApproximation m R :=
    paperLiteralAggregateOneEdgeApproximation_of_M1_M3
      m R hdimension hM2 hM3
  exact
    { maximumVoid := paperDirectMaximumVoidApproximation_of_exactIntensity m R
        (paperMaximumVoidApproximationExactIntensity_of_leadingLaplace
          m R hinput.leadingVoidLaplace)
        hP1
      gaussianVoid := paperDirectGaussianVoidDecoupling_of_leading m R
        (paperLeadingGaussianVoidDecoupling_of_exactIntensity m R
          (paperLeadingJointVoidApproximationExactIntensity_of_curtiss
            m R hCurtiss hinput.leadingVoidLaplace)
          (paperMaximumVoidApproximationExactIntensity_of_leadingLaplace
            m R hinput.leadingVoidLaplace))
        (paperLogdetLeadingRemainderNegligible_of_dimension
          m R hdimension) }

/-- Axiom-free reconstruction of the former two-boundary endpoint. The
high-dimensional leading-void Laplace approximation and the finite-measure
Curtiss theorem are explicit arguments. -/
theorem paperTheorem_movingAccompanying_from_M1_M4_and_explicit_boundaries
    (m : ℕ → ℕ) (R : (p : ℕ) → LogdetLean.CorrelationMatrix p)
    (hdimension : MovingMatrixDimensionCondition m)
    (hM2 : MovingMatrixM2 m R)
    (hM3 : MovingMatrixM3 m R)
    (hinput : PaperHighDimensionalWishartInput m R)
    (hCurtiss : PaperFiniteMeasureCurtissBridge) :
    MovingMatrixPaperTheorem m R := by
  exact paperTheorem_movingAccompanying_from_M1_M4_and_directCDFCore
    m R hdimension hM2 hM3
      (movingMatrixPaperDirectCDFCore_of_explicitBoundaries
        m R hdimension hM2 hM3 hinput hCurtiss)

/-- Literal M1--M4 signature with the direct CDF core still visible. -/
theorem paperTheorem_movingAccompanying_from_explicit_M1_M4_and_directCDFCore
    (m : ℕ → ℕ) (R : (p : ℕ) → LogdetLean.CorrelationMatrix p)
    (hdimension : MovingMatrixDimensionCondition m)
    (hM2 : MovingMatrixM2 m R)
    (hM3 : MovingMatrixM3 m R)
    (hM4 : MovingMatrixM4 m R)
    (hcore : MovingMatrixPaperDirectCDFCore m R) :
    MovingMatrixPaperTheorem m R :=
  paperTheorem_movingAccompanying_of_directCDFCore
    m R hdimension hM2 hM3 hM4 hcore

end

end LogdetLean.Coherence
