import LogdetLean.Coherence.MovingHDirectCDFPath

/-!
# Conditional kernel endpoint for the moving-`H_p` paper theorem

The original M1--M4-only claim requires two paper-specific uniform probability
estimates that are not presently derived in Mathlib.  This module exposes those
estimates as ordinary theorem hypotheses instead of project axioms.

The two additional hypotheses are exactly

* `PaperDirectMaximumVoidApproximation`, the compact-window Poisson-void
  approximation for the literal maximum;
* `PaperDirectGaussianVoidDecoupling`, the compact-window and uniform-in-`z`
  Gaussian--void decoupling estimate.

M1 is carried by the type `CorrelationMatrix`.  M2, M3, M4, and the dimension
condition occur explicitly in the theorem signature.  No fixed limit of the
moving shift or moving slope measure is assumed.
-/

namespace LogdetLean.Coherence

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

/--
Kernel-verified form of the moving Gaussian--Poisson CDF/void law under M1--M4
and the two explicit analytic conditions D1--D2.

This theorem contains no project axiom and no opaque certificate.  Its proof
is the final CDF assembly from `MovingHDirectCDFPath`.
-/
theorem paperTheorem_movingAccompanying_from_M1_M4_D1_D2
    (m : ℕ → ℕ) (R : (p : ℕ) → LogdetLean.CorrelationMatrix p)
    (hdimension : MovingMatrixDimensionCondition m)
    (hM2 : MovingMatrixM2 m R)
    (hM3 : MovingMatrixM3 m R)
    (hM4 : MovingMatrixM4 m R)
    (hD1 : PaperDirectMaximumVoidApproximation m R)
    (hD2 : PaperDirectGaussianVoidDecoupling m R) :
    MovingMatrixPaperTheorem m R := by
  exact paperTheorem_movingAccompanying_of_directCDFCore m R
    hdimension hM2 hM3 hM4
    { maximumVoid := hD1
      gaussianVoid := hD2 }

/-- Descriptive alias for the same M1--M4 plus D1--D2 endpoint. -/
theorem paperTheorem_movingAccompanying_from_explicit_direct_obligations
    (m : ℕ → ℕ) (R : (p : ℕ) → LogdetLean.CorrelationMatrix p)
    (hdimension : MovingMatrixDimensionCondition m)
    (hM2 : MovingMatrixM2 m R)
    (hM3 : MovingMatrixM3 m R)
    (hM4 : MovingMatrixM4 m R)
    (hMaximum : PaperDirectMaximumVoidApproximation m R)
    (hDecoupling : PaperDirectGaussianVoidDecoupling m R) :
    MovingMatrixPaperTheorem m R := by
  exact paperTheorem_movingAccompanying_from_M1_M4_D1_D2
    m R hdimension hM2 hM3 hM4 hMaximum hDecoupling

/-- Structure-valued version of the same conditional endpoint. -/
theorem paperTheorem_movingAccompanying_from_direct_core
    (m : ℕ → ℕ) (R : (p : ℕ) → LogdetLean.CorrelationMatrix p)
    (hdimension : MovingMatrixDimensionCondition m)
    (hM2 : MovingMatrixM2 m R)
    (hM3 : MovingMatrixM3 m R)
    (hM4 : MovingMatrixM4 m R)
    (hcore : MovingMatrixPaperDirectCDFCore m R) :
    MovingMatrixPaperTheorem m R := by
  exact paperTheorem_movingAccompanying_of_directCDFCore m R
    hdimension hM2 hM3 hM4 hcore

end

end LogdetLean.Coherence
