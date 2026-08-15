import LogdetLean.Coherence.MovingHDirectCDFPath

/-!
# Axiom-free direct endpoint for the moving-H theorem

The final moving Gaussian--Poisson CDF theorem is obtained from exactly the
two companion estimates used by the manuscript's terminal triangle
inequality:

* `PaperDirectMaximumVoidApproximation` (V1), and
* `PaperDirectGaussianVoidDecoupling` (V2).

Both are ordinary theorem hypotheses. This module declares no project axiom,
an opaque certificate, or hidden typeclass assumption. The stronger assertion
that M1--M4 alone imply V1 and V2 remains a conventional mathematical result,
not an end-to-end Lean theorem in this release.
-/

namespace LogdetLean.Coherence

noncomputable section

/-- Assemble the direct CDF core from the two literal companion estimates
V1 and V2. -/
theorem movingMatrixPaperDirectCDFCore_of_companionAssumptions
    (m : ℕ → ℕ) (R : (p : ℕ) → LogdetLean.CorrelationMatrix p)
    (hMaximumVoid : PaperDirectMaximumVoidApproximation m R)
    (hGaussianVoid : PaperDirectGaussianVoidDecoupling m R) :
    MovingMatrixPaperDirectCDFCore m R :=
  { maximumVoid := hMaximumVoid
    gaussianVoid := hGaussianVoid }

/-- Axiom-free paper-facing theorem under M1--M4 and the two explicit
companion assumptions V1--V2. M1 is carried by `CorrelationMatrix`. -/
theorem paperTheorem_movingAccompanying_from_explicit_M1_M4_V1_V2
    (m : ℕ → ℕ) (R : (p : ℕ) → LogdetLean.CorrelationMatrix p)
    (hdimension : MovingMatrixDimensionCondition m)
    (hM2 : MovingMatrixM2 m R)
    (hM3 : MovingMatrixM3 m R)
    (hM4 : MovingMatrixM4 m R)
    (hMaximumVoid : PaperDirectMaximumVoidApproximation m R)
    (hGaussianVoid : PaperDirectGaussianVoidDecoupling m R) :
    MovingMatrixPaperTheorem m R := by
  exact paperTheorem_movingAccompanying_of_directCDFCore
    m R hdimension hM2 hM3 hM4
      (movingMatrixPaperDirectCDFCore_of_companionAssumptions
        m R hMaximumVoid hGaussianVoid)

/-- Equivalent compact endpoint in which V1 and V2 are bundled as the direct
CDF core. -/
theorem paperTheorem_movingAccompanying_from_explicit_directCDFCore
    (m : ℕ → ℕ) (R : (p : ℕ) → LogdetLean.CorrelationMatrix p)
    (hdimension : MovingMatrixDimensionCondition m)
    (hM2 : MovingMatrixM2 m R)
    (hM3 : MovingMatrixM3 m R)
    (hM4 : MovingMatrixM4 m R)
    (hcore : MovingMatrixPaperDirectCDFCore m R) :
    MovingMatrixPaperTheorem m R := by
  exact paperTheorem_movingAccompanying_of_directCDFCore
    m R hdimension hM2 hM3 hM4 hcore

end

end LogdetLean.Coherence
