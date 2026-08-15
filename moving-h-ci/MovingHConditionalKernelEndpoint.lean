import LogdetLean.Coherence.MovingHCDF

open MeasureTheory Filter ProbabilityTheory
open scoped Topology

namespace LogdetLean.Coherence

/--
Axiom-free kernel endpoint for the moving-`H` paper theorem.

The theorem exposes the remaining probabilistic boundary as the explicit CDF
residual convergence proposition already defined in `MovingHCDF`.  No project
axiom is introduced: supplying a proof of that proposition yields the exact
moving-accompanying joint CDF law checked by Lean.
-/
theorem paperTheorem_movingAccompanying_from_explicit_cdf_residual
    {m p nu : ℕ → ℕ} {H : ℝ} {sR : ℕ → ℝ}
    (hSeq : MovingHHighDimSequence m p nu)
    (hResidual : MovingHCDFResidualConvergence m p nu H sR hSeq) :
    MovingHCDFCompanionLaw m p nu H sR hSeq := by
  exact movingHCDFCompanionLaw_of_residual hResidual

#print axioms paperTheorem_movingAccompanying_from_explicit_cdf_residual

end LogdetLean.Coherence
