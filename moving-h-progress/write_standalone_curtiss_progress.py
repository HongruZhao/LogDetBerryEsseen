#!/usr/bin/env python3
"""Write an import-light, kernel-checkable Curtiss progress module.

The theorem statements are generic finite-measure facts. They can be
imported by the full moving-H handoff without depending on the large
Coherence import graph, which makes focused CI reliable.
"""

from pathlib import Path
import sys

if len(sys.argv) != 2:
    raise SystemExit("usage: write_standalone_curtiss_progress.py PROJECT_ROOT")

root = Path(sys.argv[1])
source = root / "LogdetLean/FiniteMeasureCurtissProgress.lean"
audit = root / "LogdetLean/FiniteMeasureCurtissProgressAxiomAudit.lean"

source.write_text(r'''import Mathlib

/-!
# Import-light progress toward the finite-measure Curtiss bridge

This module proves two unconditional reductions needed by the moving-H
finite-subprobability argument.

* Real-Laplace convergence at zero controls the total mass.
* Once the moving target mass is small, the desired CDF approximation is
  elementary and needs no transform-uniqueness theorem.

The remaining positive-mass branch is the genuine Curtiss/uniqueness step.
-/

namespace LogdetLean

open Filter MeasureTheory Set

noncomputable section

/-- Uniform real-Laplace approximation to a Gaussian MGF times a moving
finite-measure mass. -/
def FiniteMeasureGaussianLaplaceApproximation
    (nu : ℕ → ℝ → MeasureTheory.FiniteMeasure ℝ) (mass : ℕ → ℝ → ℝ) : Prop :=
  ∀ L U : ℝ, 0 ≤ L → 0 < U → ∀ epsilon : ℝ, 0 < epsilon →
    ∀ᶠ p in atTop, ∀ v x : ℝ, |v| ≤ U → |x| ≤ L →
      |∫ y, Real.exp (v * y) ∂(nu p x : Measure ℝ) -
        Real.exp (v ^ 2 / 2) * mass p x| < epsilon

/-- Specializing the real-Laplace approximation at zero gives uniform
control of the total mass. -/
theorem finiteMeasureGaussianMassApproximation_of_laplace
    {nu : ℕ → ℝ → MeasureTheory.FiniteMeasure ℝ} {mass : ℕ → ℝ → ℝ}
    (hLaplace : FiniteMeasureGaussianLaplaceApproximation nu mass) :
    ∀ L : ℝ, 0 ≤ L → ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ p in atTop, ∀ x : ℝ, |x| ≤ L →
        |(nu p x : Measure ℝ).real univ - mass p x| < epsilon := by
  intro L hL epsilon hepsilon
  filter_upwards [hLaplace L 1 hL (by norm_num) epsilon hepsilon]
    with p hp
  intro x hx
  have hzero := hp 0 x (by norm_num) hx
  simpa only [zero_mul, Real.exp_zero, pow_two, zero_div, one_mul,
    integral_const, smul_eq_mul, mul_one] using hzero

/-- The vanishing-mass branch of the finite-measure Curtiss conclusion is
purely order-theoretic. It uses only the mass estimate and the fact that the
comparison CDF factor lies in `[0,1]`. -/
theorem finiteMeasureCDFApproximation_of_small_mass
    {nu : ℕ → ℝ → MeasureTheory.FiniteMeasure ℝ} {mass : ℕ → ℝ → ℝ}
    {F : ℝ → ℝ}
    (hmass : ∀ p x, 0 ≤ mass p x)
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ 1)
    (hLaplace : FiniteMeasureGaussianLaplaceApproximation nu mass) :
    ∀ L : ℝ, 0 ≤ L → ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ p in atTop, ∀ z x : ℝ, |x| ≤ L → mass p x ≤ epsilon / 4 →
        |(nu p x : Measure ℝ).real (Iic z) - F z * mass p x| < epsilon := by
  intro L hL epsilon hepsilon
  have hquarter : 0 < epsilon / 4 := by linarith
  filter_upwards
      [finiteMeasureGaussianMassApproximation_of_laplace
        hLaplace L hL (epsilon / 4) hquarter]
      with p hp
  intro z x hx hsmall
  have hmassApprox := hp x hx
  have htotal : (nu p x : Measure ℝ).real univ < epsilon / 2 := by
    have hupper := (abs_lt.mp hmassApprox).2
    linarith
  have hIic0 : 0 ≤ (nu p x : Measure ℝ).real (Iic z) :=
    measureReal_nonneg
  have hIicLe :
      (nu p x : Measure ℝ).real (Iic z) ≤
        (nu p x : Measure ℝ).real univ :=
    measureReal_mono (subset_univ _)
  have hF0 : 0 ≤ F z := (hF z).1
  have hF1 : F z ≤ 1 := (hF z).2
  have hprod0 : 0 ≤ F z * mass p x :=
    mul_nonneg hF0 (hmass p x)
  have hprodLe : F z * mass p x ≤ mass p x :=
    mul_le_of_le_one_left (hmass p x) hF1
  rw [abs_lt]
  constructor <;> linarith

end

end LogdetLean
''')

audit.write_text(r'''import LogdetLean.FiniteMeasureCurtissProgress

#print axioms LogdetLean.finiteMeasureGaussianMassApproximation_of_laplace
#print axioms LogdetLean.finiteMeasureCDFApproximation_of_small_mass
''')

print(source)
print(audit)
