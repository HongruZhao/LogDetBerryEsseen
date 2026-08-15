#!/usr/bin/env python3
"""Apply the first unconditional finite-measure Curtiss reduction lemma.

This script patches the complete moving-H handoff reconstructed by CI.  It is
idempotent and refuses to continue when the expected source marker is absent.
"""

from pathlib import Path
import sys


if len(sys.argv) != 2:
    raise SystemExit("usage: apply_curtiss_mass_patch.py PROJECT_ROOT")

root = Path(sys.argv[1])
bridge = root / "LogdetLean/Coherence/MovingHCurtissVoidBridge.lean"
audit = root / "LogdetLean/Coherence/MovingHCurtissVoidBridgeAxiomAudit.lean"

name = "paperFiniteMeasureGaussianMassApproximation_of_laplace"
marker = "/-- Uniform Gaussian CDF approximation for the same moving finite measures. -/"
lemma = r'''
/-- The real-Laplace approximation already controls the total mass, by
specializing the transform at zero.  This is the normalization step needed
before any probability-measure version of Curtiss can be applied. -/
theorem paperFiniteMeasureGaussianMassApproximation_of_laplace
    {nu : ℕ → ℝ → FiniteMeasure ℝ} {mass : ℕ → ℝ → ℝ}
    (hLaplace : PaperFiniteMeasureGaussianLaplaceApproximation nu mass) :
    ∀ L : ℝ, 0 ≤ L → ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ p in atTop, ∀ x : ℝ, |x| ≤ L →
        |(nu p x : Measure ℝ).real univ - mass p x| < epsilon := by
  intro L hL epsilon hepsilon
  filter_upwards [hLaplace L 1 hL (by norm_num) epsilon hepsilon]
    with p hp
  intro x hx
  have hzero := hp 0 x (by norm_num) hx
  simpa only [zero_mul, Real.exp_zero, zero_pow, zero_div, one_mul,
    integral_const, one_smul] using hzero

'''

text = bridge.read_text()
if name not in text:
    if marker not in text:
        raise SystemExit(f"expected insertion marker missing from {bridge}")
    bridge.write_text(text.replace(marker, lemma + marker, 1))

print_line = (
    "#print axioms "
    "LogdetLean.Coherence.paperFiniteMeasureGaussianMassApproximation_of_laplace"
)
audit_text = audit.read_text()
if print_line not in audit_text:
    audit.write_text(audit_text.rstrip() + "\n\n" + print_line + "\n")

print(f"patched {bridge}")
print(f"patched {audit}")
