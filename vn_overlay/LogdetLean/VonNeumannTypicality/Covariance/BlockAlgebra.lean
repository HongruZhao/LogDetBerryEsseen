import Mathlib.Data.Matrix.Block
import Mathlib.Tactic

/-!
# Block algebra for the reduced Gaussian covariance

This file kernel-checks the finite-dimensional matrix identities behind
Equations (13)--(17) of the manuscript.  The spectral interpretation of the
resulting square is deliberately kept separate.
-/

open Matrix

namespace LogdetLean.VonNeumannTypicality

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The standard symplectic form in the manuscript's `(q,p)` ordering. -/
def manuscriptSymplecticForm : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  Matrix.fromBlocks 0 1 (-1) 0

/-- The real block matrix associated with a complex matrix whose real and
imaginary parts are `A` and `C`.  This is the matrix `M_U` in Equation (13). -/
def covarianceCoupling (A C : Matrix n n ℝ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  Matrix.fromBlocks A C C (-A)

/-- Equation (16), at the matrix-algebra level: the square of `M_U` is
the realification-shaped block matrix associated with the product `B B⋆`.
The separate statement that its eigenvalues are the squared singular values,
each repeated twice, is a spectral theorem and is isolated elsewhere. -/
theorem covarianceCoupling_sq (A C : Matrix n n ℝ) :
    (covarianceCoupling A C) ^ 2 =
      Matrix.fromBlocks (A * A + C * C) (A * C - C * A)
        (C * A - A * C) (A * A + C * C) := by
  simp [covarianceCoupling, pow_two, Matrix.fromBlocks_multiply]
  noncomm_ring

/-- Equation (15): the symplectic form anticommutes with the covariance
coupling block. -/
theorem manuscriptSymplecticForm_mul_covarianceCoupling
    (A C : Matrix n n ℝ) :
    manuscriptSymplecticForm * covarianceCoupling A C =
      -(covarianceCoupling A C * manuscriptSymplecticForm) := by
  simp [manuscriptSymplecticForm, covarianceCoupling,
    Matrix.fromBlocks_multiply]

/-- The standard symplectic form squares to minus the identity. -/
theorem manuscriptSymplecticForm_sq :
    manuscriptSymplecticForm * manuscriptSymplecticForm =
      -(1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
  simp [manuscriptSymplecticForm, Matrix.fromBlocks_multiply]

/-- Abstract anticommuting-square identity underlying Equation (17).  It is
stated for an arbitrary real matrix pair so that the proof does not depend on
a spectral theorem. -/
theorem symplectic_covariance_square
    (Ω M : Matrix (n ⊕ n) (n ⊕ n) ℝ) (c d : ℝ)
    (hΩsq : Ω * Ω = -(1 : Matrix (n ⊕ n) (n ⊕ n) ℝ))
    (hanti : Ω * M = -(M * Ω)) :
    (Ω * (c • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) + d • M)) ^ 2 =
      -(c ^ 2) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) +
        d ^ 2 • (M ^ 2) := by
  simp only [pow_two, mul_add, mul_smul, mul_one]
  noncomm_ring [hΩsq, hanti]

/-- Equation (17) before multiplying by `i`: `(Ωσ)^2=-c^2 I+d^2M^2`. -/
theorem manuscript_omega_covariance_square
    (A C : Matrix n n ℝ) (c d : ℝ) :
    (manuscriptSymplecticForm *
      (c • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) +
        d • covarianceCoupling A C)) ^ 2 =
      -(c ^ 2) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) +
        d ^ 2 • (covarianceCoupling A C) ^ 2 := by
  exact symplectic_covariance_square manuscriptSymplecticForm
    (covarianceCoupling A C) c d manuscriptSymplecticForm_sq
    (manuscriptSymplecticForm_mul_covarianceCoupling A C)

end

end LogdetLean.VonNeumannTypicality
