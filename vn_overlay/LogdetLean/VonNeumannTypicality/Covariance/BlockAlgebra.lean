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
  rw [covarianceCoupling, pow_two, Matrix.fromBlocks_multiply]
  apply Matrix.fromBlocks_inj.mpr
  constructor
  · rfl
  constructor
  · noncomm_ring
  constructor
  · noncomm_ring
  · noncomm_ring

/-- Equation (15): the symplectic form anticommutes with the covariance
coupling block. -/
theorem manuscriptSymplecticForm_mul_covarianceCoupling
    (A C : Matrix n n ℝ) :
    manuscriptSymplecticForm * covarianceCoupling A C =
      -(covarianceCoupling A C * manuscriptSymplecticForm) := by
  rw [manuscriptSymplecticForm, covarianceCoupling,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_neg]
  apply Matrix.fromBlocks_inj.mpr
  simp

/-- The standard symplectic form squares to minus the identity. -/
theorem manuscriptSymplecticForm_sq :
    manuscriptSymplecticForm * manuscriptSymplecticForm =
      -(1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [manuscriptSymplecticForm, Matrix.fromBlocks_multiply, Matrix.one_apply]

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
  have hanti' : M * Ω = -(Ω * M) := by
    simpa using (congrArg Neg.neg hanti).symm
  have hleft : Ω * (Ω * M) = -M := by
    rw [← mul_assoc, hΩsq]
    simp
  have hright : (Ω * M) * Ω = M := by
    calc
      (Ω * M) * Ω = Ω * (M * Ω) := mul_assoc _ _ _
      _ = Ω * (-(Ω * M)) := by rw [hanti']
      _ = -(Ω * (Ω * M)) := by simp
      _ = -(-M) := by rw [hleft]
      _ = M := neg_neg M
  have hquad : (Ω * M) * (Ω * M) = M * M := by
    calc
      (Ω * M) * (Ω * M) = ((Ω * M) * Ω) * M :=
        (mul_assoc (Ω * M) Ω M).symm
      _ = M * M := by rw [hright]
  have hlinear :
      Ω * (c • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) + d • M) =
        c • Ω + d • (Ω * M) := by
    simp [mul_add, mul_smul]
  have hA2 :
      (c • Ω) * (c • Ω) =
        -(c * c) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
    rw [smul_mul, mul_smul, hΩsq]
    simp [smul_smul]
  have hAB :
      (c • Ω) * (d • (Ω * M)) = -(c * d) • M := by
    rw [smul_mul, mul_smul, hleft]
    simp [smul_smul]
  have hBA :
      (d • (Ω * M)) * (c • Ω) = (c * d) • M := by
    rw [smul_mul, mul_smul, hright]
    simp [smul_smul, mul_comm]
  have hB2 :
      (d • (Ω * M)) * (d • (Ω * M)) = (d * d) • (M * M) := by
    rw [smul_mul, mul_smul, hquad]
    simp [smul_smul]
  rw [hlinear, pow_two, add_mul, mul_add, mul_add]
  rw [hA2, hAB, hBA, hB2]
  abel

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
