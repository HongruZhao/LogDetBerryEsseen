import Mathlib.Data.Matrix.Block
import Mathlib.Tactic

/-!
# Block algebra for the reduced Gaussian covariance

This file kernel-checks the finite-dimensional matrix identities behind
Equations (13)--(17) of the manuscript. The spectral interpretation of the
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
imaginary parts are `A` and `C`. This is the matrix `M_U` in Equation (13). -/
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

/-- Multiplying two scalar multiples of matrices factors both scalars. The
entrywise proof avoids a simplifier loop between `smul_mul` and `mul_smul`. -/
private theorem smul_mul_smul_matrix
    (a b : ℝ) (X Y : Matrix (n ⊕ n) (n ⊕ n) ℝ) :
    (a • X) * (b • Y) = (a * b) • (X * Y) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  calc
    (∑ x, (a * X i x) * (b * Y x j)) =
        ∑ x, (a * b) * (X i x * Y x j) := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = (a * b) * ∑ x, X i x * Y x j := by
      rw [Finset.mul_sum]

/-- Abstract anticommuting-square identity underlying Equation (17). It is
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
    simp [mul_add]
  have hA2 :
      (c • Ω) * (c • Ω) =
        -(c * c) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by
    calc
      (c • Ω) * (c • Ω) = (c * c) • (Ω * Ω) :=
        smul_mul_smul_matrix c c Ω Ω
      _ = (c * c) • (-(1 : Matrix (n ⊕ n) (n ⊕ n) ℝ)) := by rw [hΩsq]
      _ = -(c * c) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) := by simp
  have hAB :
      (c • Ω) * (d • (Ω * M)) = -(c * d) • M := by
    calc
      (c • Ω) * (d • (Ω * M)) = (c * d) • (Ω * (Ω * M)) :=
        smul_mul_smul_matrix c d Ω (Ω * M)
      _ = (c * d) • (-M) := by rw [hleft]
      _ = -(c * d) • M := by simp
  have hBA :
      (d • (Ω * M)) * (c • Ω) = (c * d) • M := by
    calc
      (d • (Ω * M)) * (c • Ω) = (d * c) • ((Ω * M) * Ω) :=
        smul_mul_smul_matrix d c (Ω * M) Ω
      _ = (d * c) • M := by rw [hright]
      _ = (c * d) • M := by rw [mul_comm d c]
  have hB2 :
      (d • (Ω * M)) * (d • (Ω * M)) = (d * d) • (M * M) := by
    calc
      (d • (Ω * M)) * (d • (Ω * M)) =
          (d * d) • ((Ω * M) * (Ω * M)) :=
        smul_mul_smul_matrix d d (Ω * M) (Ω * M)
      _ = (d * d) • (M * M) := by rw [hquad]
  rw [hlinear, pow_two, add_mul, mul_add, mul_add]
  rw [hA2, hAB, hBA, hB2]
  simp only [pow_two]
  change
    (-(c * c)) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) +
        ((-(c * d)) • M + ((c * d) • M + (d * d) • (M * M))) =
      (-(c * c)) • (1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) +
        (d * d) • (M * M)
  simp [add_assoc]

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
