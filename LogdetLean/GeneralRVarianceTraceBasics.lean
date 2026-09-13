import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Deterministic variance and trace identities

This paper-specific module contains the four elementary declarations needed by
the general-correlation proof. They are proved directly from ordered-field
algebra and finite matrix identities.
-/

namespace LogdetLean

open scoped BigOperators

noncomputable section

/-- The normalizing variance used for the general-correlation leading term. -/
def generalRVarianceProxy (m : ℕ) (v a : ℝ) : ℝ :=
  v + 2 * a / (m : ℝ)

/-- The variance expression is nonnegative when both components are. -/
theorem generalRVarianceProxy_nonneg {m : ℕ} {v a : ℝ}
    (hv : 0 ≤ v) (ha : 0 ≤ a) :
    0 ≤ generalRVarianceProxy m v a := by
  unfold generalRVarianceProxy
  positivity

/-- An exact variance within four times a over m squared of the normalizing
variance has relative excess at most two over m. -/
theorem variance_proxy_relative_excess_le
    {m : ℕ} {v a tauSq : ℝ}
    (hm : 0 < m) (hv : 0 ≤ v) (ha : 0 ≤ a)
    (hlower : 0 ≤ tauSq - generalRVarianceProxy m v a)
    (hupper : tauSq - generalRVarianceProxy m v a ≤
      4 * a / (m : ℝ) ^ 2) :
    tauSq - generalRVarianceProxy m v a ≤
      (2 / (m : ℝ)) * generalRVarianceProxy m v a := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  by_cases ha0 : a = 0
  · subst a
    have hz : tauSq - generalRVarianceProxy m v 0 ≤ 0 := by
      simpa using hupper
    exact hz.trans (mul_nonneg (by positivity)
      (generalRVarianceProxy_nonneg hv (le_refl 0)))
  · have hproxy : 2 * a / (m : ℝ) ≤ generalRVarianceProxy m v a := by
      unfold generalRVarianceProxy
      linarith
    calc
      tauSq - generalRVarianceProxy m v a ≤ 4 * a / (m : ℝ) ^ 2 := hupper
      _ = (2 / (m : ℝ)) * (2 * a / (m : ℝ)) := by
        field_simp
        ring
      _ ≤ (2 / (m : ℝ)) * generalRVarianceProxy m v a := by
        gcongr

/-- If R=I+A and tr(A)=0, then tr(R^2)=card+tr(A^2). -/
theorem trace_one_add_square_of_trace_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (htrace : Matrix.trace A = 0) :
    Matrix.trace ((1 + A) * (1 + A)) =
      (Fintype.card ι : ℝ) + Matrix.trace (A * A) := by
  calc
    Matrix.trace ((1 + A) * (1 + A)) =
        Matrix.trace (1 + A + A + A * A) := by
      congr 1
      noncomm_ring
    _ = (Fintype.card ι : ℝ) + Matrix.trace (A * A) := by
      rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
        Matrix.trace_one, htrace]
      simp

end

end LogdetLean
