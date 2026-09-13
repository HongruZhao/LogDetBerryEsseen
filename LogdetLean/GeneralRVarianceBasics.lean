import LogdetLean.GeneralRFrullaniLaplace
import LogdetLean.GeneralRNonlinearRemainder
import LogdetLean.NullVA

/-!
# Covariance algebra used by the general-correlation bound

These definitions and proofs are extracted from the original covariance and
variance modules. Only the unconditional ingredients used by the main proof
are included here.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Interval

/-- Pure covariance algebra behind the exact `tau_R^2` formula.  It cleanly
separates the finite-sum calculation from the three model-specific inputs:
the determinant variance, its covariance with each log radius, and the pair
log-radius covariance. -/
theorem variance_sub_finsetSum_eq_base_add_offDiag
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (L : Ω → ℝ) (q : ι → Ω → ℝ) (V t : ℝ) (c : ι → ι → ℝ)
    (hL : MemLp L 2 μ) (hq : ∀ i, MemLp (q i) 2 μ)
    (hvarL : Var[L; μ] = V + (Fintype.card ι : ℝ) * t)
    (hcovL : ∀ i, cov[L, q i; μ] = t)
    (hcovQ : ∀ i j,
      cov[q i, q j; μ] = if i = j then t else c i j) :
    Var[fun ω ↦ L ω - ∑ i, q i ω; μ] =
      V + ∑ i : ι, ∑ j : ι with i ≠ j, c i j := by
  have hsum : MemLp (fun ω ↦ ∑ i, q i ω) 2 μ :=
    memLp_finsetSum Finset.univ (fun i _ ↦ hq i)
  rw [variance_fun_sub hL hsum, covariance_fun_sum_right hq hL,
    variance_fun_sum hq, hvarL]
  simp_rw [hcovL, hcovQ]
  have hfilter (i : ι) : Finset.univ.filter (fun j ↦ i = j) = {i} := by
    ext j
    simp [eq_comm]
  simp_rw [Finset.sum_ite]
  simp_rw [hfilter]
  simp_rw [Finset.sum_add_distrib]
  simp [mul_comm]
  ring

/-- The same variance proxy `s_R^2=V_{m,p}+2a_R/m` used in the paper. -/
def generalRSeriesVarianceProxy {p : ℕ} (m : ℕ)
    (R : CorrelationMatrix p) : ℝ :=
  generalRVarianceProxy m (nullVSeries m p) R.deviationEnergy

/-- The compact Frullani window whose limit is the Kibble covariance. -/
def kibbleWindowIntegral (m : ℕ) (rho : ℝ) (n : ℕ) : ℝ :=
  ∫ s in (1 / ((n : ℝ) + 1))..((n : ℝ) + 1),
    ∫ t in (1 / ((n : ℝ) + 1))..((n : ℝ) + 1),
      GeneralRDecomposition.weightedPairCovarianceKernel m rho s t

/-- The actual diagonal log-radius covariance is already closed, without the
scalar Kibble limit, by the exact Gamma log-variance theorem. -/
theorem covariance_log_Q_self_eq_trigamma
    {m p : ℕ} (hm : 0 < m) (R : CorrelationMatrix p) (i : Fin p) :
    cov[fun z ↦ Real.log (GeneralRDecomposition.Q R z i),
        fun z ↦ Real.log (GeneralRDecomposition.Q R z i);
        standardGaussianDataMeasure m p] =
      trigammaSeries ((m : ℝ) / 2) := by
  rw [covariance_self]
  · exact GeneralRDecomposition.variance_log_Q_eq_trigamma hm R i
  · exact (GeneralRDecomposition.measurable_Q R i).log.aemeasurable

/-- The uncentered random numerator whose variance is denoted `tau_R^2`.
Adding population and expectation constants does not change its variance. -/
def generalRLogDetNumerator {m p : ℕ} (R : CorrelationMatrix p) :
    GaussianData m p → ℝ := fun z ↦
  Real.log (GeneralRDecomposition.W0 z).det -
    ∑ i : Fin p, Real.log (GeneralRDecomposition.Q R z i)

end

end LogdetLean
