import LogdetLean.KibbleCovarianceBridge
import LogdetLean.WishartLogDetMoments

/-!
# Optional exact variance: the remaining hypothesis

The original assembly accepts square-integrability, determinant-variance,
determinant/radius-covariance, and scalar-limit inputs. The first three are
already proved in `WishartLogDetMoments`. These wrappers supply those proofs
and expose only the unresolved off-diagonal scalar Kibble limit.

Neither wrapper is an unconditional exact-variance theorem. Neither is used
by the thirteen principal results in `LogDetBerryEsseen.lean`.
-/

namespace LogdetLean

open MeasureTheory ProbabilityTheory

/-- Optional equation (5.14), conditional only on the scalar limit, after
discharging the already proved Wishart moment inputs. -/
theorem variance_generalRLogDetNumerator_eq_exactVarianceSeries_of_scalarLimits
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p)
    (hlimit : ∀ i j : Fin p, i ≠ j →
      KibbleScalarLimitCertificate m (R.val i j)) :
    Var[generalRLogDetNumerator R; standardGaussianDataMeasure m p] =
      generalRExactVarianceSeries m R := by
  have hm2 : 2 ≤ m := h.1.trans h.2
  have hm : 0 < m := by omega
  exact variance_generalRLogDetNumerator_eq_exactVarianceSeries hm R
    (memLp_log_det_W0_two hm h.2)
    (variance_log_det_W0_eq_nullVSeries hm h.2)
    (covariance_log_det_W0_log_Q_eq hm h.2 R) hlimit

/-- Optional actual-variance comparison, with the same unresolved scalar
limit explicitly retained as a hypothesis. -/
theorem variance_generalRLogDetNumerator_proxy_bounds_of_scalarLimits
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p)
    (hlimit : ∀ i j : Fin p, i ≠ j →
      KibbleScalarLimitCertificate m (R.val i j)) :
    0 ≤ Var[generalRLogDetNumerator R; standardGaussianDataMeasure m p] -
      generalRSeriesVarianceProxy m R ∧
    Var[generalRLogDetNumerator R; standardGaussianDataMeasure m p] -
      generalRSeriesVarianceProxy m R ≤ 4 * R.deviationEnergy / (m : ℝ) ^ 2 := by
  apply variance_proxy_bounds_of_eq_generalRExactVarianceSeries (h.1.trans h.2) R
  exact variance_generalRLogDetNumerator_eq_exactVarianceSeries_of_scalarLimits
    h R hlimit

end LogdetLean
