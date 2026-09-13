# Assumptions, axioms, and remaining formalization gaps

Audited against the supplied v1.1.2 Lean, arXiv, and PTRF archives on 2026-09-13.

## Assessment

The thirteen advertised endpoints have faithful statements for the principal paper results, either directly or through explicit proved model-identification bridges. A fresh build and fresh axiom reports passed. This is a statement-level and model-bridge audit; it is not an independent line-by-line mathematical review of every supporting proof or every manuscript equation.

The development does **not** establish every theoretical assertion in the paper without additional hypotheses. In particular, the optional exact general-correlation variance identification is still conditional.

## Foundational axioms

Fresh reports for the thirteen original endpoints and their thirteen public wrappers use exactly:

| Foundation | Role |
|---|---|
| `propext` | Propositional extensionality |
| `Classical.choice` | Classical choice |
| `Quot.sound` | Soundness of quotient identification |

No project axiom, `sorryAx`, or native-evaluation axiom appears in the 36 audited declaration reports. An environment-aware `#print sorries` reports that the full imported closure is sorry-free. A source scan of all 142 local Lean files found no proof placeholder, project axiom declaration, unsafe/native proof escape, or custom elaborator.

These findings do not turn a theorem of the form `P → Q` into a proof of `Q`. Ordinary hypotheses are visible in theorem types and are not entries in `#print axioms`.

## Statistical assumptions in the main endpoints

- `Admissible m p` means exactly `2 ≤ p ∧ p ≤ m`. There is no spectral condition or analytic certificate hidden in this predicate.
- `CorrelationMatrix p` consists of a real positive-definite matrix and the condition that each diagonal entry is one. Positive definiteness includes symmetry in the underlying Mathlib definition. The identity matrix is explicitly constructed as an example, so this type is inhabited.
- The original sample measure is the finite product of literal multivariate Gaussian laws with mean `mu` and covariance `Sigma` or `R`.
- The original sample statistic subtracts the empirical mean, forms the Pearson matrix, takes its log determinant, and uses the paper's exact finite centering and stated scale.
- The sample-to-residual bridge accounts for `n=m+1`, location invariance, and marginal-scale invariance.
- Asymptotic null statements require eventual admissibility, so indices 0 and 1 do not make the hypotheses impossible. The Gaussian fallback is used only outside that eventual admissible set.
- The variance equivalent involving `log(m/(m-p))` explicitly requires an eventually positive gap. The square case has a separate theorem.

`Real.log`, division, and normalization have total Lean definitions. The relevant admissible-sample positivity and nondegeneracy statements, and the normalization identities, are proved in the development; the displayed statistics are not arbitrary functions named after the paper's quantities.

## The concrete unresolved bridge

The optional identity in equation (5.14) identifies the actual variance with

$$
\tau_R^2=V_{m,p}+\sum_{i\ne j}c_m(r_{ij}).
$$

The deterministic coefficient series and its comparison with $s_R^2$ are proved. The remaining scalar condition is defined in [KibbleCovarianceBridge.lean](../LogdetLean/KibbleCovarianceBridge.lean):

```lean
def KibbleScalarLimitCertificate (m : ℕ) (rho : ℝ) : Prop :=
  Tendsto (kibbleWindowIntegral m rho) atTop
    (nhds (logRadiusCovarianceSeries m rho))
```

The integral is over compact windows expanding to the positive quadrant. The code proves convergence to the actual covariance of Gaussian log radii. It has not proved that the same limit equals the Kibble coefficient series.

The original assembly `variance_generalRLogDetNumerator_eq_exactVarianceSeries` also takes `hW`, `hvarW`, and `hcovW`. Their proofs are already present in [WishartLogDetMoments.lean](../LogdetLean/WishartLogDetMoments.lean):

| Assembly input | Existing proof |
|---|---|
| Square integrability of the log Wishart determinant | `memLp_log_det_W0_two` |
| Its exact variance | `variance_log_det_W0_eq_nullVSeries` |
| Its covariance with each log radius | `covariance_log_det_W0_log_Q_eq` |

The new [ConditionalVariance.lean](../LogdetLean/ConditionalVariance.lean) supplies those proofs and exposes two conditional endpoints whose only additional input is

```lean
hlimit : ∀ i j : Fin p, i ≠ j →
  KibbleScalarLimitCertificate m (R.val i j)
```

This improves the statement of the remaining obligation. It does not close the scalar analytic gap. Theorem 5.1 and Theorem 5.2 have no `hlimit` parameter and do not use this conditional identity to obtain their bounds. Their exact printed types and axiom reports are included in the fresh verification receipts.

## Other coverage limits

| Manuscript item | Current status |
|---|---|
| Thirteen principal endpoints | Proved under the stated paper hypotheses; model bridges reviewed |
| Optional actual variance identity and resulting actual-variance comparison | Conditional on the scalar Kibble limits |
| Cited Heiny–Johnston–Prochno bound, equation (3.1) | Outside the advertised formalization boundary |
| Every numbered equation and every regime/application statement | No complete fresh equation-by-equation audit established here |
| Informal proofs, literature priority, citations, and novelty | Not certified by the Lean build |
| Comparator/Nanoda independent checking | Not run for this project |

The original appendix and supplement already disclose the scalar certificate. The original README also excludes whole-paper equation coverage, but the abstract says “All theoretical results” have checked formulations. That wording should be narrowed to the principal results and should explicitly mention the conditional variance identity.

Suggested replacement for the abstract's formalization sentence:

> The principal results have exact or proved equivalent Lean 4 formulations whose declarations and dependencies are kernel checked. The optional exact variance identity remains conditional on a scalar Kibble limit certificate.

The arXiv appendix also says the capsule records a route for every numbered equation, whereas the capsule's own scope disclaims equation-by-equation coverage. Replace that claim with a reference to the explicit principal-statement crosswalk. These are proposed manuscript wording changes; the supplied manuscript archives have not been edited.
