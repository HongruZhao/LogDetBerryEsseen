# Scope, assumptions, and gaps

## Scope of this version

The public interface covers Theorem 4.2, Theorem 5.2, and Corollary 6.2.
The reviewed Lean statements match those paper results, directly or through
proved finite identities between the sample model and the analytic model.
The [statement map](STATEMENT_CROSSWALK.md) identifies those bridges.

The three results have no additional unproved analytic certificate in their
types. They use only the standard foundations `propext`, `Classical.choice`,
and `Quot.sound`; the complete imported declaration closure is sorry-free.
An axiom audit checks foundational dependencies. It does not remove ordinary
mathematical hypotheses from a theorem.

## Mathematical assumptions

- `Admissible m p` means `2 ≤ p ∧ p ≤ m`, with sample size `n = m + 1`.
- The observations have literal iid multivariate Gaussian laws. The general
  theorem allows arbitrary mean and positive-definite covariance.
- A population correlation matrix is real positive definite with diagonal one.
  There are no uniform eigenvalue bounds or unspecified spectral conditions.
- The statistic uses empirical centering and Pearson normalization. The exact
  null centering and scaling are identified by proved moment identities.
- Null asymptotics require eventual admissibility as the dimension tends to
  infinity. A formal Gaussian fallback at inadmissible indices has no effect
  on these eventual statements.

The formal definitions of logarithms and division are total. The relevant
positivity, nonsingularity, and normalization facts are proved in the library.

## Full formalization and the historical variance gap

In the original v1.1.2 development, the optional coefficient-series identity for the actual
**general-correlation variance**, equation (5.14), was conditional on
`KibbleScalarLimitCertificate`: the expanding-window covariance integral must
converge to the proposed coefficient series. That code proved its
limit was the actual covariance, but did not identify that limit with the
series without the extra hypothesis.

The [published full v1.1.4 archive](https://doi.org/10.5281/zenodo.22739087)
now proves that scalar identification and the actual exact variance identity
without an extra analytic certificate. All 38 previously outstanding inventory
entries are completed there. The archive contains 243 verified inventory entries
and 288 audited endpoints, including the full statement crosswalk and the
supplement sources with corrections marked in blue.

This focused repository continues to expose three main results. The older
conditional modules remain in [the historical archive](../archives/v1.1.3-retired)
as provenance, outside the active build. Historical audit reports describe their
dated source snapshots; they are not the current status of the full archive.

The variance **bounds** have a separate direct actual-covariance route in
[KibbleCovarianceBounds.lean](../LogdetLean/KibbleCovarianceBounds.lean).
They do not need the coefficient-series identity. The historical gap did not
affect the bound in Theorem 5.2.
The elementary covariance algebra needed for this route is retained in
[GeneralRVarianceBasics.lean](../LogdetLean/GeneralRVarianceBasics.lean).

## Limits of the review

The GitHub interface covers the three listed main statements and their model
bridges. The expanded equation-by-equation inventory belongs to the separate
full Zenodo ZIP, not to this reduced interface. Its revised supplement clarifies
the nondegenerate domain of the joint density and corrects the Gaussian tail
bound at the prescribed cutoff; all changes are marked in blue. The main paper
and numbered display bodies are unchanged.

The verification claim concerns the encoded mathematical statements under their
stated model and domain hypotheses. It does not certify prose, bibliographic
attribution, novelty claims, or open problems. Comparator and Nanoda have not
been run; `Challenge.lean` reuses the supporting library's definitions. See the
[version correspondence](ZENODO_RELEASE.md) for the exact source relationship.
