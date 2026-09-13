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

## Gap found in the broader original project

The optional exact coefficient-series identity for the actual
**general-correlation variance**, equation (5.14), was conditional on
`KibbleScalarLimitCertificate`: the expanding-window covariance integral must
converge to the proposed coefficient series. The original code proves its
limit is the actual covariance, but does not identify that limit with the
series without the extra hypothesis.

That conditional identity is outside the three main results. This focused
version excludes the certificate and the conditional identity modules from
its active source and import closure. Their unchanged sources are retained
in [the historical archive](../archives/v1.1.3-retired). The original statements can be inspected in
[the preserved earlier revision](https://github.com/HongruZhao/LogDetBerryEsseen/blob/ec41febe106f5b4c543bf908ff6e25764fe210bd/LogdetLean/KibbleCovarianceBridge.lean).
Removing them does not prove the missing scalar limit.

The variance **bounds** have a separate direct actual-covariance route in
[KibbleCovarianceBounds.lean](../LogdetLean/KibbleCovarianceBounds.lean).
They do not need the coefficient-series identity. Thus the unresolved exact
identity must not be confused with a missing bound in the proof of Theorem 5.2.
The elementary covariance algebra needed for this route is retained in
[GeneralRVarianceBasics.lean](../LogdetLean/GeneralRVarianceBasics.lean).

## Limits of the review

The supplied paper and source archives were compared on 2026-09-13. This is a
principal-statement and model-bridge review, supported by Lean builds and
kernel checks. It is not an independent line-by-line proof review or a
certification of every manuscript equation, application, citation, or novelty
claim. Comparator and Nanoda have not been run; `Challenge.lean` reuses the
supporting library's definitions.

The original abstract's claim about “All theoretical results” is too broad
for this focused repository. An accurate replacement is:

> Theorem 4.2, Theorem 5.2, and Corollary 6.2 have Lean 4 formulations with
> kernel-checked proofs under their stated hypotheses.

The supplied manuscript archives have not been edited.
