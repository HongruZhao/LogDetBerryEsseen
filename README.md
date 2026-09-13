# Sharp Berry–Esseen Bounds for Gaussian Correlation Log Determinants

Lean 4 formalization of the thirteen principal results in *Sharp Berry–Esseen Bounds for the Log Determinant of a Gaussian Sample Correlation Matrix*, by Hongru Zhao.

The principal results use only Lean's standard foundations: `propext`, `Classical.choice`, and `Quot.sound`. They have no project-specific axioms or unfinished proofs. The optional exact variance identity for general population correlation still requires an explicit scalar Kibble limit hypothesis; it is outside the principal theorem boundary.

## The results

Let $\widehat R$ be the Pearson correlation matrix of $n$ independent Gaussian observations in dimension $p$, with $m=n-1\ge p\ge2$.

Under population correlation $R=I_p$, define

$$
Z_{0,m,p}=\frac{\log\det\widehat R-b_{m,p}}{\sqrt{V_{m,p}}},
\qquad
\lambda_{m,p}=\frac{A_{m,p}}{V_{m,p}^{3/2}},
$$

where $b_{m,p}$ and $V_{m,p}$ are the exact mean and variance, and $A_{m,p}$ is minus the third cumulant. The development proves the signed first Edgeworth expansion and the sharp equivalent

$$
d_K(Z_{0,m,p},N(0,1))\sim\frac{\lambda_{m,p}}{6\sqrt{2\pi}}
$$

uniformly over all integers $m\ge p$ as $p\to\infty$. It also proves

$$
\lim_{p\to\infty}(\log p)^{3/2}\sup_{m\ge p}d_K(Z_{0,m,p},N(0,1))
=\frac{4\pi^2/3+7\zeta(3)}{24\sqrt\pi},
$$

with the constant in $(0.50715638,0.50715639)$.

For every positive-definite population correlation matrix $R$, put

$$
a_R=\operatorname{tr}((R-I_p)^2),\quad
s_R^2=V_{m,p}+2a_R/m,\quad
Z_R=\frac{\log\det\widehat R-\log\det R-b_{m,p}}{s_R}.
$$

The general-correlation result gives a universal constant $C$ such that

$$
d_K(Z_R,N(0,1))\le C\{\lambda_{m,p}+p^{-1}+\rho_R+Q_R^{1/3}\}
\le C'\{\lambda_{m,p}+p^{-1/3}\},
$$

where $\rho_R=\operatorname{tr}|R-I_p|^3/(m^2s_R^3)$ and $Q_R=4(p+a_R)/(m^2s_R^2)$. No uniform eigenvalue bounds are imposed on $R$. This general-correlation estimate is an upper bound; sharpness is established for the null results above.

## Main declarations

The public entry file is [LogDetBerryEsseen.lean](LogDetBerryEsseen.lean), in namespace `LogDetBerryEsseen`. [Challenge.lean](Challenge.lean) spells out its thirteen target propositions without introducing axioms or proof placeholders.

| Paper result | Public declaration |
|---|---|
| Proposition 4.1: beta product | `beta_product` |
| Theorem 4.2: signed expansion and sharp equivalent | `null_edgeworth`, `null_sharp_kolmogorov` |
| Theorem 5.1: leading term | `general_correlation_leading` |
| Theorem 5.2: full statistic | `general_correlation_full`, `general_covariance_full` |
| Proposition 6.1: uniform cumulant and variance equivalents | `third_cumulant_equivalent`, `growing_gap`, `variance_equivalent` |
| Proposition 6.1: square variance and hard-edge constants | `square_variance`, `hard_edge_constants` |
| Corollary 6.2: supremum and rational constant interval | `square_supremum`, `square_constant_decimal` |

All original `LogdetLean` declaration names remain available. The [statement crosswalk](docs/STATEMENT_CROSSWALK.md) records the exact source locations and the proved Gaussian sample, centering, scaling, and equality-of-laws bridges.

## Assumptions and the remaining gap

The main results assume the Gaussian model, positive-definite population covariance/correlation, and the stated dimension or asymptotic conditions. These are mathematical hypotheses, distinct from foundational axioms.

The separate [conditional variance module](LogdetLean/ConditionalVariance.lean) proves the optional variance identity **assuming** `KibbleScalarLimitCertificate` for the off-diagonal pairs. It supplies the three Wishart moment inputs already proved in the original development. A proof of the remaining scalar limit is still needed for an unconditional exact-variance endpoint. The main results do not import this new conditional module or require that certificate.

See [Assumptions and gaps](docs/ASSUMPTIONS_AND_GAPS.md). This repository does not certify every equation, prose argument, literature claim, or application in the manuscript.

## Building and verification

The project pins Lean `4.33.0-rc2` and Mathlib commit `641fbd329d4ffb62bef83c51f54088469056bd36`. With [Elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get
lake build
lake env lean Verification.lean
```

For the source scan, dependency checks, 36 named axiom reports, imported-closure sorry audit, and ten module checks with `leanchecker`:

```sh
bash scripts/verify.sh
```

The original source and the updated entry files passed local builds on 2026-09-13. All 36 named axiom reports contain only the three standard foundations, and the imported closure is sorry-free. The build retains 21 pre-existing linter warnings. Exact receipts and the distinction between rebuilt project proofs and reused pinned dependency caches are in [Verification](docs/VERIFICATION.md).

`Challenge.lean` reuses the existing formal definitions and imports. It is a statement interface, not an independent semantic formalization. Comparator and Nanoda have not been run for this project.

## Provenance and citation

The presentation follows [PrimeGaps186](https://github.com/openai/PrimeGaps186) and [NavierStokesAndEuler](https://github.com/openai/NavierStokesAndEuler). Their mathematical results, assumptions, licenses, and verification receipts are not transferred to this project.

The original 138 Lean source files are unchanged from the supplied v1.1.2 archive. See [provenance](docs/PROVENANCE.md), [release notes](docs/RELEASE_NOTES.md), and [CITATION.cff](CITATION.cff). The original capsule is identified in the supplied paper by [DOI 10.5281/zenodo.21898548](https://doi.org/10.5281/zenodo.21898548); that DOI does not identify this source revision. Historical ZIPs remain available in [archives](archives/README.md).

Project contributions retain [GPL-3.0-only](LICENSE). Dependencies retain their own licenses.
