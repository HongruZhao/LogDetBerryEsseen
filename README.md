# Sharp Berry–Esseen Bounds for Gaussian Correlation Log Determinants

Lean 4 proofs of the main results in *Sharp Berry–Esseen Bounds for the Log Determinant of a Gaussian Sample Correlation Matrix*, by Hongru Zhao.

The public development has **three theorems**. Read their [statements](Challenge.lean) and [proof entry points](LogDetBerryEsseen.lean).

**Version v1.1.4:** the [full formalization on Zenodo](https://doi.org/10.5281/zenodo.22739087) covers all 243 manuscript inventory entries through 288 audited endpoints. This repository presents the three main results below. The [matching GitHub release](https://github.com/HongruZhao/LogDetBerryEsseen/releases/tag/v1.1.4) includes the exact same Lean ZIP; see the [version correspondence](docs/ZENODO_RELEASE.md).

## Main results

Let $\widehat R$ be the Pearson correlation matrix of $n$ independent Gaussian observations in dimension $p$, with $m=n-1\ge p\ge2$. Write $b_{m,p}$, $V_{m,p}$, and $-A_{m,p}$ for the exact null mean, variance, and third cumulant, and set $\lambda_{m,p}=A_{m,p}/V_{m,p}^{3/2}$.

### 1. Sharp null approximation — Theorem 4.2

For population correlation $R=I_p$, define

$$
Z_{0,m,p}=\frac{\log\det\widehat R-b_{m,p}}{\sqrt{V_{m,p}}}.
$$

The signed first Edgeworth expansion holds, and

$$
d_K(Z_{0,m,p},N(0,1))\sim\frac{\lambda_{m,p}}{6\sqrt{2\pi}}
$$

uniformly over all integers $m\ge p$ as $p\to\infty$.

Lean: `LogDetBerryEsseen.sharp_null`.

### 2. General-correlation bound — Theorem 5.2

For any positive-definite population correlation matrix $R$, define $s_R>0$ by

$$
s_R^2=V_{m,p}+\frac{2}{m}\mathrm{tr}((R-I_p)^2),
$$

$$
Z_R=\frac{\log\det\widehat R-\log\det R-b_{m,p}}{s_R}.
$$

A universal constant $C$ satisfies

$$
d_K(Z_R,N(0,1))\le C(\lambda_{m,p}+p^{-1/3}).
$$

The formal theorem includes the finer matrix-dependent bound and allows arbitrary Gaussian mean and positive-definite covariance. It imposes no uniform eigenvalue bounds on $R$.

Lean: `LogDetBerryEsseen.general_correlation`.

### 3. Sharp worst-case constant — Corollary 6.2

$$
\lim_{p\to\infty}(\log p)^{3/2}\sup_{m\ge p}d_K(Z_{0,m,p},N(0,1))
=\frac{4\pi^2/3+7\zeta(3)}{24\sqrt\pi}.
$$

Lean: `LogDetBerryEsseen.worst_case`.

## Check the proofs

The project pins Lean `4.33.0-rc2` and its Mathlib revision. With [Elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get
lake build
lake env lean Verification.lean
```

For the complete source and kernel checks, run `bash scripts/verify.sh`. See the [verification record](docs/VERIFICATION.md).

All three public theorems use only `propext`, `Classical.choice`, and `Quot.sound`, with no project-specific axioms or unfinished proofs. The supporting library contains the proof dependencies of these results. The [paper-to-Lean map](docs/STATEMENT_CROSSWALK.md) and [scope report](docs/ASSUMPTIONS_AND_GAPS.md) explain the models and the boundary of this formalization.

## Citation and license

See [CITATION.cff](CITATION.cff) and [provenance](docs/PROVENANCE.md). Earlier source material is preserved in [archives](archives/README.md). Project contributions are licensed under [GPL-3.0-only](LICENSE).

## Acknowledgments

We thank OpenAI for sharing [PrimeGaps186](https://github.com/openai/PrimeGaps186). This repository follows its organization and separation of theorem statements, proofs, and verification.
