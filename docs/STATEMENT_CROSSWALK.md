# Paper-to-Lean statement crosswalk

Fresh statement review and local verification: 2026-09-13. The arXiv and PTRF
source archives have the same principal mathematical statements; their
formatting and some coverage prose differ.

The thirteen public wrappers are in [LogDetBerryEsseen.lean](../LogDetBerryEsseen.lean).
Their explicit target propositions are in [Challenge.lean](../Challenge.lean).
The original endpoints below remain available in namespace `LogdetLean`.
“Through proved bridge” means an exact finite equality of functions or laws,
not an asymptotic approximation.

| Paper result | Public wrapper | Original endpoint | Relation and scope |
|---|---|---|---|
| Proposition 4.1 | `beta_product` | [`map_centeredSampleCorrelationDet_succ_eq_map_product_betaFactors`](../LogdetLean/SampleCorrelationBeta.lean) | Through proved Gaussian sample/column law bridges. The first beta-product factor is a point mass at one. |
| Theorem 4.2: signed expansion | `null_edgeworth` | [`uniformNullEdgeworthTarget_proved`](../LogdetLean/NullUniformEdgeworthTarget.lean) | Through the proved sample-to-log-beta law and exact center, variance and third-cumulant identities. Signed CDF error, uniform in x. |
| Theorem 4.2: sharp equivalent | `null_sharp_kolmogorov` | [`tendsto_uniformActualNullSharpKolmogorov_relative_error_zero`](../LogdetLean/NullUniformEdgeworthTarget.lean) | Exact actual-sample formulation up to irrelevant initial indices; eventual admissibility removes the Gaussian fallback. |
| Theorem 5.1 | `general_correlation_leading` | [`paperTheoremFiveOne_exact`](../LogdetLean/GeneralRPaperExactTranslation.lean) | Exact. A single universal constant precedes all dimensions and all positive-definite correlation matrices; includes the rho bound. |
| Theorem 5.2: correlation | `general_correlation_full` | [`paperTheoremFiveTwo_exact`](../LogdetLean/GeneralRPaperExactTranslation.lean) | Exact. The type contains the literal iid N(mu,R) sample and both finite bounds. |
| Theorem 5.2: arbitrary covariance | `general_covariance_full` | [`paperTheoremFiveTwo_arbitraryCovariance_exact`](../LogdetLean/GeneralRPaperExactTranslation.lean) | Exact. Arbitrary mean and positive-definite covariance through its population correlation. |
| Proposition 6.1: equation (6.2) | `third_cumulant_equivalent` | [`tendsto_nullASeries_div_uniformScale`](../LogdetLean/NullAUniformAsymptotics.lean) | Exact sequential all-array equivalent, p tending to infinity. |
| Proposition 6.1: equation (6.3) | `growing_gap` | [`paperEquationSixThree_exact`](../LogdetLean/PaperTable2Endpoints.lean) | Exact. Includes finite tail bounds, d A_d tending to 4, and the growing-gap equivalent. |
| Proposition 6.1: equation (6.4) | `variance_equivalent` | [`tendsto_nullVSeries_div_uniformScale`](../LogdetLean/NullVUniformAsymptotics.lean) | Exact with the paper's eventual positive-gap condition. |
| Proposition 6.1: equation (6.5) | `square_variance` | [`tendsto_square_nullVSeries_sub_two_log`](../LogdetLean/NullRefinedAsymptotics.lean) | Exact square variance constant 2 gamma_E + pi^2/4. |
| Proposition 6.1: equation (6.6) | `hard_edge_constants` | [`paperEquationSixSix_exact`](../LogdetLean/PaperTable2Endpoints.lean) | Exact closed constant, recurrence and strict decrease in the gap. |
| Corollary 6.2: supremum | `square_supremum` | [`tendsto_scaledNullKolmogorovSup_closed`](../LogdetLean/NullSharpSupremum.lean) | Through the exact null-law bridge. The supremum is over every m >= p, including m=p. |
| Corollary 6.2: rational interval | `square_constant_decimal` | [`nullSharpSupremumConstant_decimal8`](../LogdetLean/NullSharpSupremumDecimal.lean) | Exact rational interval, not a floating-point assertion. |

## Model and normalization bridges

| Identification | Formal declaration and source |
|---|---|
| Literal iid Gaussian observations to canonical m-row residual model | `map_rawPearson_iidGaussian_succ_eq_canonicalResidual`, [OriginalGaussianPearsonReduction.lean](../LogdetLean/OriginalGaussianPearsonReduction.lean) |
| Pearson matrix equals the printed centered-scatter normalization | `paperGeneralRSampleCorrelation_eq_printedScatterFormula`, [GeneralRPaperExactTranslation.lean](../LogdetLean/GeneralRPaperExactTranslation.lean) |
| Standardized null sample statistic has the canonical beta-sum law | `map_Z0mpStatistic_eq_standardizedNullLaw`, [NullCenterStandardization.lean](../LogdetLean/NullCenterStandardization.lean) |
| Original general-correlation sample statistic has the canonical law | `map_paperGeneralRStatistic_iidGaussian_eq_ZRmpStatistic`, [GeneralRPaperExactTranslation.lean](../LogdetLean/GeneralRPaperExactTranslation.lean) |
| Moment center equals the finite digamma expression | `nullCenter_eq_nullCenterDigammaSeries`, [NullCenterStandardization.lean](../LogdetLean/NullCenterStandardization.lean) |
| Moment variance, third magnitude and skew scale equal the finite series | `nullVariance_eq_nullVSeries`, `nullThirdMagnitude_eq_nullASeries`, `nullSkewScale_eq_nullLambdaSeries`, [StandardizedCumulantBridge.lean](../LogdetLean/StandardizedCumulantBridge.lean) |

For the null model, the centered standard Gaussian column law is identified
with the row-based iid realization through `map_dataColumns_standardGaussianDataMeasure`
and `map_nestedTupleToFin_nestedProductMeasure`. Location and positive marginal
scales cancel under the original Gaussian Pearson reduction.

The 36-declaration audit includes the eight model/normalization declarations
listed above as well as all principal results and the two conditional variance
wrappers. Full types and axiom lists are in the fresh receipts.

## Items outside the unconditional principal boundary

- Equation (3.1) quotes the Heiny–Johnston–Prochno literature result and is not a principal formal endpoint.
- Equation (6.1) defines `hardEdgeAConstant`; it is not an extra theorem.
- Equations (5.14)–(5.15), interpreted as statements about actual variance, require the scalar Kibble probability identification. The deterministic coefficient-series statements are proved.
- A complete fresh equation-by-equation coverage ledger is not established here. The supplied supplement contains further proposed routes, which should not be conflated with the thirteen principal endpoints.

See [Assumptions and gaps](ASSUMPTIONS_AND_GAPS.md) for the exact conditional hypothesis and the recommended correction to the manuscript's coverage wording.
