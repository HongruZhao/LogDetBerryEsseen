# Statement crosswalk

This table is the complete paper-facing statement boundary. The relation
column uses only the required strict vocabulary:

- **Exact**: the Lean type is the paper statement after expanding notation
  and any finite equality-of-laws or pointwise bridge explicitly named below;
- **Equivalent through proved bridge**: the Lean type is stated on an exactly
  equivalent formal model, and the named Lean theorem proves the connection;
- **Partial**: only an identified part of the paper statement is covered; and
- **Not covered**: no advertised endpoint establishes the statement.

Every build and axiom status below was reproduced from a clean capsule copy
on 2026-08-12. The final archive is separately rechecked after extraction.

| Paper result | Paper location | Lean endpoint | Lean source file | Relation | Bridge, if any | Fresh build status | Axiom audit status | Notes |
|---|---|---|---|---|---|---|---|---|
| Proposition 4.1, independent beta product | Section 4.1, equation (4.2) | `map_centeredSampleCorrelationDet_succ_eq_map_product_betaFactors` | `LogdetLean/SampleCorrelationBeta.lean` | Exact | `map_rawPearson_iidGaussian_succ_eq_canonicalResidual`; `map_det_rawPearson_iidGaussian_succ_eq_canonicalResidual`; `map_dataColumns_standardGaussianDataMeasure`; `map_nestedTupleToFin_nestedProductMeasure` | PASS | PASS | The endpoint states the centered standard-Gaussian column law. The named finite bridges identify the paper's literal iid Gaussian sample and the canonical row/column realizations exactly. The first factor is a point mass at one, so the remaining factors are those indexed by `j=2,...,p`. |
| Theorem 4.2, uniform first Edgeworth expansion and sharp Kolmogorov equivalent | Section 4.2, equations (4.6) and (4.7) | `uniformNullEdgeworthTarget_proved`; `tendsto_uniformActualNullSharpKolmogorov_relative_error_zero` | `LogdetLean/NullUniformEdgeworthTarget.lean` | Exact | `map_Z0mpStatistic_eq_standardizedNullLaw`; `nullCenter_eq_nullCenterDigammaSeries`; `nullVariance_eq_nullVSeries`; `nullThirdMagnitude_eq_nullASeries`; `nullSkewScale_eq_nullLambdaSeries` | PASS | PASS | The first endpoint is the signed uniform expansion for the canonical standardized null law. The second directly states the actual-sample sharp equivalent. The finite equality of laws and normalization identities make the identification exact. |
| Theorem 5.1, general-correlation leading term | Section 5.2, equations (5.9) and (5.10) | `paperTheoremFiveOne_exact` | `LogdetLean/GeneralRPaperExactTranslation.lean` | Exact | None | PASS | PASS | Unfolding `generalRPaperLeadingRate`, `generalRSpectralCubicRate`, and `generalRPaperRhoSimpleBound` gives the displayed `lambda`, `1/p`, `rho_R`, and `2^{-3/2}m^{-1/2}` terms. The paper defines `M_R` on the same white-Wishart realization. |
| Theorem 5.2, general-correlation full statistic | Section 5.2, equations (5.11) and (5.12) | `paperTheoremFiveTwo_exact`; `paperTheoremFiveTwo_arbitraryCovariance_exact` | `LogdetLean/GeneralRPaperExactTranslation.lean` | Exact | The proof internally uses `map_paperGeneralRStatistic_literalCorrelation_eq_ZRmpStatistic` and `map_paperGeneralRStatistic_iidGaussian_eq_ZRmpStatistic` | PASS | PASS | The endpoint types themselves quantify over the literal `m+1` iid Gaussian sample and state both the detailed and dimension-only bounds. The second endpoint covers arbitrary covariance through its population correlation. |
| Proposition 6.1, uniform `A` and `V` equivalents | Section 6, equations (6.2) and (6.4) | `tendsto_nullASeries_div_uniformScale`; `tendsto_nullVSeries_div_uniformScale` | `LogdetLean/NullAUniformAsymptotics.lean`; `LogdetLean/NullVUniformAsymptotics.lean` | Exact | None | PASS | PASS | These are the sequential forms of the two uniform equivalents. The `V` theorem includes the required eventually positive gap. |
| Proposition 6.1, growing-gap third-cumulant form | Section 6, equation (6.3) | `paperEquationSixThree_exact` | `LogdetLean/PaperTable2Endpoints.lean` | Exact | `hardEdgeAConstant_tail_bounds`; `tendsto_gap_mul_hardEdgeAConstant`; `tendsto_growingGap_nullASeries_div_growingScale` | PASS | PASS | The endpoint exposes explicit two-sided finite bounds implying `A_d=4/d+O(d^{-2})`, the limit `d A_d -> 4`, and the exact sequential growing-gap equivalent `A_{m,p}~4p^2/(dm^2)`. |
| Proposition 6.1, square variance refinement | Section 6, equation (6.5) | `tendsto_square_nullVSeries_sub_two_log` | `LogdetLean/NullRefinedAsymptotics.lean` | Exact | None | PASS | PASS | This is exactly `V_{p,p}-2 log p -> 2 gamma_E + pi^2/4`. The Euler--Mascheroni constant enters only through mathlib's defining harmonic limit `Real.tendsto_harmonic_sub_log`. The proof derives the remaining `pi^2/4` correction from the exact finite trigamma series. |
| Proposition 6.1, hard-edge constants | Section 6, equation (6.6) | `paperEquationSixSix_exact` | `LogdetLean/PaperTable2Endpoints.lean` | Exact | `hardEdgeAConstant_zero_eq_squareAConstant`; `hardEdgeAConstant_eq_zero_add_negPsiTwoSum`; `hardEdgeAConstant_strictAnti` | PASS | PASS | The endpoint states the displayed square constant literally, the finite polygamma recurrence in the paper's sign convention, and strict decrease in the gap. |
| Corollary 6.2, sharp square supremum and decimal constant | Section 6, equations (6.7) and (6.8) | `tendsto_scaledNullKolmogorovSup_closed`; `nullSharpSupremumConstant_decimal8` | `LogdetLean/NullSharpSupremum.lean`; `LogdetLean/NullSharpSupremumDecimal.lean` | Exact | `map_Z0mpStatistic_eq_standardizedNullLaw`; `nullSharpSupremumConstant_eq_closed` | PASS | PASS | The supremum endpoint uses the canonical standardized null law, exactly equal in law to the printed statistic. The constant endpoint certifies the rational interval containing the displayed decimal. |

## Deliberately unadvertised statements

- Equation (3.1), the Heiny--Johnston--Prochno bound: **Not covered**. It is
  an external literature theorem.
- Equation (6.1) is a definition represented by `hardEdgeAConstant`; it is not
  a separate theorem endpoint. Equations (6.2)--(6.6) are now all represented
  in the public boundary.
- Any claim of equation-by-equation manuscript verification: **Not covered**.
