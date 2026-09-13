import LogdetLean.PaperTable2Endpoints

/-!
# Statements of the thirteen principal paper results

These proposition definitions specify the targets proved in
`LogDetBerryEsseen.lean`. They contain neither proof placeholders nor new
axioms. The existing definitions of the Gaussian model, its statistics, and
the analytic scales are reused; this is a readable statement interface, not
an independently developed Comparator challenge. See
`docs/STATEMENT_CROSSWALK.md` for the model-identification bridges.

The optional general-correlation exact variance identity is deliberately
separate: its scalar Kibble limit remains a hypothesis.
-/

namespace LogDetBerryEsseen.Challenge

open LogdetLean Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

noncomputable section

/-- Proposition 4.1: centered Gaussian Pearson determinant as an independent
beta product. The first formal factor is a point mass at one. -/
def betaProduct : Prop :=
  ∀ m p : ℕ, p ≤ m →
    Measure.map (centeredSampleCorrelationDet (m + 1) p)
        (nestedProductMeasure (stdGaussian (ObservationSpace (m + 1))) p) =
      Measure.map (nestedRealProduct p)
        (nestedProductMeasureFamily (gaussianGramSchmidtFactorMeasure m) p)

/-- Theorem 4.2, signed expansion: along every eventually admissible array,
the uniform CDF remainder divided by the standardized third cumulant vanishes. -/
def nullEdgeworth : Prop :=
  ∀ mseq : ℕ → ℕ,
    (∀ᶠ p in atTop, Admissible (mseq p) p) →
      Tendsto (fun p ↦ nullEdgeworthError (mseq p) p /
        nullSkewScale (mseq p) p) atTop (nhds 0)

/-- Theorem 4.2, sharp equivalent for the actual centered sample. The
Gaussian fallback applies only outside eventual admissibility. -/
def nullSharpKolmogorov : Prop :=
  ∀ mseq : ℕ → ℕ,
    (∀ᶠ p in atTop, Admissible (mseq p) p) →
      Tendsto (fun p ↦
        |kolmogorovDistance (actualZ0mpMeasureOrGaussian (mseq p) p)
            (gaussianReal 0 1) -
          nullLambdaSeries (mseq p) p / (6 * Real.sqrt (2 * Real.pi))| /
          nullLambdaSeries (mseq p) p) atTop (nhds 0)

/-- Theorem 5.1: one universal constant, with only the paper's dimension
and positive-definite correlation-matrix conditions. -/
def generalCorrelationLeading : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {m p : ℕ}, Admissible m p → ∀ R : CorrelationMatrix p,
      kolmogorovDistance
          (Measure.map (fun z ↦ GeneralRDecomposition.M_R m R z /
            generalRProxyScale m R) (standardGaussianDataMeasure m p))
          (gaussianReal 0 1) ≤ C * generalRPaperLeadingRate m R ∧
      generalRSpectralCubicRate m R ≤ generalRPaperRhoSimpleBound m

/-- Theorem 5.2: both bounds for the literal iid Gaussian sample, with
empirical centering and Pearson normalization. -/
def generalCorrelationFull : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {m p : ℕ}, Admissible m p →
      ∀ (mu : CorrelationMatrix.Observation p) (R : CorrelationMatrix p),
        kolmogorovDistance
            (Measure.map (paperGeneralRStatistic m R)
              (paperIidGaussianCorrelationSampleMeasure m mu R))
            (gaussianReal 0 1) ≤ C * generalRPaperFullRate m R ∧
        kolmogorovDistance
            (Measure.map (paperGeneralRStatistic m R)
              (paperIidGaussianCorrelationSampleMeasure m mu R))
            (gaussianReal 0 1) ≤
          C * (nullLambdaSeries m p + generalRDimensionCubeRootRate p)

/-- Theorem 5.2 in the model section's arbitrary covariance parametrization. -/
def generalCovarianceFull : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {m p : ℕ}, Admissible m p →
      ∀ (mu : CorrelationMatrix.Observation p) (Sigma : CovarianceMatrix p),
        kolmogorovDistance
            (Measure.map (paperGeneralRStatistic m Sigma.correlation)
              (iidGaussianDataMeasureWithMean (m + 1) mu Sigma))
            (gaussianReal 0 1) ≤ C * generalRPaperFullRate m Sigma.correlation ∧
        kolmogorovDistance
            (Measure.map (paperGeneralRStatistic m Sigma.correlation)
              (iidGaussianDataMeasureWithMean (m + 1) mu Sigma))
            (gaussianReal 0 1) ≤
          C * (nullLambdaSeries m p + generalRDimensionCubeRootRate p)

/-- Proposition 6.1, equation (6.2): the all-array third-cumulant equivalent. -/
def thirdCumulantEquivalent : Prop :=
  ∀ mseq pseq : ℕ → ℕ, Tendsto pseq atTop atTop →
    (∀ᶠ n in atTop, Admissible (mseq n) (pseq n)) →
      Tendsto (fun n ↦ nullASeries (mseq n) (pseq n) /
        nullAUniformScale (mseq n) (pseq n)) atTop (nhds 1)

/-- Proposition 6.1, equation (6.3): explicit hard-edge tail bounds and
the growing-gap equivalent. -/
def growingGap : Prop :=
  (∀ d : ℕ, 1 ≤ d →
    4 / ((d + 1 : ℕ) : ℝ) ≤ hardEdgeAConstant d ∧
      hardEdgeAConstant d ≤ 4 / (d : ℝ) + 8 / (d : ℝ) ^ 2) ∧
  Tendsto (fun d : ℕ ↦ (d : ℝ) * hardEdgeAConstant d) atTop (nhds 4) ∧
  ∀ mseq pseq : ℕ → ℕ, Tendsto pseq atTop atTop →
    (∀ᶠ n in atTop, Admissible (mseq n) (pseq n)) →
    Tendsto (fun n ↦ mseq n - pseq n) atTop atTop →
      Tendsto (fun n ↦ nullASeries (mseq n) (pseq n) /
        nullAGrowingScale (mseq n) (pseq n)) atTop (nhds 1)

/-- Proposition 6.1, equation (6.4): the variance equivalent requires an
eventually positive gap. Equation (6.5) treats the square case separately. -/
def varianceEquivalent : Prop :=
  ∀ mseq pseq : ℕ → ℕ, Tendsto pseq atTop atTop →
    (∀ᶠ n in atTop, Admissible (mseq n) (pseq n)) →
    (∀ᶠ n in atTop, 1 ≤ mseq n - pseq n) →
      Tendsto (fun n ↦ nullVSeries (mseq n) (pseq n) /
        nullVUniformScale (mseq n) (pseq n)) atTop (nhds 1)

/-- Proposition 6.1, equation (6.5): the square variance constant. -/
def squareVariance : Prop :=
  Tendsto (fun p : ℕ ↦ nullVSeries p p - 2 * Real.log (p : ℝ)) atTop
    (nhds (2 * Real.eulerMascheroniConstant + Real.pi ^ 2 / 4))

/-- Proposition 6.1, equation (6.6): value, recurrence and strict decrease. -/
def hardEdgeConstants : Prop :=
  hardEdgeAConstant 0 = 4 * Real.pi ^ 2 / 3 + 7 * realZetaThree ∧
  (∀ d : ℕ, hardEdgeAConstant d = hardEdgeAConstant 0 +
    ∑ k ∈ Finset.Icc 1 d, -negPsiTwoSeries ((k : ℝ) / 2)) ∧
  StrictAnti hardEdgeAConstant

/-- Corollary 6.2: the constrained supremum over all `m ≥ p`. -/
def squareSupremum : Prop :=
  Tendsto scaledNullKolmogorovSup atTop
    (nhds (squareAConstant / (24 * Real.sqrt Real.pi)))

/-- Corollary 6.2: the certified rational interval for the constant. -/
def squareConstantDecimal : Prop :=
  (50715638 : ℝ) / 100000000 < nullSharpSupremumConstant ∧
    nullSharpSupremumConstant < (50715639 : ℝ) / 100000000

end
end LogDetBerryEsseen.Challenge
