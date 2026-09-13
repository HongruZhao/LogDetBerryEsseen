import LogdetLean

/-!
# Three main theorem statements

The Gaussian sample, Pearson statistic, and analytic scales use the definitions
in the supporting proof library. This is a readable statement interface;
`LogDetBerryEsseen.lean` supplies the proofs.
-/

namespace LogDetBerryEsseen.Challenge

open LogdetLean Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

/-- Theorem 4.2: the uniform signed first Edgeworth expansion and the sharp
Kolmogorov equivalent for the actual centered Gaussian sample. -/
def sharpNull : Prop :=
  (∀ mseq : ℕ → ℕ,
    (∀ᶠ p in atTop, Admissible (mseq p) p) →
      Tendsto (fun p ↦ nullEdgeworthError (mseq p) p /
        nullSkewScale (mseq p) p) atTop (nhds 0)) ∧
  (∀ mseq : ℕ → ℕ,
    (∀ᶠ p in atTop, Admissible (mseq p) p) →
      Tendsto (fun p ↦
        |kolmogorovDistance (actualZ0mpMeasureOrGaussian (mseq p) p)
            (gaussianReal 0 1) -
          nullLambdaSeries (mseq p) p / (6 * Real.sqrt (2 * Real.pi))| /
          nullLambdaSeries (mseq p) p) atTop (nhds 0))

/-- Theorem 5.2: both finite bounds for the literal iid Gaussian sample,
with arbitrary mean and positive-definite population covariance. -/
def generalCorrelation : Prop :=
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

/-- Corollary 6.2: the sharp asymptotic supremum over all sample sizes m ≥ p. -/
def worstCase : Prop :=
  Tendsto scaledNullKolmogorovSup atTop
    (nhds (squareAConstant / (24 * Real.sqrt Real.pi)))

end
end LogDetBerryEsseen.Challenge
