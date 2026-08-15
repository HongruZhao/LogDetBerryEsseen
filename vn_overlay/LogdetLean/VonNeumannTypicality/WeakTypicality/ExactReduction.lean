import LogdetLean.VonNeumannTypicality.WeakTypicality.VariableDimension

/-!
# Exact-identification transfers for weak typicality

The physical entropy and the singular-value statistic are equal once the
Gaussian covariance/symplectic-spectrum calculation is available.  This file
proves the corresponding probability transfer without introducing any axiom.
The identification is an explicit theorem parameter.
-/

open Filter MeasureTheory

namespace LogdetLean.VonNeumannTypicality

noncomputable section

/-- Weak typicality is invariant under pointwise equality of triangular
statistics. -/
theorem weaklyTypical_congr
    {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (μ : (N : ℕ) → Measure (Ω N))
    (X Y : (N : ℕ) → Ω N → ℝ) (m : ℕ → ℝ)
    (hXY : ∀ N ω, X N ω = Y N ω)
    (hY : WeaklyTypical μ Y m) :
    WeaklyTypical μ X m := by
  intro ε hε
  simpa only [relativeBadEvent, hXY] using hY ε hε

/-- Paper-facing conditional capstone.  Once the physical entropy has been
identified pointwise with the singular-value statistic and the regularized
statistic has been shown weakly typical, the unregularized physical entropy is
weakly typical for the actual varying subsystem dimension `k N`. -/
theorem weaklyTypical_physicalEntropy_of_regularized_singularValueStatistic
    {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    (μ : (N : ℕ) → Measure (Ω N))
    [∀ N, IsProbabilityMeasure (μ N)]
    (s : ℝ) (k : ℕ → ℕ)
    (tau : (N : ℕ) → Ω N → Fin (k N) → ℝ)
    (physicalEntropy : (N : ℕ) → Ω N → ℝ)
    (m : ℕ → ℝ)
    (hk : ∀ N, k N ≤ N)
    (htau0 : ∀ N ω i, 0 ≤ tau N ω i)
    (htau1 : ∀ N ω i, tau N ω i ≤ 1)
    (hm : Tendsto m atTop atTop)
    (hexact : ∀ N ω,
      physicalEntropy N ω = entropySpectralStatistic s (tau N ω))
    (hregularized : WeaklyTypical μ
      (fun N ω ↦ regularizedEntropySpectralStatistic s
        (inverseSquareCutoff N) (tau N ω)) m) :
    WeaklyTypical μ physicalEntropy m := by
  apply weaklyTypical_congr μ physicalEntropy
    (fun N ω ↦ entropySpectralStatistic s (tau N ω)) m hexact
  exact weaklyTypical_entropySpectralStatistic_of_regularized_variableDimension
    μ s k tau m hk htau0 htau1 hm hregularized

end

end LogdetLean.VonNeumannTypicality
