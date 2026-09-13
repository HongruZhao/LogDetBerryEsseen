import Challenge

/-!
# Main results

The three public theorems correspond to Theorem 4.2, Theorem 5.2, and
Corollary 6.2 of the paper. Their explicit statements are in `Challenge.lean`;
the supporting proofs are in `LogdetLean/`.
-/

namespace LogDetBerryEsseen

/-- Uniform null Edgeworth expansion and sharp Kolmogorov equivalent. -/
theorem sharp_null : Challenge.sharpNull :=
  ⟨LogdetLean.uniformNullEdgeworthTarget_proved,
   LogdetLean.tendsto_uniformActualNullSharpKolmogorov_relative_error_zero⟩

/-- General-correlation Berry–Esseen bounds for an iid Gaussian sample. -/
theorem general_correlation : Challenge.generalCorrelation :=
  LogdetLean.paperTheoremFiveTwo_arbitraryCovariance_exact

/-- Sharp worst-case asymptotic constant over every admissible sample size. -/
theorem worst_case : Challenge.worstCase :=
  LogdetLean.tendsto_scaledNullKolmogorovSup_closed

end LogDetBerryEsseen
