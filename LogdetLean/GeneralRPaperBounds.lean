import LogdetLean.WishartLeadingKolmogorov
import Mathlib.Tactic

/-!
# Paper-facing universal-constant bounds for general correlation matrices

The quantitative development naturally produces an explicit sum of four
costs.  This module absorbs their fixed numerical coefficients into one
universal constant and states exactly the two displays used in the paper:

* the leading-term bound by `lambda + 1/p + rho_R`; and
* the full-statistic bound with the additional `Q_R^(1/3)` term.

No new probability argument enters here; these are deterministic
consequences of `kolmogorovDistance_M_R_proxyScale_le` and
`kolmogorovDistance_ZRmpStatistic_le_finalRateEnvelope`.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory Real

/-- The dimensionless leading rate printed in the manuscript. -/
def generalRPaperLeadingRate {p : ℕ} (m : ℕ)
    (R : CorrelationMatrix p) : ℝ :=
  nullLambdaSeries m p + 1 / (p : ℝ) +
    generalRSpectralCubicRate m R

/-- The dimensionless full rate printed in the manuscript. -/
def generalRPaperFullRate {p : ℕ} (m : ℕ)
    (R : CorrelationMatrix p) : ℝ :=
  generalRPaperLeadingRate m R + generalRNonlinearCubeRootRate m R

/-- The dimension-only cube-root rate `p^(-1/3)` in the simplified display. -/
def generalRDimensionCubeRootRate (p : ℕ) : ℝ :=
  (1 / (p : ℝ)) ^ ((3 : ℝ)⁻¹)

/-- One explicit universal constant that absorbs every fixed coefficient in
the paper-facing bounds.  Its numerical optimization is irrelevant. -/
def generalRPaperUniversalConstant : ℝ :=
  100 * analyticLogNormalApproximationConstant +
    100 / Real.sqrt (2 * Real.pi) + 100

/-- A universal constant for the final simplified display. -/
def generalRPaperSimpleUniversalConstant : ℝ :=
  5 * generalRPaperUniversalConstant

theorem generalRPaperUniversalConstant_pos :
    0 < generalRPaperUniversalConstant := by
  unfold generalRPaperUniversalConstant
  have hC := analyticLogNormalApproximationConstant_ge_one
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
  positivity

theorem generalRPaperSimpleUniversalConstant_pos :
    0 < generalRPaperSimpleUniversalConstant := by
  unfold generalRPaperSimpleUniversalConstant
  positivity [generalRPaperUniversalConstant_pos]

private theorem one_div_pred_le_two_div
    {p : ℕ} (hp : 2 ≤ p) :
    1 / ((p : ℝ) - 1) ≤ 2 / (p : ℝ) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by positivity
  have hpred : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  apply (div_le_div_iff₀ hpred hp0).2
  linarith

private theorem generalRSpectralCubicRate_nonneg
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    0 ≤ generalRSpectralCubicRate m R := by
  have hm : 0 ≤ (m : ℝ) ^ 2 := sq_nonneg _
  have hs : 0 ≤ generalRProxyScale m R ^ 3 :=
    pow_nonneg (generalRProxyScale_pos h R).le _
  have hc : 0 ≤ ∑ i, |R.deviationEigenvalues i| ^ 3 := by
    exact Finset.sum_nonneg fun _ _ ↦ pow_nonneg (abs_nonneg _) _
  unfold generalRSpectralCubicRate generalRCubicRateRho
  exact div_nonneg hc (mul_nonneg hm hs)

private theorem generalRPaperLeadingRate_nonneg
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    0 ≤ generalRPaperLeadingRate m R := by
  have hlambda := (nullLambdaSeries_pos h).le
  have hp2 : 2 ≤ p := h.1
  have hp : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (show 0 < p by omega)
  have hrho := generalRSpectralCubicRate_nonneg h R
  unfold generalRPaperLeadingRate
  positivity

private theorem generalRPaperLeadingEnvelope_le
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    generalRLeadingNormalRate m R + generalRScaleMismatchRate p ≤
      generalRPaperUniversalConstant * generalRPaperLeadingRate m R := by
  have hp2 : 2 ≤ p := h.1
  have hpR : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (show 0 < p by omega)
  have hpred := one_div_pred_le_two_div hp2
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hfour : 4 / ((p : ℝ) - 1) ≤ 8 / (p : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hpred (show (0 : ℝ) ≤ 4 by norm_num)
    calc
      4 / ((p : ℝ) - 1) = 4 * (1 / ((p : ℝ) - 1)) := by ring
      _ ≤ 4 * (2 / (p : ℝ)) := hmul
      _ = 8 / (p : ℝ) := by ring
  have hscale : generalRScaleMismatchRate p ≤
      (8 / (p : ℝ)) / Real.sqrt (2 * Real.pi) := by
    unfold generalRScaleMismatchRate
    exact div_le_div_of_nonneg_right hfour hsqrt.le
  have hlambda := (nullLambdaSeries_pos h).le
  have hb : 0 ≤ 1 / (p : ℝ) := by positivity
  have hrho := generalRSpectralCubicRate_nonneg h R
  have hC : 0 ≤ analyticLogNormalApproximationConstant :=
    analyticLogNormalApproximationConstant_ge_one.trans' (by norm_num)
  let B := generalRPaperLeadingRate m R
  have hB : 0 ≤ B := generalRPaperLeadingRate_nonneg h R
  have hbB : 1 / (p : ℝ) ≤ B := by
    dsimp [B, generalRPaperLeadingRate]
    linarith
  have h38 : 38 / ((p : ℝ) - 1) ≤ 76 / (p : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hpred (show (0 : ℝ) ≤ 38 by norm_num)
    calc
      38 / ((p : ℝ) - 1) = 38 * (1 / ((p : ℝ) - 1)) := by ring
      _ ≤ 38 * (2 / (p : ℝ)) := hmul
      _ = 76 / (p : ℝ) := by ring
  have hinside :
      nullLambdaSeries m p + 38 / ((p : ℝ) - 1) +
          8 * generalRSpectralCubicRate m R ≤ 76 * B := by
    dsimp [B, generalRPaperLeadingRate]
    calc
      nullLambdaSeries m p + 38 / ((p : ℝ) - 1) +
          8 * generalRSpectralCubicRate m R ≤
          nullLambdaSeries m p + 76 / (p : ℝ) +
            8 * generalRSpectralCubicRate m R := by linarith
      _ ≤ 76 * nullLambdaSeries m p + 76 / (p : ℝ) +
          76 * generalRSpectralCubicRate m R := by
        exact add_le_add
          (add_le_add (by nlinarith : nullLambdaSeries m p ≤
            76 * nullLambdaSeries m p) le_rfl)
          (by nlinarith : 8 * generalRSpectralCubicRate m R ≤
            76 * generalRSpectralCubicRate m R)
      _ = 76 * (nullLambdaSeries m p + 1 / (p : ℝ) +
          generalRSpectralCubicRate m R) := by ring
  have hlead : generalRLeadingNormalRate m R ≤
      76 * analyticLogNormalApproximationConstant * B := by
    unfold generalRLeadingNormalRate generalRThirdDerivativeRate
    calc
      analyticLogNormalApproximationConstant *
          (nullLambdaSeries m p + 38 / ((p : ℝ) - 1) +
            8 * generalRSpectralCubicRate m R) ≤
          analyticLogNormalApproximationConstant * (76 * B) :=
        mul_le_mul_of_nonneg_left hinside hC
      _ = 76 * analyticLogNormalApproximationConstant * B := by ring
  have hsmall : (8 / (p : ℝ)) / Real.sqrt (2 * Real.pi) ≤
      (8 / Real.sqrt (2 * Real.pi)) * B := by
    have hcoef : 0 ≤ 8 / Real.sqrt (2 * Real.pi) := by positivity
    calc
      (8 / (p : ℝ)) / Real.sqrt (2 * Real.pi) =
          (8 / Real.sqrt (2 * Real.pi)) * (1 / (p : ℝ)) := by ring
      _ ≤ (8 / Real.sqrt (2 * Real.pi)) * B :=
        mul_le_mul_of_nonneg_left hbB hcoef
  have hconst :
      76 * analyticLogNormalApproximationConstant +
          8 / Real.sqrt (2 * Real.pi) ≤
        generalRPaperUniversalConstant := by
    unfold generalRPaperUniversalConstant
    have hC1 := analyticLogNormalApproximationConstant_ge_one
    have hinv : 0 ≤ 1 / Real.sqrt (2 * Real.pi) := by positivity
    rw [show 100 / Real.sqrt (2 * Real.pi) =
        100 * (1 / Real.sqrt (2 * Real.pi)) by ring,
      show 8 / Real.sqrt (2 * Real.pi) =
        8 * (1 / Real.sqrt (2 * Real.pi)) by ring]
    nlinarith
  calc
    generalRLeadingNormalRate m R + generalRScaleMismatchRate p ≤
        76 * analyticLogNormalApproximationConstant * B +
          (8 / Real.sqrt (2 * Real.pi)) * B :=
      add_le_add hlead (hscale.trans hsmall)
    _ = (76 * analyticLogNormalApproximationConstant +
          8 / Real.sqrt (2 * Real.pi)) * B := by ring
    _ ≤ generalRPaperUniversalConstant * B :=
      mul_le_mul_of_nonneg_right hconst hB

/-- Exact paper display for the leading term, with a concrete universal
constant and the proxy scale `s_R`. -/
theorem kolmogorovDistance_M_R_proxyScale_le_paperRate
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    kolmogorovDistance
        (Measure.map
          (fun z ↦ GeneralRDecomposition.M_R m R z /
            generalRProxyScale m R)
          (standardGaussianDataMeasure m p))
        (gaussianReal 0 1) ≤
      generalRPaperUniversalConstant * generalRPaperLeadingRate m R := by
  have hbase := kolmogorovDistance_M_R_proxyScale_le h R
  calc
    kolmogorovDistance
        (Measure.map
          (fun z ↦ GeneralRDecomposition.M_R m R z /
            generalRProxyScale m R)
          (standardGaussianDataMeasure m p))
        (gaussianReal 0 1) ≤
        generalRLeadingNormalRate m R + generalRScaleMismatchRate p := hbase
    _ ≤ generalRPaperUniversalConstant * generalRPaperLeadingRate m R :=
      generalRPaperLeadingEnvelope_le h R

/-- Exact paper display for the full statistic, including the cube-root
nonlinear perturbation loss. -/
theorem kolmogorovDistance_ZRmpStatistic_le_paperRate
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    kolmogorovDistance
        (Measure.map (ZRmpStatistic m R)
          (standardGaussianDataMeasure m p))
        (gaussianReal 0 1) ≤
      generalRPaperUniversalConstant * generalRPaperFullRate m R := by
  have hfull := kolmogorovDistance_ZRmpStatistic_le_finalRateEnvelope h R
  have hlead := generalRPaperLeadingEnvelope_le h R
  have hcube := (generalRNonlinearCubeRootRate_pos h R).le
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hpert : generalRNonlinearPerturbationRate m R =
      (1 + 1 / Real.sqrt (2 * Real.pi)) *
        generalRNonlinearCubeRootRate m R := by
    unfold generalRNonlinearPerturbationRate
    ring
  have hCpert : (1 + 1 / Real.sqrt (2 * Real.pi) : ℝ) ≤
      generalRPaperUniversalConstant := by
    unfold generalRPaperUniversalConstant
    have hC1 := analyticLogNormalApproximationConstant_ge_one
    have hinv : 0 ≤ 1 / Real.sqrt (2 * Real.pi) := by positivity
    rw [show 100 / Real.sqrt (2 * Real.pi) =
        100 * (1 / Real.sqrt (2 * Real.pi)) by ring]
    nlinarith
  unfold generalRFinalRateEnvelope at hfull
  unfold generalRPaperFullRate
  calc
    kolmogorovDistance
        (Measure.map (ZRmpStatistic m R)
          (standardGaussianDataMeasure m p))
        (gaussianReal 0 1) ≤
        generalRLeadingNormalRate m R + generalRScaleMismatchRate p +
          generalRNonlinearPerturbationRate m R := hfull
    _ ≤ generalRPaperUniversalConstant * generalRPaperLeadingRate m R +
          (1 + 1 / Real.sqrt (2 * Real.pi)) *
            generalRNonlinearCubeRootRate m R := by
      rw [hpert]
      exact add_le_add hlead le_rfl
    _ ≤ generalRPaperUniversalConstant * generalRPaperLeadingRate m R +
          generalRPaperUniversalConstant * generalRNonlinearCubeRootRate m R :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hCpert hcube)
    _ = generalRPaperUniversalConstant *
          (generalRPaperLeadingRate m R +
            generalRNonlinearCubeRootRate m R) := by ring

private theorem one_div_dimension_le_cubeRootRate
    {p : ℕ} (hp : 2 ≤ p) :
    1 / (p : ℝ) ≤ generalRDimensionCubeRootRate p := by
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  have hq0 : 0 ≤ 1 / (p : ℝ) := by positivity
  have hq1 : 1 / (p : ℝ) ≤ 1 := by
    exact (div_le_one hpR).2 (by exact_mod_cast (show 1 ≤ p by omega))
  unfold generalRDimensionCubeRootRate
  exact Real.self_le_rpow_of_le_one hq0 hq1 (by norm_num)

private theorem generalRSpectralCubicRate_le_cubeRootRate
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    generalRSpectralCubicRate m R ≤ generalRDimensionCubeRootRate p := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  have hmR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (show 0 < m by omega)
  have hsqrtp : (0 : ℝ) < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 hpR
  have hsqrtm : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmR
  have hsqrtle : Real.sqrt (p : ℝ) ≤ Real.sqrt (m : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hpm)
  have hinvSqrt : 1 / Real.sqrt (m : ℝ) ≤ 1 / Real.sqrt (p : ℝ) :=
    one_div_le_one_div_of_le hsqrtp hsqrtle
  let q : ℝ := 1 / (p : ℝ)
  let r : ℝ := q ^ ((3 : ℝ)⁻¹)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hr0 : 0 ≤ r := Real.rpow_nonneg hq0 _
  have hrcube : r ^ 3 = q := by
    dsimp [r]
    exact Real.rpow_inv_natCast_pow hq0 (by norm_num)
  have hsqrtOne : 1 ≤ Real.sqrt (p : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ p by omega))
  have hsqrtSq : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) :=
    Real.sq_sqrt hpR.le
  have hpcube : (p : ℝ) ≤ Real.sqrt (p : ℝ) ^ 3 := by
    have hnonneg : 0 ≤ Real.sqrt (p : ℝ) ^ 2 *
        (Real.sqrt (p : ℝ) - 1) :=
      mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hsqrtOne)
    nlinarith
  have hinvCube : (1 / Real.sqrt (p : ℝ)) ^ 3 ≤ q := by
    dsimp [q]
    rw [one_div, inv_pow]
    simpa [one_div] using (inv_le_inv₀ (pow_pos hsqrtp 3) hpR).2 hpcube
  have hinvRoot : 1 / Real.sqrt (p : ℝ) ≤ r := by
    apply (pow_le_pow_iff_left₀ (by positivity) hr0 (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [hrcube]
    exact hinvCube
  have hsqrtTwo : 1 ≤ 2 * Real.sqrt 2 := by
    have hsq : 1 ≤ Real.sqrt 2 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith
  have hcoef : 1 / (2 * Real.sqrt 2 * Real.sqrt (m : ℝ)) ≤
      1 / Real.sqrt (m : ℝ) := by
    apply one_div_le_one_div_of_le hsqrtm
    simpa using mul_le_mul_of_nonneg_right hsqrtTwo hsqrtm.le
  change generalRSpectralCubicRate m R ≤ r
  exact (generalRSpectralCubicRate_le_simple h R).trans
    (hcoef.trans (hinvSqrt.trans hinvRoot))

private theorem generalRNonlinearCubeRootRate_le_three_dimensionCubeRoot
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    generalRNonlinearCubeRootRate m R ≤
      3 * generalRDimensionCubeRootRate p := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  have hmR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (show 0 < m by omega)
  have hpred := one_div_pred_le_two_div hp
  have hQ := generalRNonlinearRateQ_le_simple h R
  have hmInv : 2 / (m : ℝ) ≤ 2 / (p : ℝ) := by
    exact div_le_div_of_nonneg_left (by norm_num) hpR
      (by exact_mod_cast hpm)
  have hQten : generalRNonlinearRateQ m R ≤ 10 / (p : ℝ) := by
    have hfour : 4 / ((p : ℝ) - 1) ≤ 8 / (p : ℝ) := by
      calc
        4 / ((p : ℝ) - 1) = 4 * (1 / ((p : ℝ) - 1)) := by ring
        _ ≤ 4 * (2 / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hpred (by norm_num)
        _ = 8 / (p : ℝ) := by ring
    calc
      generalRNonlinearRateQ m R ≤
          4 / ((p : ℝ) - 1) + 2 / (m : ℝ) := hQ
      _ ≤ 8 / (p : ℝ) + 2 / (p : ℝ) := add_le_add hfour hmInv
      _ = 10 / (p : ℝ) := by ring
  let q : ℝ := 1 / (p : ℝ)
  let r : ℝ := q ^ ((3 : ℝ)⁻¹)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hr0 : 0 ≤ r := Real.rpow_nonneg hq0 _
  have hrcube : r ^ 3 = q := by
    dsimp [r]
    exact Real.rpow_inv_natCast_pow hq0 (by norm_num)
  have hdelta0 := (generalRNonlinearCubeRootRate_pos h R).le
  have hcubes : generalRNonlinearCubeRootRate m R ^ 3 ≤ (3 * r) ^ 3 := by
    rw [generalRNonlinearCubeRootRate_cube h R, mul_pow, hrcube]
    dsimp [q]
    have hten : 10 / (p : ℝ) ≤ 27 / (p : ℝ) :=
      div_le_div_of_nonneg_right (by norm_num) hpR.le
    calc
      generalRNonlinearRateQ m R ≤ 10 / (p : ℝ) := hQten
      _ ≤ 27 / (p : ℝ) := hten
      _ = (3 : ℝ) ^ 3 * (1 / (p : ℝ)) := by
        rw [div_eq_mul_inv]
        norm_num
  have hout := (pow_le_pow_iff_left₀ hdelta0 (mul_nonneg (by norm_num) hr0)
    (by norm_num : (3 : ℕ) ≠ 0)).mp hcubes
  simpa [generalRDimensionCubeRootRate, q, r] using hout

/-- Exact simplified paper display
`d_K(Z_R,N) <= C {lambda_(m,p) + p^(-1/3)}`. -/
theorem kolmogorovDistance_ZRmpStatistic_le_simplePaperRate
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    kolmogorovDistance
        (Measure.map (ZRmpStatistic m R)
          (standardGaussianDataMeasure m p))
        (gaussianReal 0 1) ≤
      generalRPaperSimpleUniversalConstant *
        (nullLambdaSeries m p + generalRDimensionCubeRootRate p) := by
  have hfull := kolmogorovDistance_ZRmpStatistic_le_paperRate h R
  have hone := one_div_dimension_le_cubeRootRate h.1
  have hrho := generalRSpectralCubicRate_le_cubeRootRate h R
  have hdelta := generalRNonlinearCubeRootRate_le_three_dimensionCubeRoot h R
  have hlambda := (nullLambdaSeries_pos h).le
  have hr : 0 ≤ generalRDimensionCubeRootRate p := by
    unfold generalRDimensionCubeRootRate
    exact Real.rpow_nonneg (by positivity) _
  have hrate : generalRPaperFullRate m R ≤
      5 * (nullLambdaSeries m p + generalRDimensionCubeRootRate p) := by
    unfold generalRPaperFullRate generalRPaperLeadingRate
    linarith
  unfold generalRPaperSimpleUniversalConstant
  have hmul := mul_le_mul_of_nonneg_left hrate
    (generalRPaperUniversalConstant_pos.le)
  exact hfull.trans (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul)

/-- Existential universal-constant form of the leading-term theorem, matching
the paper's quantifier structure. -/
theorem exists_universal_generalR_leading_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {m p : ℕ}, ∀ (_h : Admissible m p),
      ∀ R : CorrelationMatrix p,
        kolmogorovDistance
            (Measure.map
              (fun z ↦ GeneralRDecomposition.M_R m R z /
                generalRProxyScale m R)
              (standardGaussianDataMeasure m p))
            (gaussianReal 0 1) ≤ C * generalRPaperLeadingRate m R := by
  exact ⟨generalRPaperUniversalConstant, generalRPaperUniversalConstant_pos,
    fun h R ↦ kolmogorovDistance_M_R_proxyScale_le_paperRate h R⟩

/-- Existential universal-constant form of the full-statistic theorem. -/
theorem exists_universal_generalR_full_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {m p : ℕ}, ∀ (_h : Admissible m p),
      ∀ R : CorrelationMatrix p,
        kolmogorovDistance
            (Measure.map (ZRmpStatistic m R)
              (standardGaussianDataMeasure m p))
            (gaussianReal 0 1) ≤ C * generalRPaperFullRate m R := by
  exact ⟨generalRPaperUniversalConstant, generalRPaperUniversalConstant_pos,
    fun h R ↦ kolmogorovDistance_ZRmpStatistic_le_paperRate h R⟩

/-- Existential universal-constant form of the simplified theorem. -/
theorem exists_universal_generalR_simple_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {m p : ℕ}, ∀ (_h : Admissible m p),
      ∀ R : CorrelationMatrix p,
        kolmogorovDistance
            (Measure.map (ZRmpStatistic m R)
              (standardGaussianDataMeasure m p))
            (gaussianReal 0 1) ≤
          C * (nullLambdaSeries m p + generalRDimensionCubeRootRate p) := by
  exact ⟨generalRPaperSimpleUniversalConstant,
    generalRPaperSimpleUniversalConstant_pos,
    fun h R ↦ kolmogorovDistance_ZRmpStatistic_le_simplePaperRate h R⟩

end

end LogdetLean
