import LogdetLean.NullUniformEdgeworthTarget
import LogdetLean.NullRegimeAsymptotics
import LogdetLean.NullGrowingGapLimits
import LogdetLean.HardEdgeConstant
import LogdetLean.SequentialUniformization
import Mathlib.Tactic

/-!
# The sharp constrained null supremum

This file assembles the sharp null Edgeworth theorem with the regime
asymptotics.  The first part is a reusable deterministic lemma: sequential
one-sided control of a two-parameter family, together with a diagonal lower
witness, controls the supremum over the expanding tail `m ≥ p`.

The null-specific asymptotic theorems are added below this deterministic
assembly.  They are kept separate from the Fourier proof in
`NullUniformEdgeworthTarget.lean`.
-/

namespace LogdetLean

open Filter Set MeasureTheory ProbabilityTheory Real

noncomputable section

/-- A bounded detector for an excess above `C`.  Capping at one lets us use
the uniformization theorem even when the original family has a
`p`-dependent deterministic bound. -/
def cappedUpperExcess (C x : ℝ) : ℝ := min (max (x - C) 0) 1

theorem cappedUpperExcess_nonneg (C x : ℝ) :
    0 ≤ cappedUpperExcess C x := by
  unfold cappedUpperExcess
  exact le_min (le_max_right _ _) zero_le_one

theorem cappedUpperExcess_le_one (C x : ℝ) :
    cappedUpperExcess C x ≤ 1 := by
  exact min_le_right _ _

theorem cappedUpperExcess_tendsto_zero {u : ℕ → ℝ} {C : ℝ}
    (hu : Tendsto u atTop (nhds C)) :
    Tendsto (fun n ↦ cappedUpperExcess C (u n)) atTop (nhds 0) := by
  have hsub : Tendsto (fun n ↦ u n - C) atTop (nhds 0) := by
    simpa using hu.sub_const C
  have hmax : Tendsto (fun n ↦ max (u n - C) 0) atTop (nhds 0) := by
    simpa using hsub.max
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0))
  have hmin : Tendsto (fun n ↦ min (max (u n - C) 0) 1)
      atTop (nhds 0) := by
    simpa using hmax.min
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1))
  exact hmin

/-- A convergent family whose limit is at most `C` has vanishing capped
upper excess above `C`. -/
theorem cappedUpperExcess_tendsto_zero_of_tendsto_le
    {u : ℕ → ℝ} {L C : ℝ}
    (hu : Tendsto u atTop (nhds L)) (hLC : L ≤ C) :
    Tendsto (fun n ↦ cappedUpperExcess C (u n)) atTop (nhds 0) := by
  have hsub : Tendsto (fun n ↦ u n - C) atTop (nhds (L - C)) :=
    hu.sub_const C
  have hmax : Tendsto (fun n ↦ max (u n - C) 0)
      atTop (nhds 0) := by
    have h := hsub.max
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0))
    simpa [max_eq_right (sub_nonpos.mpr hLC)] using h
  have hmin := hmax.min
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1))
  simpa [cappedUpperExcess] using hmin

/-- Reindex a theorem uniform over all tails `m(p) ≥ p` along an arbitrary
strictly increasing dimension sequence.  The extension
`max p (m(invFun pseq p))` is admissible at every integer and agrees with the
given sequence on its image eventually. -/
theorem tendsto_two_sequence_of_all_admissible_sequences
    {X : Type*} [TopologicalSpace X]
    {g : ℕ → ℕ → X} {L : X}
    (hfull : ∀ m : ℕ → ℕ,
      (∀ᶠ p in atTop, p ≤ m p) →
        Tendsto (fun p ↦ g (m p) p) atTop (nhds L))
    {mseq pseq : ℕ → ℕ} (hpmono : StrictMono pseq)
    (hadm : ∀ᶠ n in atTop, pseq n ≤ mseq n) :
    Tendsto (fun n ↦ g (mseq n) (pseq n)) atTop (nhds L) := by
  let mfull : ℕ → ℕ := fun p ↦ max p (mseq (Function.invFun pseq p))
  have hmfull : ∀ p, p ≤ mfull p := fun p ↦ by
    dsimp [mfull]
    exact le_max_left _ _
  have hbase := hfull mfull (Filter.Eventually.of_forall hmfull)
  have hcomp := hbase.comp hpmono.tendsto_atTop
  apply hcomp.congr'
  filter_upwards [hadm] with n hn
  have hinv : Function.invFun pseq (pseq n) = n :=
    Function.leftInverse_invFun hpmono.injective n
  dsimp [mfull]
  rw [hinv, max_eq_right hn]

/-- Every natural-valued sequence has a further cofinal sequence on which
it is either constant or tends to infinity.  This is the discrete
compactness principle behind the fixed-gap/divergent-gap dichotomy. -/
theorem exists_cofinal_subsequence_const_or_atTop (q : ℕ → ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ d : ℕ, ∀ n, q (φ n) = d) ∨
        Tendsto (q ∘ φ) atTop atTop) := by
  by_cases hq : Tendsto q atTop atTop
  · refine ⟨id, strictMono_id, Or.inr ?_⟩
    simpa only [Function.comp_id] using hq
  · have hnot : ¬ ∀ b : ℕ, ∀ᶠ n in atTop, b ≤ q n := by
      simpa only [Filter.tendsto_atTop] using hq
    push Not at hnot
    obtain ⟨b, hb⟩ := hnot
    have hbounded : ∃ᶠ n in atTop,
        ∃ d ∈ Finset.range b, q n = d := by
      exact hb.mono fun n hn ↦
        ⟨q n, Finset.mem_range.mpr hn, rfl⟩
    obtain ⟨d, hdmem, hdfreq⟩ :=
      (Finset.frequently_exists (Finset.range b)).mp hbounded
    obtain ⟨φ, hφ, hconst⟩ :=
      Filter.exists_seq_forall_of_frequently hdfreq
    obtain ⟨ψ, hψ, hφψ⟩ := Filter.strictMono_subseq_of_tendsto_atTop hφ
    refine ⟨φ ∘ ψ, hφψ, Or.inl ⟨d, ?_⟩⟩
    intro n
    exact hconst (ψ n)

private theorem value_le_of_cappedUpperExcess_le_lt_one
    {C x e : ℝ} (hcap : cappedUpperExcess C x ≤ e) (he : e < 1) :
    x ≤ C + e := by
  have hmax : max (x - C) 0 ≤ 1 := by
    by_contra hnot
    have hone : 1 ≤ max (x - C) 0 := le_of_not_ge hnot
    have hcapone : cappedUpperExcess C x = 1 := by
      simp [cappedUpperExcess, min_eq_right hone]
    rw [hcapone] at hcap
    linarith
  have hrewrite : cappedUpperExcess C x = max (x - C) 0 := by
    simp [cappedUpperExcess, min_eq_left hmax]
  rw [hrewrite] at hcap
  have hx : x - C ≤ max (x - C) 0 := le_max_left _ _
  linarith

/-- Deterministic sharp-supremum assembly.

`f p m` is the scaled quantity of interest.  The diagonal `m=p` converges to
`C`.  Every eventually admissible parameter sequence has vanishing capped
excess above `C`.  Then the supremum over all `m≥p` converges to `C`.

The family needs only a bound depending on `p`; the cap provides the fixed
bound required by `tendsto_admissibleTailSup_zero_of_all_sequences`. -/
theorem tendsto_admissibleTailSup_of_diagonal_and_capped_excess
    {f : ℕ → ℕ → ℝ} {C : ℝ}
    (hbounded : ∀ p, ∃ B : ℝ, ∀ m, p ≤ m → f p m ≤ B)
    (hdiag : Tendsto (fun p ↦ f p p) atTop (nhds C))
    (hseq : ∀ m : ℕ → ℕ,
      (∀ᶠ p in atTop, p ≤ m p) →
        Tendsto (fun p ↦ cappedUpperExcess C (f p (m p)))
          atTop (nhds 0)) :
    Tendsto (admissibleTailSup f) atTop (nhds C) := by
  let excess : ℕ → ℕ → ℝ := fun p m ↦ cappedUpperExcess C (f p m)
  have hexcess : Tendsto (admissibleTailSup excess) atTop (nhds 0) := by
    apply tendsto_admissibleTailSup_zero_of_all_sequences
      (C := (1 : ℝ))
    · intro p m hpm
      exact cappedUpperExcess_nonneg C (f p m)
    · intro p m hpm
      exact cappedUpperExcess_le_one C (f p m)
    · intro m hm
      simpa [excess] using hseq m hm
  have hupperLimit : Tendsto
      (fun p ↦ C + admissibleTailSup excess p) atTop (nhds C) := by
    simpa using
      (tendsto_const_nhds.add hexcess : Tendsto
        (fun p ↦ C + admissibleTailSup excess p) atTop (nhds (C + 0)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hdiag hupperLimit
  · filter_upwards with p
    unfold admissibleTailSup
    apply le_csSup
    · obtain ⟨B, hB⟩ := hbounded p
      refine ⟨B, ?_⟩
      rintro x ⟨m, hpm, rfl⟩
      exact hB m hpm
    · exact ⟨p, le_rfl, rfl⟩
  · obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hexcess (1 / 2) (by norm_num)
    have hevent : ∀ᶠ p in atTop, admissibleTailSup excess p < 1 := by
      filter_upwards [eventually_ge_atTop N] with p hpN
      have hp := hN p hpN
      rw [dist_zero_right, Real.norm_eq_abs,
        abs_of_nonneg (admissibleTailSup_nonneg
          (fun p m hpm ↦ cappedUpperExcess_nonneg C (f p m))
          (fun p m hpm ↦ cappedUpperExcess_le_one C (f p m)) p)] at hp
      linarith
    filter_upwards [hevent] with p hp
    change sSup (admissibleTailValues f p) ≤
      C + admissibleTailSup excess p
    apply csSup_le (admissibleTailValues_nonempty f p)
    rintro x ⟨m, hpm, rfl⟩
    have hcap_le_sup : cappedUpperExcess C (f p m) ≤
        admissibleTailSup excess p := by
      unfold admissibleTailSup
      apply le_csSup
      · exact admissibleTailValues_bddAbove
          (fun p m hpm ↦ cappedUpperExcess_le_one C (f p m)) p
      · exact ⟨m, hpm, rfl⟩
    have hf_le := value_le_of_cappedUpperExcess_le_lt_one hcap_le_sup hp
    change f p m ≤ C + sSup (admissibleTailValues excess p) at hf_le
    exact hf_le

/-! ## Null-specific scaled quantities -/

/-- The hard-edge normalization `(log p)^(3/2)`. -/
def nullSharpLogScale (p : ℕ) : ℝ :=
  Real.log (p : ℝ) ^ (3 / 2 : ℝ)

theorem nullSharpLogScale_nonneg (p : ℕ) : 0 ≤ nullSharpLogScale p := by
  unfold nullSharpLogScale
  by_cases hp : p = 0
  · simp [hp]
  · exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hp))) _

/-- The scaled standardized third-cumulant magnitude. -/
def scaledNullLambda (m p : ℕ) : ℝ :=
  nullSharpLogScale p * nullLambdaSeries m p

/-- The scaled exact null Kolmogorov distance. -/
def scaledNullKolmogorov (p m : ℕ) : ℝ :=
  nullSharpLogScale p *
    kolmogorovDistance (standardizedNullLaw m p) (gaussianReal 0 1)

/-- The constrained supremum appearing in the sharp square-edge theorem. -/
def scaledNullKolmogorovSup (p : ℕ) : ℝ :=
  admissibleTailSup scaledNullKolmogorov p

/-- Exact square-edge constant before evaluating the positive hard-edge
series in terms of zeta values. -/
def nullSharpSupremumConstant : ℝ :=
  hardEdgeAConstant 0 / (24 * Real.sqrt Real.pi)

/-- Closed zeta-series form of the sharp constrained constant. -/
theorem nullSharpSupremumConstant_eq_closed :
    nullSharpSupremumConstant =
      squareAConstant / (24 * Real.sqrt Real.pi) := by
  rw [nullSharpSupremumConstant, hardEdgeAConstant_zero_eq_squareAConstant]

theorem nullSharpSupremumConstant_pos : 0 < nullSharpSupremumConstant := by
  unfold nullSharpSupremumConstant
  exact div_pos (hardEdgeAConstant_pos 0) (by positivity)

/-- The elementary simplification converting the square scaled-cumulant
constant into the displayed Kolmogorov constant. -/
theorem hardEdge_edgeworth_constant_simplify (A : ℝ) :
    (A / (2 : ℝ) ^ (3 / 2 : ℝ)) /
        (6 * Real.sqrt (2 * Real.pi)) =
      A / (24 * Real.sqrt Real.pi) := by
  have hpow : (2 : ℝ) ^ (3 / 2 : ℝ) = 2 * Real.sqrt 2 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hsqrt : Real.sqrt (2 * Real.pi) =
      Real.sqrt 2 * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrt2 : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) :=
    Real.mul_self_sqrt (by norm_num)
  have hden :
      (2 * Real.sqrt 2) * (6 * (Real.sqrt 2 * Real.sqrt Real.pi)) =
        24 * Real.sqrt Real.pi := by
    calc
    (2 * Real.sqrt 2) * (6 * (Real.sqrt 2 * Real.sqrt Real.pi)) =
        12 * (Real.sqrt 2 * Real.sqrt 2) * Real.sqrt Real.pi := by ring
    _ = 24 * Real.sqrt Real.pi := by rw [hsqrt2]; ring
  rw [hpow, hsqrt, div_div, hden]

theorem scaledNullKolmogorov_nonneg (p m : ℕ) :
    0 ≤ scaledNullKolmogorov p m := by
  exact mul_nonneg (nullSharpLogScale_nonneg p)
    (kolmogorovDistance_nonneg _ _)

theorem scaledNullKolmogorov_le_logScale (p m : ℕ) :
    scaledNullKolmogorov p m ≤ nullSharpLogScale p := by
  unfold scaledNullKolmogorov
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (kolmogorovDistance_le_one _ _) (nullSharpLogScale_nonneg p)

/-- Two-sequence form of the uniform relative Edgeworth remainder. -/
theorem tendsto_nullUniformEdgeworthRelativeRemainder_zero_two_sequence
    {mseq pseq : ℕ → ℕ} (hpmono : StrictMono pseq)
    (hadm : ∀ᶠ n in atTop, Admissible (mseq n) (pseq n)) :
    Tendsto
      (fun n ↦ nullUniformEdgeworthRelativeRemainder (mseq n) (pseq n))
      atTop (nhds 0) := by
  apply tendsto_two_sequence_of_all_admissible_sequences
      (g := fun m p ↦ nullUniformEdgeworthRelativeRemainder m p)
      (L := 0) (pseq := pseq) (mseq := mseq)
  · intro m hm
    exact tendsto_nullUniformEdgeworthRelativeRemainder_zero m
      ((eventually_ge_atTop 2).and hm)
  · exact hpmono
  · exact hadm.mono fun n hn ↦ hn.2

/-- Once the scaled third cumulant has a limit, the checked uniform
Edgeworth estimate transfers that limit to the correspondingly scaled exact
Kolmogorov distance. -/
theorem tendsto_scaledNullKolmogorov_of_scaledNullLambda
    {mseq pseq : ℕ → ℕ} {L : ℝ}
    (hpmono : StrictMono pseq)
    (hadm : ∀ᶠ n in atTop, Admissible (mseq n) (pseq n))
    (hlambda : Tendsto (fun n ↦ scaledNullLambda (mseq n) (pseq n))
      atTop (nhds L)) :
    Tendsto (fun n ↦ scaledNullKolmogorov (pseq n) (mseq n))
      atTop (nhds (L / (6 * Real.sqrt (2 * Real.pi)))) := by
  let K : ℝ := 6 * Real.sqrt (2 * Real.pi)
  let lead : ℕ → ℝ := fun n ↦ scaledNullLambda (mseq n) (pseq n) / K
  let err : ℕ → ℝ := fun n ↦
    scaledNullKolmogorov (pseq n) (mseq n) - lead n
  have hrem :=
    tendsto_nullUniformEdgeworthRelativeRemainder_zero_two_sequence hpmono hadm
  have hbound : ∀ᶠ n in atTop,
      |err n| ≤ scaledNullLambda (mseq n) (pseq n) *
        nullUniformEdgeworthRelativeRemainder (mseq n) (pseq n) := by
    filter_upwards [hadm] with n hn
    have hfinite := uniformNullSharpKolmogorov_finite hn
    have hs : 0 ≤ nullSharpLogScale (pseq n) :=
      nullSharpLogScale_nonneg (pseq n)
    have hmul := mul_le_mul_of_nonneg_left hfinite hs
    dsimp [err, lead, scaledNullKolmogorov, scaledNullLambda, K]
    calc
      |nullSharpLogScale (pseq n) *
            kolmogorovDistance (standardizedNullLaw (mseq n) (pseq n))
              (gaussianReal 0 1) -
          nullSharpLogScale (pseq n) * nullLambdaSeries (mseq n) (pseq n) /
            (6 * Real.sqrt (2 * Real.pi))| =
          nullSharpLogScale (pseq n) *
            |kolmogorovDistance (standardizedNullLaw (mseq n) (pseq n))
                (gaussianReal 0 1) -
              nullLambdaSeries (mseq n) (pseq n) /
                (6 * Real.sqrt (2 * Real.pi))| := by
            rw [show nullSharpLogScale (pseq n) *
                    kolmogorovDistance
                      (standardizedNullLaw (mseq n) (pseq n))
                      (gaussianReal 0 1) -
                  nullSharpLogScale (pseq n) *
                    nullLambdaSeries (mseq n) (pseq n) /
                      (6 * Real.sqrt (2 * Real.pi)) =
                nullSharpLogScale (pseq n) *
                  (kolmogorovDistance
                      (standardizedNullLaw (mseq n) (pseq n))
                      (gaussianReal 0 1) -
                    nullLambdaSeries (mseq n) (pseq n) /
                      (6 * Real.sqrt (2 * Real.pi))) by ring,
              abs_mul, abs_of_nonneg hs]
      _ ≤ nullSharpLogScale (pseq n) *
          (nullLambdaSeries (mseq n) (pseq n) *
            nullUniformEdgeworthRelativeRemainder (mseq n) (pseq n)) := hmul
      _ = nullSharpLogScale (pseq n) * nullLambdaSeries (mseq n) (pseq n) *
          nullUniformEdgeworthRelativeRemainder (mseq n) (pseq n) := by ring
  have hright : Tendsto
      (fun n ↦ scaledNullLambda (mseq n) (pseq n) *
        nullUniformEdgeworthRelativeRemainder (mseq n) (pseq n))
      atTop (nhds 0) := by
    simpa using hlambda.mul hrem
  have habserr : Tendsto (fun n ↦ |err n|) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun n ↦ abs_nonneg _
    · exact hbound
    · exact hright
  have herr : Tendsto err atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [Real.norm_eq_abs] using habserr
  have hlead : Tendsto lead atTop (nhds (L / K)) := by
    dsimp [lead]
    exact hlambda.div_const K
  have hsum := hlead.add herr
  have heq : (fun n ↦ lead n + err n) =ᶠ[atTop]
      (fun n ↦ scaledNullKolmogorov (pseq n) (mseq n)) := by
    filter_upwards with n
    dsimp [err]
    ring
  have hout := hsum.congr' heq
  simpa [K] using hout

/-- The square sequence `m=p` attains the candidate sharp constant. -/
theorem tendsto_square_scaledNullKolmogorov :
    Tendsto (fun p ↦ scaledNullKolmogorov p p) atTop
      (nhds nullSharpSupremumConstant) := by
  have hlambda : Tendsto (fun p ↦ scaledNullLambda p p) atTop
      (nhds (hardEdgeAConstant 0 / (2 : ℝ) ^ (3 / 2 : ℝ))) := by
    simpa [scaledNullLambda, nullSharpLogScale] using
      tendsto_square_nullLambda_logPow
  have hmain := tendsto_scaledNullKolmogorov_of_scaledNullLambda
    (mseq := fun p ↦ p) (pseq := fun p ↦ p)
    (L := hardEdgeAConstant 0 / (2 : ℝ) ^ (3 / 2 : ℝ))
    strictMono_id (eventually_ge_atTop 2 |>.mono fun p hp ↦ ⟨hp, le_rfl⟩)
    hlambda
  have hconst := hardEdge_edgeworth_constant_simplify (hardEdgeAConstant 0)
  unfold nullSharpSupremumConstant
  rw [← hconst]
  exact hmain

/-- The fixed-gap/diverging-gap dichotomy gives uniform one-sided control
once the growing-gap scaled-cumulant estimate is available.  This assembly
lemma isolates the compactness argument from that analytic estimate. -/
theorem tendsto_cappedUpperExcess_scaledNullKolmogorov_of_growingGap
    (hdiv : ∀ {mseq pseq : ℕ → ℕ},
      StrictMono pseq →
      (∀ᶠ n in atTop, Admissible (mseq n) (pseq n)) →
      Tendsto (fun n ↦ mseq n - pseq n) atTop atTop →
      Tendsto (fun n ↦ scaledNullLambda (mseq n) (pseq n))
        atTop (nhds 0))
    (m : ℕ → ℕ) (hm : ∀ᶠ p in atTop, p ≤ m p) :
    Tendsto (fun p ↦ cappedUpperExcess nullSharpSupremumConstant
      (scaledNullKolmogorov p (m p))) atTop (nhds 0) := by
  refine Filter.tendsto_of_subseq_tendsto (fun ns hns ↦ ?_)
  obtain ⟨θ, hθ, hpmono⟩ := Filter.strictMono_subseq_of_tendsto_atTop hns
  let pseq : ℕ → ℕ := ns ∘ θ
  let mseq : ℕ → ℕ := m ∘ pseq
  have hpmono' : StrictMono pseq := by simpa [pseq] using hpmono
  have hadmBase : ∀ᶠ p in atTop, Admissible (m p) p :=
    (eventually_ge_atTop 2).and hm
  have hadm : ∀ᶠ n in atTop, Admissible (mseq n) (pseq n) := by
    have h := hpmono'.tendsto_atTop.eventually hadmBase
    simpa [mseq, Function.comp_apply] using h
  let q : ℕ → ℕ := fun n ↦ mseq n - pseq n
  obtain ⟨φ, hφ, hcases⟩ := exists_cofinal_subsequence_const_or_atTop q
  let pp : ℕ → ℕ := pseq ∘ φ
  let mm : ℕ → ℕ := mseq ∘ φ
  have hpp : StrictMono pp := hpmono'.comp hφ
  have hadm' : ∀ᶠ n in atTop, Admissible (mm n) (pp n) := by
    have h := hφ.tendsto_atTop.eventually hadm
    simpa [mm, pp, Function.comp_apply] using h
  refine ⟨θ ∘ φ, ?_⟩
  have htarget : Tendsto
      (fun n ↦ cappedUpperExcess nullSharpSupremumConstant
        (scaledNullKolmogorov (pp n) (mm n))) atTop (nhds 0) := by
    rcases hcases with ⟨d, hconst⟩ | hgapTop
    · have hgap : ∀ᶠ n in atTop, mm n = pp n + d := by
        filter_upwards [hadm'] with n hn
        have hq := hconst n
        have hle := hn.2
        dsimp [q, mm, pp, Function.comp_apply] at hq hle ⊢
        omega
      have hlambda : Tendsto
          (fun n ↦ scaledNullLambda (mm n) (pp n)) atTop
          (nhds (hardEdgeAConstant d / (2 : ℝ) ^ (3 / 2 : ℝ))) := by
        simpa [scaledNullLambda, nullSharpLogScale] using
          tendsto_fixedGap_nullLambda_logPow_of_eventually_eq
            mm pp d hpp.tendsto_atTop hgap
      have hdkRaw := tendsto_scaledNullKolmogorov_of_scaledNullLambda
        hpp hadm' hlambda
      have hdk : Tendsto
          (fun n ↦ scaledNullKolmogorov (pp n) (mm n)) atTop
          (nhds (hardEdgeAConstant d / (24 * Real.sqrt Real.pi))) := by
        simpa only [hardEdge_edgeworth_constant_simplify] using hdkRaw
      have hle : hardEdgeAConstant d / (24 * Real.sqrt Real.pi) ≤
          nullSharpSupremumConstant := by
        unfold nullSharpSupremumConstant
        exact div_le_div_of_nonneg_right
          (hardEdgeAConstant_antitone (Nat.zero_le d)) (by positivity)
      exact cappedUpperExcess_tendsto_zero_of_tendsto_le hdk hle
    · have hgap' : Tendsto (fun n ↦ mm n - pp n) atTop atTop := by
        change Tendsto (q ∘ φ) atTop atTop
        exact hgapTop
      have hlambda := hdiv hpp hadm' hgap'
      have hdkRaw := tendsto_scaledNullKolmogorov_of_scaledNullLambda
        hpp hadm' hlambda
      have hdk : Tendsto
          (fun n ↦ scaledNullKolmogorov (pp n) (mm n)) atTop
          (nhds 0) := by simpa using hdkRaw
      exact cappedUpperExcess_tendsto_zero_of_tendsto_le hdk
        (le_of_lt nullSharpSupremumConstant_pos)
  simpa [pseq, mseq, pp, mm, Function.comp_apply] using htarget

/-- Conditional final assembly: a growing-gap cumulant estimate plus the
already checked fixed-gap theory and square witness imply convergence of the
actual constrained `sSup`. -/
theorem tendsto_scaledNullKolmogorovSup_of_growingGap
    (hdiv : ∀ {mseq pseq : ℕ → ℕ},
      StrictMono pseq →
      (∀ᶠ n in atTop, Admissible (mseq n) (pseq n)) →
      Tendsto (fun n ↦ mseq n - pseq n) atTop atTop →
      Tendsto (fun n ↦ scaledNullLambda (mseq n) (pseq n))
        atTop (nhds 0)) :
    Tendsto scaledNullKolmogorovSup atTop
      (nhds nullSharpSupremumConstant) := by
  unfold scaledNullKolmogorovSup
  apply tendsto_admissibleTailSup_of_diagonal_and_capped_excess
  · intro p
    exact ⟨nullSharpLogScale p, fun m _hm ↦
      scaledNullKolmogorov_le_logScale p m⟩
  · exact tendsto_square_scaledNullKolmogorov
  · exact tendsto_cappedUpperExcess_scaledNullKolmogorov_of_growingGap hdiv

/-- Sharp constrained square-edge theorem for the actual standardized null
law.  The supremum is the real `sSup` over every integer `m ≥ p`. -/
theorem tendsto_scaledNullKolmogorovSup :
    Tendsto scaledNullKolmogorovSup atTop
      (nhds nullSharpSupremumConstant) := by
  apply tendsto_scaledNullKolmogorovSup_of_growingGap
  intro mseq pseq hp hadm hgap
  simpa [scaledNullLambda, nullSharpLogScale] using
    tendsto_growingGap_nullLambda_logPow_of_strictMono hp hadm hgap

/-- The same theorem with the exact displayed zeta-series constant. -/
theorem tendsto_scaledNullKolmogorovSup_closed :
    Tendsto scaledNullKolmogorovSup atTop
      (nhds (squareAConstant / (24 * Real.sqrt Real.pi))) := by
  rw [← nullSharpSupremumConstant_eq_closed]
  exact tendsto_scaledNullKolmogorovSup

end

end LogdetLean
