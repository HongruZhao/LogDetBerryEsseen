import LogdetLean.NullUniformEdgeworthTarget
import LogdetLean.GeneralRPaperExactTranslation
import LogdetLean.NullVUniformAsymptotics
import LogdetLean.NullRefinedAsymptotics
import LogdetLean.NullSharpSupremumDecimal

/-!
# Paper-facing public endpoints

This narrow module contains the interface advertised in the paper's Table 2.
In release v1.1.2 it also packages the complete growing-gap statement (6.3)
and the complete hard-edge identity (6.6) as two auditable public endpoints.
It does not broaden the paper-facing verification claim to other declarations
that happen to lie in the transitive source dependency cone.
-/

namespace LogdetLean

open Filter
open scoped Topology BigOperators

/-- Public endpoint for equation (6.3).

The first two clauses give an explicit finite remainder bound and its limiting
form for `A_d = 4/d + O(d^{-2})`.  The last clause is the sequential form of
`A_{m,p} ~ 4p^2 / ((m-p)m^2)` whenever the gap tends to infinity. -/
theorem paperEquationSixThree_exact :
    (forall d : Nat, 1 <= d ->
      4 / (((d + 1 : Nat) : Real)) <= hardEdgeAConstant d /\
        hardEdgeAConstant d <= 4 / (d : Real) + 8 / (d : Real) ^ 2) /\
    Tendsto (fun d : Nat => (d : Real) * hardEdgeAConstant d)
      atTop (nhds 4) /\
    forall mseq pseq : Nat -> Nat,
      Tendsto pseq atTop atTop ->
      (∀ᶠ n in atTop, Admissible (mseq n) (pseq n)) ->
      Tendsto (fun n => mseq n - pseq n) atTop atTop ->
      Tendsto (fun n => nullASeries (mseq n) (pseq n) /
        nullAGrowingScale (mseq n) (pseq n)) atTop (nhds 1) := by
  refine ⟨?_, tendsto_gap_mul_hardEdgeAConstant, ?_⟩
  · intro d hd
    exact hardEdgeAConstant_tail_bounds d hd
  · intro mseq pseq hp hadm hgap
    exact tendsto_growingGap_nullASeries_div_growingScale hp hadm hgap

/-- Public endpoint for equation (6.6), including the strict decrease stated
immediately after its display.  Here `negPsiTwoSeries x = -psi_2(x)`, so the
finite sum has exactly the manuscript's sign convention. -/
theorem paperEquationSixSix_exact :
    hardEdgeAConstant 0 =
      4 * Real.pi ^ 2 / 3 + 7 * realZetaThree /\
    (forall d : Nat, hardEdgeAConstant d = hardEdgeAConstant 0 +
      Finset.sum (Finset.Icc 1 d)
        (fun k => -negPsiTwoSeries ((k : Real) / 2))) /\
    StrictAnti hardEdgeAConstant := by
  refine ⟨?_, hardEdgeAConstant_eq_zero_add_negPsiTwoSum,
    hardEdgeAConstant_strictAnti⟩
  simpa [squareAConstant] using hardEdgeAConstant_zero_eq_squareAConstant

end LogdetLean

#check LogdetLean.map_centeredSampleCorrelationDet_succ_eq_map_product_betaFactors
#check LogdetLean.uniformNullEdgeworthTarget_proved
#check LogdetLean.tendsto_uniformActualNullSharpKolmogorov_relative_error_zero
#check LogdetLean.paperTheoremFiveOne_exact
#check LogdetLean.paperTheoremFiveTwo_exact
#check LogdetLean.paperTheoremFiveTwo_arbitraryCovariance_exact
#check LogdetLean.tendsto_nullASeries_div_uniformScale
#check LogdetLean.paperEquationSixThree_exact
#check LogdetLean.tendsto_nullVSeries_div_uniformScale
#check LogdetLean.tendsto_square_nullVSeries_sub_two_log
#check LogdetLean.paperEquationSixSix_exact
#check LogdetLean.tendsto_scaledNullKolmogorovSup_closed
#check LogdetLean.nullSharpSupremumConstant_decimal8
