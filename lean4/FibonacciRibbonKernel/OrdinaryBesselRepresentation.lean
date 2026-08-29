import FibonacciRibbonKernel.HomogeneousBesselNormalForm
import FibonacciRibbonKernel.BorelFactorialTransport

namespace FibonacciRibbonKernel

open PowerSeries
open scoped Classical

inductive OrdinaryBesselGenerated : ℕ → ℚ⟦X⟧ → Prop
  | zero (degree : ℕ) : OrdinaryBesselGenerated degree 0
  | base (degree index : ℕ) (hindex : index ≤ degree) :
      OrdinaryBesselGenerated degree
        (besselOrdinarySeries degree ⟨index, by omega⟩)
  | add {degree : ℕ} {left right : ℚ⟦X⟧} :
      OrdinaryBesselGenerated degree left →
      OrdinaryBesselGenerated degree right →
      OrdinaryBesselGenerated degree (left + right)
  | neg {degree : ℕ} {value : ℚ⟦X⟧} :
      OrdinaryBesselGenerated degree value →
      OrdinaryBesselGenerated degree (-value)
  | scalar {degree : ℕ} (coefficient : ℚ) {value : ℚ⟦X⟧} :
      OrdinaryBesselGenerated degree value →
      OrdinaryBesselGenerated degree (PowerSeries.C coefficient * value)
  | shift {degree : ℕ} (amount : ℕ) {value : ℚ⟦X⟧} :
      OrdinaryBesselGenerated degree value →
      OrdinaryBesselGenerated degree
        (PowerSeries.X ^ amount * risingEulerApply amount value)

theorem OrdinaryBesselGenerated.finsetSum
    {degree : ℕ} {indexType : Type*} [DecidableEq indexType]
    (indices : Finset indexType) (values : indexType → ℚ⟦X⟧)
    (hvalues : ∀ index ∈ indices,
      OrdinaryBesselGenerated degree (values index)) :
    OrdinaryBesselGenerated degree (∑ index ∈ indices, values index) := by
  induction indices using Finset.induction_on with
  | empty => exact OrdinaryBesselGenerated.zero degree
  | @insert index indices hindex ih =>
      rw [Finset.sum_insert hindex]
      exact (hvalues index (Finset.mem_insert_self index indices)).add
        (ih fun current hcurrent =>
          hvalues current (Finset.mem_insert_of_mem hcurrent))

theorem OrdinaryBesselGenerated.listSum
    {degree : ℕ} (values : List ℚ⟦X⟧)
    (hvalues : ∀ value ∈ values, OrdinaryBesselGenerated degree value) :
    OrdinaryBesselGenerated degree values.sum := by
  induction values with
  | nil => exact OrdinaryBesselGenerated.zero degree
  | cons head tail ih =>
      rw [List.sum_cons]
      exact (hvalues head (by simp)).add
        (ih fun value hvalue => hvalues value (by simp [hvalue]))

theorem factorialUnscale_besselMonomial
    (degree index : ℕ) (hindex : index ≤ degree) :
    factorialUnscale (besselMonomial degree index) =
      besselOrdinarySeries degree ⟨index, by omega⟩ := by
  ext coefficient
  rw [factorialUnscale_coeff, besselOrdinarySeries_coeff]
  unfold besselFactorialCoeff besselBasisVector
  rfl

theorem factorialUnscale_C_mul
    (coefficient : ℚ) (series : ℚ⟦X⟧) :
    factorialUnscale (PowerSeries.C coefficient * series) =
      PowerSeries.C coefficient * factorialUnscale series := by
  ext degree
  rw [factorialUnscale_coeff, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul, factorialUnscale_coeff]
  ring

theorem factorialUnscale_homogeneousTerm_generated
    {degree : ℕ} (term : HomogeneousBesselTerm degree) :
  OrdinaryBesselGenerated degree
      (factorialUnscale term.eval) := by
  have hpoly := term.coefficient.as_sum_support_C_mul_X_pow
  have hpolySeries : (term.coefficient : ℚ⟦X⟧) =
      ∑ power ∈ term.coefficient.support,
        PowerSeries.C (term.coefficient.coeff power) * PowerSeries.X ^ power := by
    ext coefficient
    have hcoeff := congrArg (fun value : Polynomial ℚ =>
      value.coeff coefficient) hpoly
    simpa only [Polynomial.coeff_coe, map_sum, PowerSeries.coeff_C_mul_X_pow,
      Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow] using hcoeff
  unfold HomogeneousBesselTerm.eval
  rw [hpolySeries, Finset.sum_mul]
  rw [factorialUnscale_finsetSum]
  apply OrdinaryBesselGenerated.finsetSum term.coefficient.support
  intro power hpower
  rw [mul_assoc, factorialUnscale_C_mul]
  rw [factorialUnscale_X_pow_mul]
  have hbase : OrdinaryBesselGenerated degree
      (factorialUnscale (besselMonomial degree term.index)) := by
    rw [factorialUnscale_besselMonomial degree term.index term.index_le]
    exact OrdinaryBesselGenerated.base degree term.index term.index_le
  exact OrdinaryBesselGenerated.scalar (term.coefficient.coeff power)
    (OrdinaryBesselGenerated.shift power hbase)

theorem factorialUnscale_list_sum
    (values : List ℚ⟦X⟧) :
    factorialUnscale values.sum = (values.map factorialUnscale).sum := by
  induction values with
  | nil =>
      ext degree
      simp [factorialUnscale_coeff]
  | cons head tail ih =>
      rw [List.sum_cons, factorialUnscale_add, ih,
        List.map_cons, List.sum_cons]

theorem HomogeneousBesselGenerated.factorialUnscale_generated
    {degree : ℕ} {value : ℚ⟦X⟧}
    (hvalue : HomogeneousBesselGenerated degree value) :
    OrdinaryBesselGenerated degree (factorialUnscale value) := by
  obtain ⟨terms, hterms⟩ := hvalue.normalForm
  rw [hterms]
  clear hterms
  induction terms with
  | nil =>
      have hzero : factorialUnscale (0 : ℚ⟦X⟧) = 0 := by
        ext degree
        simp [factorialUnscale_coeff]
      rw [List.map_nil, List.sum_nil, hzero]
      exact OrdinaryBesselGenerated.zero degree
  | cons head tail ih =>
      rw [List.map_cons, List.sum_cons, factorialUnscale_add]
      exact (factorialUnscale_homogeneousTerm_generated head).add ih

theorem actualEvenShiftedOrdinary_besselGenerated
    (halfDimension : ℕ) (hhalf : 1 ≤ halfDimension) :
    OrdinaryBesselGenerated halfDimension
      (factorialUnscale
        (PowerSeries.X ^ staircaseWeight (2 * halfDimension - 1) *
          generalUnrestrictedFactorialSeries (2 * halfDimension - 1))) :=
  (generalUnrestrictedFactorialSeries_even_shifted_homogeneous
    halfDimension hhalf).factorialUnscale_generated

end FibonacciRibbonKernel
