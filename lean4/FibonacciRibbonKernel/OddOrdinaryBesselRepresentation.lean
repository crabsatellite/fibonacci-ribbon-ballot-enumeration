import FibonacciRibbonKernel.OrdinaryBesselRepresentation

namespace FibonacciRibbonKernel

open PowerSeries
open scoped Classical

inductive OddOrdinaryBesselGenerated : ℕ → ℚ⟦X⟧ → Prop
  | zero (degree : ℕ) : OddOrdinaryBesselGenerated degree 0
  | base (degree index : ℕ) (hindex : index ≤ degree) :
      OddOrdinaryBesselGenerated degree
        (oddBesselOrdinarySeries degree ⟨index, by omega⟩)
  | add {degree : ℕ} {left right : ℚ⟦X⟧} :
      OddOrdinaryBesselGenerated degree left →
      OddOrdinaryBesselGenerated degree right →
      OddOrdinaryBesselGenerated degree (left + right)
  | neg {degree : ℕ} {value : ℚ⟦X⟧} :
      OddOrdinaryBesselGenerated degree value →
      OddOrdinaryBesselGenerated degree (-value)
  | scalar {degree : ℕ} (coefficient : ℚ) {value : ℚ⟦X⟧} :
      OddOrdinaryBesselGenerated degree value →
      OddOrdinaryBesselGenerated degree (PowerSeries.C coefficient * value)
  | shift {degree : ℕ} (amount : ℕ) {value : ℚ⟦X⟧} :
      OddOrdinaryBesselGenerated degree value →
      OddOrdinaryBesselGenerated degree
        (PowerSeries.X ^ amount * risingEulerApply amount value)

theorem OddOrdinaryBesselGenerated.finsetSum
    {degree : ℕ} {indexType : Type*} [DecidableEq indexType]
    (indices : Finset indexType) (values : indexType → ℚ⟦X⟧)
    (hvalues : ∀ index ∈ indices,
      OddOrdinaryBesselGenerated degree (values index)) :
    OddOrdinaryBesselGenerated degree (∑ index ∈ indices, values index) := by
  induction indices using Finset.induction_on with
  | empty => exact OddOrdinaryBesselGenerated.zero degree
  | @insert index indices hindex ih =>
      rw [Finset.sum_insert hindex]
      exact (hvalues index (Finset.mem_insert_self index indices)).add
        (ih fun current hcurrent =>
          hvalues current (Finset.mem_insert_of_mem hcurrent))

theorem factorialUnscale_oddBesselMonomial
    (degree index : ℕ) (hindex : index ≤ degree) :
    factorialUnscale
        (PowerSeries.exp ℚ * besselMonomial degree index) =
      oddBesselOrdinarySeries degree ⟨index, by omega⟩ := by
  ext coefficient
  rw [factorialUnscale_coeff, oddBesselOrdinarySeries_coeff]
  unfold oddBesselFactorialCoeff oddBesselBasisVector besselBasisVector
  rfl

theorem factorialUnscale_exponentialHomogeneousTerm_generated
    {degree : ℕ} (term : HomogeneousBesselTerm degree) :
    OddOrdinaryBesselGenerated degree
      (factorialUnscale (PowerSeries.exp ℚ * term.eval)) := by
  have hpoly := term.coefficient.as_sum_support_C_mul_X_pow
  have hpolySeries : (term.coefficient : ℚ⟦X⟧) =
      ∑ power ∈ term.coefficient.support,
        PowerSeries.C (term.coefficient.coeff power) * PowerSeries.X ^ power := by
    ext coefficient
    have hcoeff := congrArg (fun value : Polynomial ℚ =>
      value.coeff coefficient) hpoly
    simpa only [Polynomial.coeff_coe, map_sum,
      PowerSeries.coeff_C_mul_X_pow,
      Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow] using hcoeff
  unfold HomogeneousBesselTerm.eval
  rw [show PowerSeries.exp ℚ *
      ((term.coefficient : ℚ⟦X⟧) * besselMonomial degree term.index) =
      (term.coefficient : ℚ⟦X⟧) *
        (PowerSeries.exp ℚ * besselMonomial degree term.index) by ring]
  rw [hpolySeries, Finset.sum_mul]
  rw [factorialUnscale_finsetSum]
  apply OddOrdinaryBesselGenerated.finsetSum term.coefficient.support
  intro power hpower
  rw [mul_assoc, factorialUnscale_C_mul]
  rw [factorialUnscale_X_pow_mul]
  have hbase : OddOrdinaryBesselGenerated degree
      (factorialUnscale
        (PowerSeries.exp ℚ * besselMonomial degree term.index)) := by
    rw [factorialUnscale_oddBesselMonomial degree term.index term.index_le]
    exact OddOrdinaryBesselGenerated.base degree term.index term.index_le
  exact OddOrdinaryBesselGenerated.scalar (term.coefficient.coeff power)
    (OddOrdinaryBesselGenerated.shift power hbase)

theorem ExponentialHomogeneousBesselGenerated.factorialUnscale_generated
    {degree : ℕ} {value : ℚ⟦X⟧}
    (hvalue : ExponentialHomogeneousBesselGenerated degree value) :
    OddOrdinaryBesselGenerated degree (factorialUnscale value) := by
  obtain ⟨base, hbase, rfl⟩ := hvalue
  obtain ⟨terms, hterms⟩ := hbase.normalForm
  rw [hterms]
  clear hterms hbase base
  induction terms with
  | nil =>
      have hzero : factorialUnscale (PowerSeries.exp ℚ * 0) = 0 := by
        rw [mul_zero]
        ext degree
        simp [factorialUnscale_coeff]
      rw [List.map_nil, List.sum_nil, hzero]
      exact OddOrdinaryBesselGenerated.zero degree
  | cons head tail ih =>
      rw [List.map_cons, List.sum_cons, mul_add, factorialUnscale_add]
      exact (factorialUnscale_exponentialHomogeneousTerm_generated head).add ih

theorem actualOddShiftedOrdinary_besselGenerated
    (halfDimension : ℕ) :
    OddOrdinaryBesselGenerated halfDimension
      (factorialUnscale
        (PowerSeries.X ^ staircaseWeight (2 * halfDimension) *
          generalUnrestrictedFactorialSeries (2 * halfDimension))) :=
  (generalUnrestrictedFactorialSeries_odd_shifted_exponentialHomogeneous
    halfDimension).factorialUnscale_generated

end FibonacciRibbonKernel
