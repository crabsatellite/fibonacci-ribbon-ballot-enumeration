import FibonacciRibbonKernel.PolynomialDifferentialSystem
import Mathlib.Algebra.Polynomial.OfFn

namespace FibonacciRibbonKernel

open PowerSeries
open scoped Classical

theorem polynomial_coe_pow_ps (value : Polynomial ℚ) (power : ℕ) :
    ((value ^ power : Polynomial ℚ) : ℚ⟦X⟧) =
      (value : ℚ⟦X⟧) ^ power := by
  change Polynomial.coeToPowerSeries.ringHom (value ^ power) = _
  rw [map_pow]
  rfl

theorem polynomial_C_natCast_coe (value : ℕ) :
    ((Polynomial.C (value : ℚ) : Polynomial ℚ) : ℚ⟦X⟧) =
      (value : ℚ⟦X⟧) := by
  rw [Polynomial.coe_C]
  norm_num

noncomputable def eulerOperatorApply
    (operator : Polynomial (Polynomial ℚ)) (value : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  operator.sum fun order coefficient =>
    (coefficient : ℚ⟦X⟧) * eulerDerivative^[order] value

def EulerOperatorDFinite (value : ℚ⟦X⟧) : Prop :=
  ∃ operator : Polynomial (Polynomial ℚ), operator ≠ 0 ∧
    eulerOperatorApply operator value = 0

theorem eulerOperatorApply_zero (value : ℚ⟦X⟧) :
    eulerOperatorApply 0 value = 0 := by
  simp [eulerOperatorApply]

theorem eulerOperatorApply_add
    (left right : Polynomial (Polynomial ℚ)) (value : ℚ⟦X⟧) :
    eulerOperatorApply (left + right) value =
      eulerOperatorApply left value + eulerOperatorApply right value := by
  unfold eulerOperatorApply
  apply Polynomial.sum_add_index
  · intro order
    simp
  · intro order first second
    rw [polynomial_coe_add, add_mul]

theorem eulerOperatorApply_finsetSum
    {indexType : Type*} [DecidableEq indexType]
    (indices : Finset indexType)
    (operators : indexType → Polynomial (Polynomial ℚ))
    (value : ℚ⟦X⟧) :
    eulerOperatorApply (∑ index ∈ indices, operators index) value =
      ∑ index ∈ indices, eulerOperatorApply (operators index) value := by
  induction indices using Finset.induction_on with
  | empty => simp [eulerOperatorApply_zero]
  | @insert index indices hindex ih =>
      simp only [Finset.sum_insert hindex]
      rw [eulerOperatorApply_add, ih]

theorem eulerOperatorApply_ofFn (order : ℕ)
    (coefficients : Fin (order + 1) → Polynomial ℚ)
    (value : ℚ⟦X⟧) :
    eulerOperatorApply (Polynomial.ofFn (order + 1) coefficients) value =
      ∑ index, (coefficients index : ℚ⟦X⟧) *
        eulerDerivative^[index.val] value := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  rw [show (∑ index, Polynomial.monomial index.val (coefficients index)) =
      ∑ index ∈ Finset.univ,
        Polynomial.monomial index.val (coefficients index) by simp]
  rw [eulerOperatorApply_finsetSum]
  apply Finset.sum_congr rfl
  intro index hindex
  unfold eulerOperatorApply
  rw [Polynomial.sum_monomial_index]
  simp

theorem eulerDFinite_to_operator {value : ℚ⟦X⟧} :
    EulerDFinite value → EulerOperatorDFinite value := by
  rintro ⟨order, coefficients, ⟨⟨index, hindex⟩, hrelation⟩⟩
  refine ⟨Polynomial.ofFn (order + 1) coefficients, ?_, ?_⟩
  · intro hzero
    have hinjective := Polynomial.injective_ofFn (R := Polynomial ℚ) (order + 1)
    have hfunction : coefficients = 0 := hinjective (by
      simpa [Polynomial.ofFn_zero] using hzero)
    have := congrFun hfunction index
    simp only [Pi.zero_apply] at this
    exact hindex this
  · rw [eulerOperatorApply_ofFn]
    exact hrelation

theorem eulerOperatorApply_eq_fin_natDegree
    (operator : Polynomial (Polynomial ℚ)) (value : ℚ⟦X⟧) :
    eulerOperatorApply operator value =
      ∑ index : Fin (operator.natDegree + 1),
        (operator.coeff index.val : ℚ⟦X⟧) *
          eulerDerivative^[index.val] value := by
  unfold eulerOperatorApply
  rw [operator.sum_over_range (fun _ => by simp)]
  exact (Fin.sum_univ_eq_sum_range (fun index =>
    (operator.coeff index : ℚ⟦X⟧) *
      eulerDerivative^[index] value) (operator.natDegree + 1)).symm

theorem eulerOperator_to_eulerDFinite {value : ℚ⟦X⟧} :
    EulerOperatorDFinite value → EulerDFinite value := by
  rintro ⟨operator, hoperator, hrelation⟩
  refine ⟨operator.natDegree,
    (fun index : Fin (operator.natDegree + 1) =>
      operator.coeff index.val), ?_⟩
  constructor
  · refine ⟨⟨operator.natDegree, by omega⟩, ?_⟩
    change operator.coeff operator.natDegree ≠ 0
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hoperator
  · rw [← eulerOperatorApply_eq_fin_natDegree]
    exact hrelation

theorem eulerDFinite_iff_operator {value : ℚ⟦X⟧} :
    EulerDFinite value ↔ EulerOperatorDFinite value :=
  ⟨eulerDFinite_to_operator, eulerOperator_to_eulerDFinite⟩

noncomputable def shiftedEulerDerivative (shift : ℕ)
    (value : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  eulerDerivative value + (shift : ℚ⟦X⟧) * value

theorem eulerDerivative_X_pow_mul (shift : ℕ) (value : ℚ⟦X⟧) :
    eulerDerivative (X ^ shift * value) =
      X ^ shift * shiftedEulerDerivative shift value := by
  rw [eulerDerivative_mul]
  unfold shiftedEulerDerivative eulerDerivative
  rw [PowerSeries.derivative_pow, PowerSeries.derivative_X]
  by_cases hshift : shift = 0
  · subst shift
    simp
  · have hshiftPos : 1 ≤ shift := Nat.one_le_iff_ne_zero.mpr hshift
    have hpower : (X : ℚ⟦X⟧) ^ shift =
        X * X ^ (shift - 1) := by
      calc
        X ^ shift = X ^ ((shift - 1) + 1) := by congr 1; omega
        _ = X ^ (shift - 1) * X := pow_succ _ _
        _ = X * X ^ (shift - 1) := mul_comm _ _
    rw [hpower]
    ring

theorem iterate_eulerDerivative_X_pow_mul
    (shift order : ℕ) (value : ℚ⟦X⟧) :
    eulerDerivative^[order] (X ^ shift * value) =
      X ^ shift * (shiftedEulerDerivative shift)^[order] value := by
  induction order with
  | zero => simp
  | succ order ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact eulerDerivative_X_pow_mul shift _

noncomputable def eulerEnd : Module.End ℚ ℚ⟦X⟧ :=
  (LinearMap.mulLeft ℚ X).comp (PowerSeries.derivative ℚ).toLinearMap

noncomputable def scalarEnd (shift : ℕ) : Module.End ℚ ℚ⟦X⟧ :=
  (shift : ℚ) • LinearMap.id

theorem eulerEnd_apply (value : ℚ⟦X⟧) :
    eulerEnd value = eulerDerivative value := by
  rfl

theorem scalarEnd_apply (shift : ℕ) (value : ℚ⟦X⟧) :
    scalarEnd shift value = (shift : ℚ⟦X⟧) * value := by
  change (shift : ℚ) • value = (shift : ℚ⟦X⟧) * value
  rw [Algebra.smul_def]
  norm_num

theorem eulerEnd_commute_scalarEnd (shift : ℕ) :
    Commute eulerEnd (scalarEnd shift) := by
  unfold Commute
  apply LinearMap.ext
  intro value
  change eulerEnd (scalarEnd shift value) =
    scalarEnd shift (eulerEnd value)
  rw [scalarEnd_apply, scalarEnd_apply, eulerEnd_apply, eulerEnd_apply]
  simp [eulerDerivative]
  ring

theorem shiftedEulerDerivative_eq_end_apply (shift : ℕ) (value : ℚ⟦X⟧) :
    shiftedEulerDerivative shift value =
      (eulerEnd + scalarEnd shift) value := by
  simp [shiftedEulerDerivative, eulerEnd_apply, scalarEnd_apply]

theorem eulerEnd_pow_apply (order : ℕ) (value : ℚ⟦X⟧) :
    (eulerEnd ^ order) value = eulerDerivative^[order] value := by
  exact Module.End.pow_apply eulerEnd order value

theorem scalarEnd_pow_apply (shift order : ℕ) (value : ℚ⟦X⟧) :
    (scalarEnd shift ^ order) value =
      ((shift : ℚ) ^ order) • value := by
  induction order generalizing value with
  | zero => simp
  | succ order ih =>
      rw [pow_succ, Module.End.mul_apply, ih]
      simp [scalarEnd, smul_smul, pow_succ']
      rw [mul_comm]

theorem end_finsetSum_apply
    {indexType : Type*} [DecidableEq indexType]
    (indices : Finset indexType)
    (operators : indexType → Module.End ℚ ℚ⟦X⟧)
    (value : ℚ⟦X⟧) :
    (∑ index ∈ indices, operators index) value =
      ∑ index ∈ indices, operators index value := by
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices hindex ih =>
      simp only [Finset.sum_insert hindex, LinearMap.add_apply]
      rw [ih]

theorem iterate_eulerDerivative_smul
    (scalar : ℚ) (order : ℕ) (value : ℚ⟦X⟧) :
    eulerDerivative^[order] (scalar • value) =
      scalar • eulerDerivative^[order] value := by
  induction order with
  | zero => simp
  | succ order ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      simp [eulerDerivative]

theorem iterate_shiftedEulerDerivative_binomial
    (shift order : ℕ) (value : ℚ⟦X⟧) :
    (shiftedEulerDerivative shift)^[order] value =
      ∑ derivativeOrder ∈ Finset.range (order + 1),
        ((Nat.choose order derivativeOrder : ℕ) : ℚ⟦X⟧) *
          (shift : ℚ⟦X⟧) ^ (order - derivativeOrder) *
          eulerDerivative^[derivativeOrder] value := by
  have hpow := (eulerEnd_commute_scalarEnd shift).add_pow order
  have happ := congrArg (fun operator : Module.End ℚ ℚ⟦X⟧ => operator value) hpow
  rw [Module.End.pow_apply] at happ
  have hfunction : (⇑(eulerEnd + scalarEnd shift)) =
      shiftedEulerDerivative shift := by
    funext current
    exact (shiftedEulerDerivative_eq_end_apply shift current).symm
  rw [hfunction] at happ
  rw [happ]
  rw [end_finsetSum_apply]
  apply Finset.sum_congr rfl
  intro derivativeOrder hderivativeOrder
  rw [Module.End.mul_apply, Module.End.mul_apply,
    scalarEnd_pow_apply, eulerEnd_pow_apply]
  rw [Module.End.natCast_apply,
    ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  change eulerDerivative^[derivativeOrder]
      ((((shift : ℚ) ^ (order - derivativeOrder)) *
        (Nat.choose order derivativeOrder : ℚ)) • value) = _
  rw [iterate_eulerDerivative_smul]
  simp only [Algebra.smul_def]
  push_cast
  ring

theorem eulerOperatorApply_C_mul
    (coefficient : Polynomial ℚ)
    (operator : Polynomial (Polynomial ℚ)) (value : ℚ⟦X⟧) :
    eulerOperatorApply (Polynomial.C coefficient * operator) value =
      (coefficient : ℚ⟦X⟧) * eulerOperatorApply operator value := by
  induction operator using Polynomial.induction_on' with
  | add left right leftIH rightIH =>
      rw [mul_add, eulerOperatorApply_add,
        eulerOperatorApply_add, leftIH, rightIH, mul_add]
  | monomial order current =>
      rw [Polynomial.C_mul_monomial]
      unfold eulerOperatorApply
      rw [Polynomial.sum_monomial_index,
        Polynomial.sum_monomial_index]
      · rw [polynomial_coe_mul]
        ring
      · simp
      · simp

noncomputable def eulerShiftAffine (shift : ℕ) :
    Polynomial (Polynomial ℚ) :=
  Polynomial.X + Polynomial.C (Polynomial.C (shift : ℚ))

theorem eulerOperatorApply_shiftAffine_pow
    (shift order : ℕ) (value : ℚ⟦X⟧) :
    eulerOperatorApply (eulerShiftAffine shift ^ order) value =
      (shiftedEulerDerivative shift)^[order] value := by
  have hpow := (Commute.all
    (Polynomial.X : Polynomial (Polynomial ℚ))
    (Polynomial.C (Polynomial.C (shift : ℚ)))).add_pow order
  unfold eulerShiftAffine
  rw [hpow]
  rw [show (∑ derivativeOrder ∈ Finset.range (order + 1),
      (Polynomial.X : Polynomial (Polynomial ℚ)) ^ derivativeOrder *
        Polynomial.C (Polynomial.C (shift : ℚ)) ^
          (order - derivativeOrder) *
        (order.choose derivativeOrder : Polynomial (Polynomial ℚ))) =
      ∑ derivativeOrder ∈ Finset.range (order + 1),
        Polynomial.monomial derivativeOrder
          (Polynomial.C (shift : ℚ) ^ (order - derivativeOrder) *
            (order.choose derivativeOrder : Polynomial ℚ)) by
    apply Finset.sum_congr rfl
    intro derivativeOrder hderivativeOrder
    simp only [Polynomial.X_pow_eq_monomial]
    rw [← map_pow]
    rw [← Polynomial.C_eq_natCast]
    rw [Polynomial.monomial_mul_C, Polynomial.monomial_mul_C]
    simp]
  rw [eulerOperatorApply_finsetSum]
  rw [iterate_shiftedEulerDerivative_binomial]
  apply Finset.sum_congr rfl
  intro derivativeOrder hderivativeOrder
  unfold eulerOperatorApply
  rw [Polynomial.sum_monomial_index]
  · rw [polynomial_coe_mul]
    rw [polynomial_coe_pow_ps, polynomial_C_natCast_coe,
      polynomial_coe_natCast]
    ring
  · simp

noncomputable def shiftedEulerOperatorApply
    (operator : Polynomial (Polynomial ℚ)) (shift : ℕ)
    (value : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  operator.sum fun order coefficient =>
    (coefficient : ℚ⟦X⟧) *
      (shiftedEulerDerivative shift)^[order] value

theorem shiftedEulerOperatorApply_add
    (left right : Polynomial (Polynomial ℚ))
    (shift : ℕ) (value : ℚ⟦X⟧) :
    shiftedEulerOperatorApply (left + right) shift value =
      shiftedEulerOperatorApply left shift value +
        shiftedEulerOperatorApply right shift value := by
  unfold shiftedEulerOperatorApply
  apply Polynomial.sum_add_index
  · intro order
    simp
  · intro order first second
    rw [polynomial_coe_add, add_mul]

theorem shiftedEulerOperatorApply_monomial
    (order : ℕ) (coefficient : Polynomial ℚ)
    (shift : ℕ) (value : ℚ⟦X⟧) :
    shiftedEulerOperatorApply (Polynomial.monomial order coefficient)
        shift value =
      (coefficient : ℚ⟦X⟧) *
        (shiftedEulerDerivative shift)^[order] value := by
  unfold shiftedEulerOperatorApply
  rw [Polynomial.sum_monomial_index]
  simp

theorem eulerOperatorApply_comp_shift
    (operator : Polynomial (Polynomial ℚ))
    (shift : ℕ) (value : ℚ⟦X⟧) :
    eulerOperatorApply
        (operator.comp (eulerShiftAffine shift)) value =
      shiftedEulerOperatorApply operator shift value := by
  induction operator using Polynomial.induction_on' with
  | add left right leftIH rightIH =>
      rw [Polynomial.add_comp, eulerOperatorApply_add,
        shiftedEulerOperatorApply_add, leftIH, rightIH]
  | monomial order coefficient =>
      rw [Polynomial.monomial_comp, eulerOperatorApply_C_mul,
        eulerOperatorApply_shiftAffine_pow,
        shiftedEulerOperatorApply_monomial]

theorem eulerOperatorApply_X_pow_mul
    (operator : Polynomial (Polynomial ℚ))
    (shift : ℕ) (value : ℚ⟦X⟧) :
    eulerOperatorApply operator (X ^ shift * value) =
      X ^ shift * shiftedEulerOperatorApply operator shift value := by
  induction operator using Polynomial.induction_on' with
  | add left right leftIH rightIH =>
      rw [eulerOperatorApply_add,
        shiftedEulerOperatorApply_add, leftIH, rightIH, mul_add]
  | monomial order coefficient =>
      unfold eulerOperatorApply shiftedEulerOperatorApply
      rw [Polynomial.sum_monomial_index,
        Polynomial.sum_monomial_index]
      · rw [iterate_eulerDerivative_X_pow_mul]
        ring
      · simp
      · simp

theorem EulerDFinite.cancel_X_pow
    {value : ℚ⟦X⟧} (shift : ℕ)
    (hfinite : EulerDFinite (X ^ shift * value)) :
    EulerDFinite value := by
  rw [eulerDFinite_iff_operator] at hfinite ⊢
  obtain ⟨operator, hoperator, hrelation⟩ := hfinite
  let shiftedOperator := operator.comp (eulerShiftAffine shift)
  have hshiftedOperator : shiftedOperator ≠ 0 := by
    dsimp only [shiftedOperator, eulerShiftAffine]
    exact (Polynomial.comp_X_add_C_ne_zero_iff).mpr hoperator
  refine ⟨shiftedOperator, hshiftedOperator, ?_⟩
  have hproduct : X ^ shift *
      eulerOperatorApply shiftedOperator value = 0 := by
    rw [show eulerOperatorApply shiftedOperator value =
        shiftedEulerOperatorApply operator shift value by
      exact eulerOperatorApply_comp_shift operator shift value]
    rw [← eulerOperatorApply_X_pow_mul]
    exact hrelation
  exact (mul_eq_zero.mp hproduct).resolve_left
    (pow_ne_zero shift PowerSeries.X_ne_zero)

theorem iterate_eulerDerivative_C_mul
    (scalar : ℚ) (order : ℕ) (value : ℚ⟦X⟧) :
    eulerDerivative^[order] (PowerSeries.C scalar * value) =
      PowerSeries.C scalar * eulerDerivative^[order] value := by
  change eulerDerivative^[order]
      (algebraMap ℚ ℚ⟦X⟧ scalar * value) =
    algebraMap ℚ ℚ⟦X⟧ scalar * eulerDerivative^[order] value
  rw [← Algebra.smul_def, ← Algebra.smul_def]
  exact iterate_eulerDerivative_smul scalar order value

theorem eulerOperatorApply_C_mul_value
    (operator : Polynomial (Polynomial ℚ))
    (scalar : ℚ) (value : ℚ⟦X⟧) :
    eulerOperatorApply operator (PowerSeries.C scalar * value) =
      PowerSeries.C scalar * eulerOperatorApply operator value := by
  induction operator using Polynomial.induction_on' with
  | add left right leftIH rightIH =>
      rw [eulerOperatorApply_add, eulerOperatorApply_add,
        leftIH, rightIH, mul_add]
  | monomial order coefficient =>
      unfold eulerOperatorApply
      rw [Polynomial.sum_monomial_index,
        Polynomial.sum_monomial_index]
      · rw [iterate_eulerDerivative_C_mul]
        ring
      · simp
      · simp

theorem EulerDFinite.cancel_C_mul
    {value : ℚ⟦X⟧} (scalar : ℚ) (hscalar : scalar ≠ 0)
    (hfinite : EulerDFinite (PowerSeries.C scalar * value)) :
    EulerDFinite value := by
  rw [eulerDFinite_iff_operator] at hfinite ⊢
  obtain ⟨operator, hoperator, hrelation⟩ := hfinite
  refine ⟨operator, hoperator, ?_⟩
  have hproduct : PowerSeries.C scalar *
      eulerOperatorApply operator value = 0 := by
    rw [← eulerOperatorApply_C_mul_value]
    exact hrelation
  have hCne : PowerSeries.C scalar ≠ 0 := by
    intro hzero
    apply hscalar
    apply PowerSeries.C_injective
    simpa using hzero
  exact (mul_eq_zero.mp hproduct).resolve_left hCne

theorem generalUnrestrictedFactorialSeries_even_eulerDFinite
    (halfDimension : ℕ) (hhalf : 1 ≤ halfDimension) :
    EulerDFinite
      (generalUnrestrictedFactorialSeries (2 * halfDimension - 1)) := by
  have hfinite :=
    (generalClosedEvenAssembly_besselGenerated halfDimension).eulerDFinite
  rw [← generalUnrestrictedFactorialSeries_even_closed
    halfDimension hhalf] at hfinite
  have hfactorial : (halfDimension.factorial : ℚ⟦X⟧) =
      PowerSeries.C (halfDimension.factorial : ℚ) := by
    exact (map_natCast PowerSeries.C halfDimension.factorial).symm
  rw [hfactorial] at hfinite
  have hshifted := EulerDFinite.cancel_C_mul
    (halfDimension.factorial : ℚ) (by positivity) hfinite
  exact EulerDFinite.cancel_X_pow
    (staircaseWeight (2 * halfDimension - 1)) hshifted

theorem generalUnrestrictedFactorialSeries_odd_eulerDFinite
    (halfDimension : ℕ) :
    EulerDFinite
      (generalUnrestrictedFactorialSeries (2 * halfDimension)) := by
  have hfinite :=
    (generalClosedOddAssembly_besselGenerated halfDimension).eulerDFinite
  rw [← generalUnrestrictedFactorialSeries_odd_closed
    halfDimension] at hfinite
  have hfactorial : (halfDimension.factorial : ℚ⟦X⟧) =
      PowerSeries.C (halfDimension.factorial : ℚ) := by
    exact (map_natCast PowerSeries.C halfDimension.factorial).symm
  rw [hfactorial] at hfinite
  have hshifted := EulerDFinite.cancel_C_mul
    (halfDimension.factorial : ℚ) (by positivity) hfinite
  exact EulerDFinite.cancel_X_pow
    (staircaseWeight (2 * halfDimension)) hshifted

end FibonacciRibbonKernel
