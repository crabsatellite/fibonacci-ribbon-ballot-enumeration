import FibonacciRibbonKernel.EulerOperatorTransport

namespace FibonacciRibbonKernel

open PowerSeries
open scoped Classical

noncomputable def factorialUnscale (series : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  PowerSeries.mk fun degree =>
    (degree.factorial : ℚ) * PowerSeries.coeff degree series

@[simp] theorem factorialUnscale_coeff
    (series : ℚ⟦X⟧) (degree : ℕ) :
    PowerSeries.coeff degree (factorialUnscale series) =
      (degree.factorial : ℚ) * PowerSeries.coeff degree series := by
  simp [factorialUnscale]

noncomputable def generalUnrestrictedOrdinarySeriesQ (rank : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun degree => (unrestrictedCount rank degree : ℚ)

@[simp] theorem generalUnrestrictedOrdinarySeriesQ_coeff
    (rank degree : ℕ) :
    PowerSeries.coeff degree (generalUnrestrictedOrdinarySeriesQ rank) =
      (unrestrictedCount rank degree : ℚ) := by
  simp [generalUnrestrictedOrdinarySeriesQ]

theorem factorialUnscale_generalUnrestrictedFactorialSeries (rank : ℕ) :
    factorialUnscale (generalUnrestrictedFactorialSeries rank) =
      generalUnrestrictedOrdinarySeriesQ rank := by
  ext degree
  rw [factorialUnscale_coeff,
    generalUnrestrictedFactorialSeries_coeff,
    generalUnrestrictedOrdinarySeriesQ_coeff]
  have hfactorial : (degree.factorial : ℚ) ≠ 0 := by positivity
  field_simp

theorem factorialUnscale_add (left right : ℚ⟦X⟧) :
    factorialUnscale (left + right) =
      factorialUnscale left + factorialUnscale right := by
  ext degree
  simp [factorialUnscale_coeff, mul_add]

theorem factorialUnscale_finsetSum
    {index : Type*} [DecidableEq index]
    (indices : Finset index) (values : index → ℚ⟦X⟧) :
    factorialUnscale (∑ item ∈ indices, values item) =
      ∑ item ∈ indices, factorialUnscale (values item) := by
  induction indices using Finset.induction_on with
  | empty =>
      ext degree
      simp [factorialUnscale_coeff]
  | @insert item indices hitem ih =>
      simp only [Finset.sum_insert hitem]
      rw [factorialUnscale_add, ih]

theorem eulerDerivative_coeff (series : ℚ⟦X⟧) (degree : ℕ) :
    PowerSeries.coeff degree (eulerDerivative series) =
      (degree : ℚ) * PowerSeries.coeff degree series := by
  unfold eulerDerivative
  cases degree with
  | zero => simp
  | succ degree =>
      rw [show (X : ℚ⟦X⟧) = X ^ 1 by simp]
      rw [PowerSeries.coeff_X_pow_mul']
      rw [PowerSeries.coeff_derivative]
      push_cast
      ring

theorem eulerDerivative_iterate_coeff
    (series : ℚ⟦X⟧) (order degree : ℕ) :
    PowerSeries.coeff degree (eulerDerivative^[order] series) =
      (degree : ℚ) ^ order * PowerSeries.coeff degree series := by
  induction order with
  | zero => simp
  | succ order ih =>
      rw [Function.iterate_succ_apply', eulerDerivative_coeff, ih]
      ring

theorem factorialUnscale_eulerDerivative (series : ℚ⟦X⟧) :
    factorialUnscale (eulerDerivative series) =
      eulerDerivative (factorialUnscale series) := by
  ext degree
  rw [factorialUnscale_coeff, eulerDerivative_coeff,
    eulerDerivative_coeff, factorialUnscale_coeff]
  ring

theorem factorialUnscale_eulerDerivative_iterate
    (series : ℚ⟦X⟧) (order : ℕ) :
    factorialUnscale (eulerDerivative^[order] series) =
      eulerDerivative^[order] (factorialUnscale series) := by
  induction order with
  | zero => rfl
  | succ order ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [factorialUnscale_eulerDerivative, ih]

noncomputable def risingEulerApply : ℕ → ℚ⟦X⟧ → ℚ⟦X⟧
  | 0, series => series
  | shift + 1, series =>
      eulerDerivative (risingEulerApply shift series) +
        PowerSeries.C (shift + 1 : ℚ) * risingEulerApply shift series

noncomputable def risingFactorialQ (degree shift : ℕ) : ℚ :=
  ∏ offset ∈ Finset.range shift, (degree + offset + 1 : ℕ)

theorem risingFactorialQ_zero (degree : ℕ) :
    risingFactorialQ degree 0 = 1 := by
  simp [risingFactorialQ]

theorem risingFactorialQ_succ (degree shift : ℕ) :
    risingFactorialQ degree (shift + 1) =
      risingFactorialQ degree shift * (degree + shift + 1 : ℕ) := by
  unfold risingFactorialQ
  rw [Finset.prod_range_succ]

theorem risingFactorialQ_mul_factorial (degree shift : ℕ) :
    risingFactorialQ degree shift * (degree.factorial : ℚ) =
      ((degree + shift).factorial : ℚ) := by
  induction shift with
  | zero => simp [risingFactorialQ_zero]
  | succ shift ih =>
      rw [risingFactorialQ_succ,
        show degree + (shift + 1) = (degree + shift) + 1 by omega,
        Nat.factorial_succ]
      push_cast
      rw [← ih]
      ring

theorem risingEulerApply_coeff
    (shift : ℕ) (series : ℚ⟦X⟧) (degree : ℕ) :
    PowerSeries.coeff degree (risingEulerApply shift series) =
      risingFactorialQ degree shift *
        PowerSeries.coeff degree series := by
  induction shift with
  | zero =>
      rw [risingEulerApply, risingFactorialQ_zero, one_mul]
  | succ shift ih =>
      rw [risingEulerApply, map_add, eulerDerivative_coeff,
        PowerSeries.coeff_C_mul, ih]
      rw [risingFactorialQ_succ]
      push_cast
      ring

theorem factorialUnscale_X_pow_mul
    (shift : ℕ) (series : ℚ⟦X⟧) :
    factorialUnscale (X ^ shift * series) =
      X ^ shift * risingEulerApply shift (factorialUnscale series) := by
  ext degree
  by_cases hshift : shift ≤ degree
  · rw [factorialUnscale_coeff,
      PowerSeries.coeff_X_pow_mul' series shift degree,
      PowerSeries.coeff_X_pow_mul'
        (risingEulerApply shift (factorialUnscale series)) shift degree,
      if_pos hshift, if_pos hshift,
      risingEulerApply_coeff, factorialUnscale_coeff]
    have hfactorial : (degree.factorial : ℚ) =
        risingFactorialQ (degree - shift) shift *
          ((degree - shift).factorial : ℚ) := by
      rw [risingFactorialQ_mul_factorial]
      rw [Nat.sub_add_cancel hshift]
    rw [hfactorial]
    ring
  · rw [factorialUnscale_coeff,
      PowerSeries.coeff_X_pow_mul' series shift degree,
      PowerSeries.coeff_X_pow_mul'
        (risingEulerApply shift (factorialUnscale series)) shift degree,
      if_neg hshift, if_neg hshift, mul_zero]

end FibonacciRibbonKernel
