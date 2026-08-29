import FibonacciRibbonKernel.FullAllPlusAsymptotic

namespace FibonacciRibbonKernel

open Filter
open scoped BigOperators

noncomputable def cosineVandermondeWeight
    (dimension : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  ∏ upper : Fin dimension,
    ∏ lower ∈ Finset.Iio upper,
      (Real.cos (angles upper) - Real.cos (angles lower)) ^ 2

noncomputable def evenWeylAngleWeight
    (dimension : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  cosineVandermondeWeight dimension angles *
    ∏ coordinate, (1 + Real.cos (angles coordinate))

noncomputable def oddWeylAngleWeight
    (dimension : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  cosineVandermondeWeight dimension angles *
    ∏ coordinate,
      (1 - Real.cos (angles coordinate)) *
        (1 + Real.cos (angles coordinate))

noncomputable def scaledCosineVandermondeWeight
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  ∏ upper : Fin dimension,
    ∏ lower ∈ Finset.Iio upper,
      ((index + 1 : ℝ) *
        (Real.cos (coordinates upper / Real.sqrt (index + 1 : ℝ)) -
          Real.cos (coordinates lower / Real.sqrt (index + 1 : ℝ)))) ^ 2

noncomputable def quadraticVandermondeWeight
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  ∏ upper : Fin dimension,
    ∏ lower ∈ Finset.Iio upper,
      ((coordinates lower ^ 2 - coordinates upper ^ 2) / 2) ^ 2

noncomputable def evenScaledWeylWeight
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  scaledCosineVandermondeWeight dimension index coordinates *
    allPlusScaledWeight dimension index coordinates

noncomputable def evenLimitWeylWeight
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  quadraticVandermondeWeight dimension coordinates * (2 : ℝ) ^ dimension

noncomputable def oddScaledWeylWeight
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  scaledCosineVandermondeWeight dimension index coordinates *
    ∏ coordinate,
      ((index + 1 : ℝ) *
          (1 - Real.cos
            (coordinates coordinate / Real.sqrt (index + 1 : ℝ)))) *
        (1 + Real.cos
          (coordinates coordinate / Real.sqrt (index + 1 : ℝ)))

noncomputable def oddLimitWeylWeight
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) : ℝ :=
  quadraticVandermondeWeight dimension coordinates *
    ∏ coordinate, coordinates coordinate ^ 2

theorem tendsto_scaledCosineDifference
    (left right : ℝ) :
    Tendsto
      (fun index : ℕ =>
        (index + 1 : ℝ) *
          (Real.cos (left / Real.sqrt (index + 1 : ℝ)) -
            Real.cos (right / Real.sqrt (index + 1 : ℝ))))
      atTop (nhds ((right ^ 2 - left ^ 2) / 2)) := by
  let leftCos : ℕ → ℝ := fun index =>
    Real.cos (left / Real.sqrt (index + 1 : ℝ))
  let rightCos : ℕ → ℝ := fun index =>
    Real.cos (right / Real.sqrt (index + 1 : ℝ))
  have hleft : Tendsto
      (fun index : ℕ => (index + 1 : ℝ) * (leftCos index - 1))
      atTop (nhds (-(left ^ 2) / 2)) := by
    exact tendsto_cos_sqrt_quadratic left
  have hright : Tendsto
      (fun index : ℕ => (index + 1 : ℝ) * (rightCos index - 1))
      atTop (nhds (-(right ^ 2) / 2)) := by
    exact tendsto_cos_sqrt_quadratic right
  have hsub := hleft.sub hright
  change Tendsto
    (fun index : ℕ => (index + 1 : ℝ) *
      (leftCos index - rightCos index))
    atTop (nhds ((right ^ 2 - left ^ 2) / 2))
  convert hsub using 1 <;> ring

theorem tendsto_scaledCosineVandermondeWeight
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) :
    Tendsto
      (fun index =>
        scaledCosineVandermondeWeight dimension index coordinates)
      atTop (nhds (quadraticVandermondeWeight dimension coordinates)) := by
  unfold scaledCosineVandermondeWeight quadraticVandermondeWeight
  apply tendsto_finsetProd
  intro upper _hupper
  apply tendsto_finsetProd
  intro lower _hlower
  exact (tendsto_scaledCosineDifference
    (coordinates upper) (coordinates lower)).pow 2

theorem tendsto_evenScaledWeylWeight
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) :
    Tendsto (fun index => evenScaledWeylWeight dimension index coordinates)
      atTop (nhds (evenLimitWeylWeight dimension coordinates)) := by
  unfold evenScaledWeylWeight evenLimitWeylWeight
  exact (tendsto_scaledCosineVandermondeWeight dimension coordinates).mul
    (tendsto_allPlusScaledWeight dimension coordinates)

theorem tendsto_scaledOddCoordinateWeight (value : ℝ) :
    Tendsto
      (fun index : ℕ =>
        ((index + 1 : ℝ) *
            (1 - Real.cos (value / Real.sqrt (index + 1 : ℝ)))) *
          (1 + Real.cos (value / Real.sqrt (index + 1 : ℝ))))
      atTop (nhds (value ^ 2)) := by
  have hminus : Tendsto
      (fun index : ℕ =>
        (index + 1 : ℝ) *
          (1 - Real.cos (value / Real.sqrt (index + 1 : ℝ))))
      atTop (nhds (value ^ 2 / 2)) := by
    have h := tendsto_cos_sqrt_quadratic value
    convert h.neg using 1 <;> ring
  have hplus : Tendsto
      (fun index : ℕ =>
        1 + Real.cos (value / Real.sqrt (index + 1 : ℝ)))
      atTop (nhds 2) := by
    have hconstant : Tendsto (fun _ : ℕ => value)
        atTop (nhds value) := tendsto_const_nhds
    have hsqrt : Tendsto (fun index : ℕ => Real.sqrt (index + 1 : ℝ))
        atTop atTop := by
      have hcast : Tendsto (fun index : ℕ => (index + 1 : ℝ))
          atTop atTop := by
        have hbase := tendsto_natCast_atTop_atTop (R := ℝ)
        have hshift := hbase.comp (tendsto_add_atTop_nat 1)
        apply hshift.congr'
        filter_upwards with index
        simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
      exact Real.tendsto_sqrt_atTop.comp hcast
    have hzero := hconstant.div_atTop hsqrt
    have hcosRaw := Real.continuous_cos.continuousAt.tendsto.comp hzero
    rw [Real.cos_zero] at hcosRaw
    have hcos : Tendsto
        (fun index : ℕ =>
          Real.cos (value / Real.sqrt (index + 1 : ℝ)))
        atTop (nhds 1) := by
      apply hcosRaw.congr'
      filter_upwards with index
      rfl
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa only [one_add_one_eq_two] using hone.add hcos
  convert hminus.mul hplus using 1
  · ring_nf

theorem tendsto_oddScaledWeylWeight
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) :
    Tendsto (fun index => oddScaledWeylWeight dimension index coordinates)
      atTop (nhds (oddLimitWeylWeight dimension coordinates)) := by
  unfold oddScaledWeylWeight oddLimitWeylWeight
  apply (tendsto_scaledCosineVandermondeWeight dimension coordinates).mul
  apply tendsto_finsetProd
  intro coordinate _hcoordinate
  exact tendsto_scaledOddCoordinateWeight (coordinates coordinate)

theorem evenWeylAngleWeight_nonneg
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    0 ≤ evenWeylAngleWeight dimension angles := by
  unfold evenWeylAngleWeight cosineVandermondeWeight
  apply mul_nonneg
  · positivity
  · apply Finset.prod_nonneg
    intro coordinate _hcoordinate
    linarith [Real.neg_one_le_cos (angles coordinate)]

theorem oddWeylAngleWeight_nonneg
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    0 ≤ oddWeylAngleWeight dimension angles := by
  unfold oddWeylAngleWeight cosineVandermondeWeight
  apply mul_nonneg
  · positivity
  · apply Finset.prod_nonneg
    intro coordinate _hcoordinate
    exact mul_nonneg
      (sub_nonneg.2 (Real.cos_le_one _))
      (by linarith [Real.neg_one_le_cos (angles coordinate)])

end FibonacciRibbonKernel
