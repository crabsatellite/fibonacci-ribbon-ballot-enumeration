import FibonacciRibbonKernel.FibonacciKernelLocalRatio
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

namespace FibonacciRibbonKernel

open Filter

theorem sin_eq_mul_sinc (value : ℝ) :
    Real.sin value = value * Real.sinc value := by
  by_cases hvalue : value = 0
  · subst value
    simp
  · rw [Real.sinc_of_ne_zero hvalue]
    field_simp

theorem cos_sub_one_eq_neg_two_mul_sin_half_sq (value : ℝ) :
    Real.cos value - 1 = -2 * Real.sin (value / 2) ^ 2 := by
  have hvalue : 2 * (value / 2) = value := by ring
  have hcos := Real.cos_two_mul (value / 2)
  rw [hvalue] at hcos
  have htrig := Real.sin_sq_add_cos_sq (value / 2)
  nlinarith

theorem tendsto_cos_sqrt_quadratic (value : ℝ) :
    Tendsto
      (fun index : ℕ =>
        (index + 1 : ℝ) *
          (Real.cos (value / Real.sqrt (index + 1 : ℝ)) - 1))
      atTop (nhds (-(value ^ 2) / 2)) := by
  have hcast : Tendsto (fun index : ℕ => (index + 1 : ℝ)) atTop atTop := by
    have hbase := tendsto_natCast_atTop_atTop (R := ℝ)
    have hshift := hbase.comp (tendsto_add_atTop_nat 1)
    apply hshift.congr'
    filter_upwards with index
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  have hsqrtRaw := Real.tendsto_sqrt_atTop.comp hcast
  have hsqrt : Tendsto (fun index : ℕ => Real.sqrt (index + 1 : ℝ))
      atTop atTop := by
    apply hsqrtRaw.congr'
    filter_upwards with index
    rfl
  have hhalf : Tendsto
      (fun index : ℕ => value / (2 * Real.sqrt (index + 1 : ℝ)))
      atTop (nhds 0) := by
    have hdenominator : Tendsto
        (fun index : ℕ => 2 * Real.sqrt (index + 1 : ℝ))
        atTop atTop :=
      (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).2 hsqrt
    exact tendsto_const_nhds.div_atTop hdenominator
  have hsinc : Tendsto
      (fun index : ℕ =>
        Real.sinc (value / (2 * Real.sqrt (index + 1 : ℝ))))
      atTop (nhds 1) := by
    have hsincRaw := Real.continuous_sinc.continuousAt.tendsto.comp hhalf
    rw [Real.sinc_zero] at hsincRaw
    apply hsincRaw.congr'
    filter_upwards with index
    rfl
  have hlimit := (hsinc.pow 2).const_mul (-(value ^ 2) / 2)
  have hlimit' : Tendsto
      (fun index : ℕ => (-(value ^ 2) / 2) *
        Real.sinc (value / (2 * Real.sqrt (index + 1 : ℝ))) ^ 2)
      atTop (nhds (-(value ^ 2) / 2)) := by
    simpa only [one_pow, mul_one] using hlimit
  apply hlimit'.congr'
  filter_upwards with index
  have hsqrtPos : 0 < Real.sqrt (index + 1 : ℝ) := by positivity
  have hsqrtSq : Real.sqrt (index + 1 : ℝ) ^ 2 = (index + 1 : ℝ) :=
    Real.sq_sqrt (by positivity)
  rw [cos_sub_one_eq_neg_two_mul_sin_half_sq,
    sin_eq_mul_sinc]
  field_simp [hsqrtPos.ne']
  rw [hsqrtSq]

end FibonacciRibbonKernel
