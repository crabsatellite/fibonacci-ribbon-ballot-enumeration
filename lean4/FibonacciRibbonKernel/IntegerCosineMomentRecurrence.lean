import FibonacciRibbonKernel.OddWeylRealGessel

namespace FibonacciRibbonKernel

open MeasureTheory

noncomputable def integerCosineMoment
    (order : ℤ) (power : ℕ) : ℝ :=
  (1 / Real.pi) *
    ∫ angle in (0 : ℝ)..Real.pi,
      (2 * Real.cos angle) ^ power *
        Real.cos ((order : ℝ) * angle)

theorem cos_int_mul_eq_cos_natAbs_mul
    (order : ℤ) (angle : ℝ) :
    Real.cos ((order : ℝ) * angle) =
      Real.cos ((order.natAbs : ℝ) * angle) := by
  cases order with
  | ofNat value => simp
  | negSucc value =>
      rw [Int.natAbs_negSucc]
      push_cast
      change Real.cos ((-((value : ℝ) + 1)) * angle) =
        Real.cos (((value : ℝ) + 1) * angle)
      rw [show (-((value : ℝ) + 1)) * angle =
          -(((value : ℝ) + 1) * angle) by ring,
        Real.cos_neg]

theorem integerCosineMoment_zero
    (order : ℤ) :
    integerCosineMoment order 0 = if order = 0 then 1 else 0 := by
  unfold integerCosineMoment
  simp only [pow_zero, one_mul]
  rw [show (fun angle : ℝ => Real.cos ((order : ℝ) * angle)) =
      fun angle => Real.cos ((order.natAbs : ℝ) * angle) by
    funext angle
    exact cos_int_mul_eq_cos_natAbs_mul order angle]
  rw [integral_cos_nat_mul]
  by_cases hzero : order = 0
  · subst order
    simp [Real.pi_ne_zero]
  · have habs : order.natAbs ≠ 0 := by
      rw [Int.natAbs_ne_zero]
      exact hzero
    rw [if_neg hzero, if_neg habs, mul_zero]

theorem two_cos_mul_cos_int
    (order : ℤ) (angle : ℝ) :
    2 * Real.cos angle * Real.cos ((order : ℝ) * angle) =
      Real.cos (((order + 1 : ℤ) : ℝ) * angle) +
        Real.cos (((order - 1 : ℤ) : ℝ) * angle) := by
  rw [show (((order + 1 : ℤ) : ℝ) * angle) =
      (order : ℝ) * angle + angle by push_cast; ring,
    show (((order - 1 : ℤ) : ℝ) * angle) =
      (order : ℝ) * angle - angle by push_cast; ring,
    Real.cos_add, Real.cos_sub]
  ring

theorem integerCosineMoment_succ
    (order : ℤ) (power : ℕ) :
    integerCosineMoment order (power + 1) =
      integerCosineMoment (order + 1) power +
        integerCosineMoment (order - 1) power := by
  unfold integerCosineMoment
  rw [show (fun angle : ℝ =>
      (2 * Real.cos angle) ^ power.succ *
        Real.cos ((order : ℝ) * angle)) =
      fun angle =>
        (2 * Real.cos angle) ^ power *
          (2 * Real.cos angle) * Real.cos ((order : ℝ) * angle) by
    funext angle
    rw [show power.succ = power + 1 by omega, pow_succ]]
  rw [show (fun angle : ℝ =>
      (2 * Real.cos angle) ^ power *
          (2 * Real.cos angle) * Real.cos ((order : ℝ) * angle)) =
      fun angle =>
        (2 * Real.cos angle) ^ power *
          (Real.cos (((order + 1 : ℤ) : ℝ) * angle) +
            Real.cos (((order - 1 : ℤ) : ℝ) * angle)) by
    funext angle
    calc
      (2 * Real.cos angle) ^ power * (2 * Real.cos angle) *
          Real.cos ((order : ℝ) * angle) =
        (2 * Real.cos angle) ^ power *
          (2 * Real.cos angle * Real.cos ((order : ℝ) * angle)) := by ring
      _ = _ := by rw [two_cos_mul_cos_int]]
  simp_rw [mul_add]
  rw [intervalIntegral.integral_add]
  · ring
  · exact Continuous.intervalIntegrable (μ := volume)
      (by fun_prop : Continuous (fun angle : ℝ =>
        (2 * Real.cos angle) ^ power *
          Real.cos (((order + 1 : ℤ) : ℝ) * angle))) 0 Real.pi
  · exact Continuous.intervalIntegrable (μ := volume)
      (by fun_prop : Continuous (fun angle : ℝ =>
        (2 * Real.cos angle) ^ power *
          Real.cos (((order - 1 : ℤ) : ℝ) * angle))) 0 Real.pi

theorem integerCosineMoment_neg
    (order : ℤ) (power : ℕ) :
    integerCosineMoment (-order) power =
      integerCosineMoment order power := by
  unfold integerCosineMoment
  apply congrArg (fun value : ℝ => (1 / Real.pi) * value)
  apply intervalIntegral.integral_congr
  intro angle _hangle
  push_cast
  rw [neg_mul, Real.cos_neg]

end FibonacciRibbonKernel
