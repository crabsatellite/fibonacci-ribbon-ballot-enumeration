import FibonacciRibbonKernel.LiteralBesselDerivative

namespace FibonacciRibbonKernel

open PowerSeries

noncomputable def symmetricLiteralBesselJ (order : ℤ) : ℚ⟦X⟧ :=
  literalBesselJ order.natAbs

noncomputable def literalBesselWalkCoefficient
    (order : ℤ) (power : ℕ) : ℝ :=
  factorialScaledCoeffReal (symmetricLiteralBesselJ order) power

theorem derivative_symmetricLiteralBesselJ (order : ℤ) :
    PowerSeries.derivative ℚ (symmetricLiteralBesselJ order) =
      symmetricLiteralBesselJ (order + 1) +
        symmetricLiteralBesselJ (order - 1) := by
  cases order with
  | ofNat value =>
      cases value with
      | zero =>
          change PowerSeries.derivative ℚ (literalBesselJ 0) =
            literalBesselJ 1 + literalBesselJ 1
          rw [derivative_literalBesselJ_zero]
          ring
      | succ value =>
          unfold symmetricLiteralBesselJ
          have hbase : (Int.ofNat (value + 1)).natAbs = value + 1 := rfl
          have hplus : (Int.ofNat (value + 1) + 1).natAbs =
              value + 2 := by simp; omega
          have hminus : (Int.ofNat (value + 1) - 1).natAbs =
              value := by simp
          rw [hbase, hplus, hminus]
          rw [derivative_literalBesselJ_succ value]
          ring
  | negSucc value =>
      unfold symmetricLiteralBesselJ
      rw [show (Int.negSucc value).natAbs = value + 1 by omega,
        show (Int.negSucc value + 1).natAbs = value by omega,
        show (Int.negSucc value - 1).natAbs = value + 2 by omega]
      exact derivative_literalBesselJ_succ value

theorem factorialScaledCoeffReal_succ_eq_derivative
    (series : ℚ⟦X⟧) (power : ℕ) :
    factorialScaledCoeffReal series (power + 1) =
      factorialScaledCoeffReal (PowerSeries.derivative ℚ series) power := by
  unfold factorialScaledCoeffReal factorialScaledCoeffQ
  rw [PowerSeries.coeff_derivative, Nat.factorial_succ]
  push_cast
  ring

theorem literalBesselWalkCoefficient_succ
    (order : ℤ) (power : ℕ) :
    literalBesselWalkCoefficient order (power + 1) =
      literalBesselWalkCoefficient (order + 1) power +
        literalBesselWalkCoefficient (order - 1) power := by
  unfold literalBesselWalkCoefficient
  rw [factorialScaledCoeffReal_succ_eq_derivative,
    derivative_symmetricLiteralBesselJ,
    show factorialScaledCoeffReal
        (symmetricLiteralBesselJ (order + 1) +
          symmetricLiteralBesselJ (order - 1)) power =
      factorialScaledCoeffReal (symmetricLiteralBesselJ (order + 1)) power +
        factorialScaledCoeffReal (symmetricLiteralBesselJ (order - 1)) power by
      unfold factorialScaledCoeffReal factorialScaledCoeffQ
      rw [map_add]
      push_cast
      ring]

theorem literalBesselWalkCoefficient_zero (order : ℤ) :
    literalBesselWalkCoefficient order 0 =
      if order = 0 then 1 else 0 := by
  unfold literalBesselWalkCoefficient factorialScaledCoeffReal
    factorialScaledCoeffQ symmetricLiteralBesselJ
  simp only [Nat.factorial_zero, Nat.cast_one, one_mul]
  by_cases hzero : order = 0
  · subst order
    rw [if_pos rfl, Int.natAbs_zero,
      literalBesselJ_coeff_of_eq 0 0]
    norm_num
  · rw [if_neg hzero]
    have habs : order.natAbs ≠ 0 := by
      rw [Int.natAbs_ne_zero]
      exact hzero
    apply Rat.cast_eq_zero.mpr
    apply literalBesselJ_coeff_eq_zero
    rintro ⟨index, heq⟩
    have : order.natAbs = 0 := by omega
    exact habs this

theorem integerCosineMoment_eq_literalBesselWalkCoefficient
    (order : ℤ) (power : ℕ) :
    integerCosineMoment order power =
      literalBesselWalkCoefficient order power := by
  induction power generalizing order with
  | zero =>
      rw [integerCosineMoment_zero,
        literalBesselWalkCoefficient_zero]
  | succ power inductionHypothesis =>
      rw [integerCosineMoment_succ,
        literalBesselWalkCoefficient_succ,
        inductionHypothesis, inductionHypothesis]

end FibonacciRibbonKernel
