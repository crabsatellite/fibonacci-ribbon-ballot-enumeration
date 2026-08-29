import FibonacciRibbonKernel.BinomialMomentCarrier

namespace FibonacciRibbonKernel

open scoped BigOperators

theorem besselJ0FactorialCoeffReal_odd (half : ℕ) :
    besselJ0FactorialCoeffReal (2 * half + 1) = 0 := by
  unfold besselJ0FactorialCoeffReal besselJ0FactorialCoeffQ
  rw [besselJ0_coeff_odd]
  simp

theorem besselJ1FactorialCoeffReal_even (half : ℕ) :
    besselJ1FactorialCoeffReal (2 * half) = 0 := by
  unfold besselJ1FactorialCoeffReal besselJ1FactorialCoeffQ
  rw [besselJ1_coeff_even]
  simp

theorem besselMinusFactorialCoeffReal_eq_sign_mul_plus (power : ℕ) :
    besselMinusFactorialCoeffReal power =
      (-1 : ℝ) ^ power * besselPlusFactorialCoeffReal power := by
  obtain ⟨half, rfl | rfl⟩ := Nat.even_or_odd' power
  · rw [besselMinusFactorialCoeffReal_eq_sub,
      besselPlusFactorialCoeffReal_eq_sum,
      besselJ1FactorialCoeffReal_even]
    have hsign : (-1 : ℝ) ^ (2 * half) = 1 := by
      rw [pow_mul]
      norm_num
    rw [hsign]
    ring
  · rw [besselMinusFactorialCoeffReal_eq_sub,
      besselPlusFactorialCoeffReal_eq_sum,
      besselJ0FactorialCoeffReal_odd]
    have hsign : (-1 : ℝ) ^ (2 * half + 1) = -1 := by
      rw [pow_add, pow_mul]
      norm_num
    rw [hsign]
    ring

theorem binomialConvolutionReal_sign
    (left right : ℕ → ℝ) (power : ℕ) :
    binomialConvolutionReal
        (fun index => (-1 : ℝ) ^ index * left index)
        (fun index => (-1 : ℝ) ^ index * right index) power =
      (-1 : ℝ) ^ power * binomialConvolutionReal left right power := by
  unfold binomialConvolutionReal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _hindex
  have hindex : index.val ≤ power := by omega
  have hsum : index.val + (power - index.val) = power := by omega
  have hsign :
      (-1 : ℝ) ^ index.val * (-1 : ℝ) ^ (power - index.val) =
        (-1 : ℝ) ^ power := by
    rw [← pow_add, hsum]
  dsimp only
  calc
    (Nat.choose power index.val : ℝ) *
          ((-1 : ℝ) ^ index.val * left index.val) *
          ((-1 : ℝ) ^ (power - index.val) * right (power - index.val)) =
        ((-1 : ℝ) ^ index.val * (-1 : ℝ) ^ (power - index.val)) *
          ((Nat.choose power index.val : ℝ) * left index.val *
            right (power - index.val)) := by ring
    _ = _ := by rw [hsign]

theorem binomialMomentPower_sign
    (moment : ℕ → ℝ) (factorCount power : ℕ) :
    binomialMomentPower (fun index => (-1 : ℝ) ^ index * moment index)
        factorCount power =
      (-1 : ℝ) ^ power * binomialMomentPower moment factorCount power := by
  induction factorCount generalizing power with
  | zero =>
      unfold binomialMomentPower
      by_cases hpower : power = 0
      · subst power
        simp
      · simp [hpower]
  | succ factorCount inductionHypothesis =>
      unfold binomialMomentPower
      have hleft :
          binomialMomentPower
              (fun index => (-1 : ℝ) ^ index * moment index) factorCount =
            fun index => (-1 : ℝ) ^ index *
              binomialMomentPower moment factorCount index := by
        funext index
        exact inductionHypothesis index
      rw [hleft, binomialConvolutionReal_sign]

theorem binomialMomentPower_minus_eq_sign_plus
    (factorCount power : ℕ) :
    binomialMomentPower besselMinusFactorialCoeffReal factorCount power =
      (-1 : ℝ) ^ power *
        binomialMomentPower besselPlusFactorialCoeffReal factorCount power := by
  have hmoment : besselMinusFactorialCoeffReal =
      fun index => (-1 : ℝ) ^ index * besselPlusFactorialCoeffReal index := by
    funext index
    exact besselMinusFactorialCoeffReal_eq_sign_mul_plus index
  rw [hmoment, binomialMomentPower_sign]

end FibonacciRibbonKernel
