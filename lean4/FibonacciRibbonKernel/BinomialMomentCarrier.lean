import FibonacciRibbonKernel.BesselSpectralMomentCarrier

namespace FibonacciRibbonKernel

open PowerSeries
open scoped BigOperators

noncomputable def binomialConvolutionReal
    (left right : ℕ → ℝ) (power : ℕ) : ℝ :=
  ∑ index : Fin (power + 1),
    (Nat.choose power index.val : ℝ) * left index.val *
      right (power - index.val)

noncomputable def binomialMomentPower
    (moment : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, power => if power = 0 then 1 else 0
  | factorCount + 1, power =>
      binomialConvolutionReal (binomialMomentPower moment factorCount)
        moment power

noncomputable def factorialScaledCoeffReal
    (series : ℚ⟦X⟧) (power : ℕ) : ℝ :=
  (factorialScaledCoeffQ series power : ℝ)

theorem factorialScaledCoeffReal_mul
    (left right : ℚ⟦X⟧) (power : ℕ) :
    factorialScaledCoeffReal (left * right) power =
      binomialConvolutionReal (factorialScaledCoeffReal left)
        (factorialScaledCoeffReal right) power := by
  have hreal := congrArg (fun value : ℚ => (value : ℝ))
    (factorialScaledCoeffQ_mul left right power)
  push_cast at hreal
  simpa only [factorialScaledCoeffReal, binomialConvolutionReal] using hreal

theorem factorialScaledCoeffReal_one (power : ℕ) :
    factorialScaledCoeffReal (1 : ℚ⟦X⟧) power =
      if power = 0 then 1 else 0 := by
  unfold factorialScaledCoeffReal factorialScaledCoeffQ
  by_cases hpower : power = 0
  · subst power
    simp
  · rw [if_neg hpower]
    simp [PowerSeries.coeff_one, hpower]

theorem factorialScaledCoeffReal_pow
    (series : ℚ⟦X⟧) (factorCount power : ℕ) :
    factorialScaledCoeffReal (series ^ factorCount) power =
      binomialMomentPower (factorialScaledCoeffReal series)
        factorCount power := by
  induction factorCount generalizing power with
  | zero =>
      rw [pow_zero, factorialScaledCoeffReal_one]
      rfl
  | succ factorCount inductionHypothesis =>
      rw [pow_succ, factorialScaledCoeffReal_mul]
      unfold binomialMomentPower
      unfold binomialConvolutionReal
      apply Finset.sum_congr rfl
      intro index _hindex
      rw [inductionHypothesis index.val]

theorem factorialScaledCoeffReal_exp (power : ℕ) :
    factorialScaledCoeffReal (PowerSeries.exp ℚ) power = 1 := by
  unfold factorialScaledCoeffReal
  rw [factorialScaledCoeffQ_exp]
  norm_num

theorem factorialScaledCoeffReal_plus (power : ℕ) :
    factorialScaledCoeffReal (besselJ0 + besselJ1) power =
      besselPlusFactorialCoeffReal power := by
  rfl

theorem factorialScaledCoeffReal_minus (power : ℕ) :
    factorialScaledCoeffReal (besselJ0 - besselJ1) power =
      besselMinusFactorialCoeffReal power := by
  rfl

noncomputable def signedCosineMoment
    (plusPower minusPower power : ℕ) : ℝ :=
  binomialConvolutionReal
    (binomialMomentPower besselPlusFactorialCoeffReal plusPower)
    (binomialMomentPower besselMinusFactorialCoeffReal minusPower)
    power

noncomputable def oddSignedCosineMoment
    (plusPower minusPower power : ℕ) : ℝ :=
  binomialConvolutionReal (fun _ => 1)
    (signedCosineMoment plusPower minusPower) power

theorem factorialScaledCoeffReal_signed_product
    (plusPower minusPower power : ℕ) :
    factorialScaledCoeffReal
        ((besselJ0 + besselJ1) ^ plusPower *
          (besselJ0 - besselJ1) ^ minusPower) power =
      signedCosineMoment plusPower minusPower power := by
  rw [factorialScaledCoeffReal_mul]
  unfold signedCosineMoment
  congr 1
  · funext coefficient
    rw [factorialScaledCoeffReal_pow]
    congr 1
  · funext coefficient
    rw [factorialScaledCoeffReal_pow]
    congr 1

theorem besselSpectralFactorialCoeffReal_eq_signedCosineMoment
    (degree coefficient : ℕ) (scaleIndex : Fin (degree + 1)) :
    (besselSpectralFactorialCoeff degree coefficient scaleIndex : ℝ) =
      signedCosineMoment (degree - scaleIndex.val) scaleIndex.val coefficient := by
  rw [besselSpectralFactorialCoeff_eq_signed_product]
  change factorialScaledCoeffReal
      ((besselJ0 + besselJ1) ^ (degree - scaleIndex.val) *
        (besselJ0 - besselJ1) ^ scaleIndex.val) coefficient = _
  exact factorialScaledCoeffReal_signed_product
    (degree - scaleIndex.val) scaleIndex.val coefficient

theorem oddBesselSpectralFactorialCoeffReal_eq_signedCosineMoment
    (degree coefficient : ℕ) (scaleIndex : Fin (degree + 1)) :
    (oddBesselSpectralFactorialCoeff degree coefficient scaleIndex : ℝ) =
      oddSignedCosineMoment (degree - scaleIndex.val) scaleIndex.val coefficient := by
  rw [oddBesselSpectralFactorialCoeff_eq_signed_product]
  change factorialScaledCoeffReal
      (PowerSeries.exp ℚ *
        ((besselJ0 + besselJ1) ^ (degree - scaleIndex.val) *
          (besselJ0 - besselJ1) ^ scaleIndex.val)) coefficient = _
  rw [factorialScaledCoeffReal_mul]
  have hright :
      factorialScaledCoeffReal
          ((besselJ0 + besselJ1) ^ (degree - scaleIndex.val) *
            (besselJ0 - besselJ1) ^ scaleIndex.val) =
        signedCosineMoment (degree - scaleIndex.val) scaleIndex.val := by
    funext power
    exact factorialScaledCoeffReal_signed_product
      (degree - scaleIndex.val) scaleIndex.val power
  rw [hright]
  unfold oddSignedCosineMoment
  congr 1
  funext power
  exact factorialScaledCoeffReal_exp power

end FibonacciRibbonKernel
