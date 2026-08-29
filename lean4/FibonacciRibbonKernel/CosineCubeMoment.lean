import FibonacciRibbonKernel.CosineMomentIteration

namespace FibonacciRibbonKernel

noncomputable def cosineMomentIdentity (power : ℕ) : ℝ :=
  if power = 0 then 1 else 0

noncomputable def iteratedPlusCosineMoment : ℕ → ℕ → ℝ
  | 0, power => cosineMomentIdentity power
  | factorCount + 1, power =>
      addCosineFactorIntegral true (iteratedPlusCosineMoment factorCount) power

noncomputable def cosineCubeMoment (plusPower : ℕ) : ℕ → ℕ → ℝ
  | 0, power => iteratedPlusCosineMoment plusPower power
  | minusPower + 1, power =>
      addCosineFactorIntegral false
        (cosineCubeMoment plusPower minusPower) power

theorem iteratedPlusCosineMoment_eq_binomialMomentPower
    (factorCount power : ℕ) :
    iteratedPlusCosineMoment factorCount power =
      binomialMomentPower besselPlusFactorialCoeffReal factorCount power := by
  induction factorCount generalizing power with
  | zero => rfl
  | succ factorCount inductionHypothesis =>
      unfold iteratedPlusCosineMoment binomialMomentPower
      rw [addCosineFactorIntegral_eq_binomialConvolution]
      unfold cosineFactorMoment
      change binomialConvolutionReal (iteratedPlusCosineMoment factorCount)
          besselPlusFactorialCoeffReal power = _
      congr 1
      funext current
      exact inductionHypothesis current

theorem cosineCubeMoment_eq_factorialScaledCoeffReal
    (plusPower minusPower power : ℕ) :
    cosineCubeMoment plusPower minusPower power =
      factorialScaledCoeffReal
        ((besselJ0 + besselJ1) ^ plusPower *
          (besselJ0 - besselJ1) ^ minusPower) power := by
  induction minusPower generalizing power with
  | zero =>
      unfold cosineCubeMoment
      rw [iteratedPlusCosineMoment_eq_binomialMomentPower]
      rw [pow_zero, mul_one, factorialScaledCoeffReal_pow]
      congr 1
  | succ minusPower inductionHypothesis =>
      unfold cosineCubeMoment
      rw [addCosineFactorIntegral_eq_binomialConvolution]
      unfold cosineFactorMoment
      change binomialConvolutionReal (cosineCubeMoment plusPower minusPower)
          besselMinusFactorialCoeffReal power = _
      rw [pow_succ]
      rw [← mul_assoc, factorialScaledCoeffReal_mul]
      congr 1
      funext current
      exact inductionHypothesis current

theorem cosineCubeMoment_eq_signedCosineMoment
    (plusPower minusPower power : ℕ) :
    cosineCubeMoment plusPower minusPower power =
      signedCosineMoment plusPower minusPower power := by
  rw [cosineCubeMoment_eq_factorialScaledCoeffReal,
    factorialScaledCoeffReal_signed_product]

theorem besselSpectralFactorialCoeffReal_eq_cosineCubeMoment
    (degree coefficient : ℕ) (scaleIndex : Fin (degree + 1)) :
    (besselSpectralFactorialCoeff degree coefficient scaleIndex : ℝ) =
      cosineCubeMoment (degree - scaleIndex.val) scaleIndex.val coefficient := by
  rw [besselSpectralFactorialCoeffReal_eq_signedCosineMoment,
    cosineCubeMoment_eq_signedCosineMoment]

theorem cosineCubeMoment_plus_succ
    (plusPower minusPower power : ℕ) :
    cosineCubeMoment (plusPower + 1) minusPower power =
      addCosineFactorIntegral true
        (cosineCubeMoment plusPower minusPower) power := by
  rw [cosineCubeMoment_eq_factorialScaledCoeffReal,
    addCosineFactorIntegral_eq_binomialConvolution]
  unfold cosineFactorMoment
  change factorialScaledCoeffReal
      ((besselJ0 + besselJ1) ^ (plusPower + 1) *
        (besselJ0 - besselJ1) ^ minusPower) power =
    binomialConvolutionReal (cosineCubeMoment plusPower minusPower)
      besselPlusFactorialCoeffReal power
  have hproduct :
      (besselJ0 + besselJ1) ^ (plusPower + 1) *
          (besselJ0 - besselJ1) ^ minusPower =
        ((besselJ0 + besselJ1) ^ plusPower *
          (besselJ0 - besselJ1) ^ minusPower) *
            (besselJ0 + besselJ1) := by
    rw [pow_succ]
    ring
  rw [hproduct, factorialScaledCoeffReal_mul]
  congr 1
  · funext current
    exact (cosineCubeMoment_eq_factorialScaledCoeffReal
      plusPower minusPower current).symm

theorem cosineCubeMoment_minus_succ
    (plusPower minusPower power : ℕ) :
    cosineCubeMoment plusPower (minusPower + 1) power =
      addCosineFactorIntegral false
        (cosineCubeMoment plusPower minusPower) power := by
  rw [cosineCubeMoment_eq_factorialScaledCoeffReal,
    addCosineFactorIntegral_eq_binomialConvolution]
  unfold cosineFactorMoment
  change factorialScaledCoeffReal
      ((besselJ0 + besselJ1) ^ plusPower *
        (besselJ0 - besselJ1) ^ (minusPower + 1)) power =
    binomialConvolutionReal (cosineCubeMoment plusPower minusPower)
      besselMinusFactorialCoeffReal power
  rw [pow_succ, ← mul_assoc, factorialScaledCoeffReal_mul]
  congr 1
  · funext current
    exact (cosineCubeMoment_eq_factorialScaledCoeffReal
      plusPower minusPower current).symm

end FibonacciRibbonKernel
