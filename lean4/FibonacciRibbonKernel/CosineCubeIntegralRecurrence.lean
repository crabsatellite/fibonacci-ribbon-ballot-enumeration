import FibonacciRibbonKernel.CosineCubeInnerExpansion

namespace FibonacciRibbonKernel

open MeasureTheory
open scoped BigOperators Interval

theorem integral_cosineIntervalMeasure_eq_interval (function : ℝ → ℝ) :
    (∫ angle : ℝ, function angle ∂cosineIntervalMeasure) =
      ∫ angle in (0 : ℝ)..Real.pi, function angle := by
  unfold cosineIntervalMeasure
  rw [intervalIntegral.integral_of_le Real.pi_pos.le]

theorem cosineCubeIntegralMoment_plus_succ
    (plusPower minusPower power : ℕ) :
    cosineCubeIntegralMoment (plusPower + 1) minusPower power =
      addCosineFactorIntegral true
        (cosineCubeIntegralMoment plusPower minusPower) power := by
  unfold cosineCubeIntegralMoment
  rw [cosineCubeRawIntegral_plus_fubini]
  have hinner :
      (fun angle : ℝ =>
        ∫ tail : Fin (plusPower + minusPower) → ℝ,
          cosineCubeRawIntegrand (plusPower + 1) minusPower power
            (cosinePlusCons plusPower minusPower angle tail)
          ∂cosineCubeProductMeasure (plusPower + minusPower)) =
      fun angle : ℝ =>
        cosineFactorWeight true angle *
          ∑ index : Fin (power + 1),
            (Nat.choose power index.val : ℝ) *
              (2 * Real.cos angle) ^ (power - index.val) *
              (∫ tail : Fin (plusPower + minusPower) → ℝ,
                cosineCubeRawIntegrand plusPower minusPower index.val tail
                ∂cosineCubeProductMeasure (plusPower + minusPower)) := by
    funext angle
    exact cosineCubeRawInner_plus_expand plusPower minusPower power angle
  rw [hinner, integral_cosineIntervalMeasure_eq_interval]
  unfold addCosineFactorIntegral momentTranslate
  rw [show (plusPower + 1) + minusPower =
      (plusPower + minusPower) + 1 by omega, pow_succ]
  rw [mul_comm ((1 / Real.pi) ^ (plusPower + minusPower)) (1 / Real.pi),
    mul_assoc]
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro angle _hangle
  dsimp only
  rw [← mul_assoc]
  rw [Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _hindex
  ring

theorem cosineCubeIntegralMoment_zero_zero (power : ℕ) :
    cosineCubeIntegralMoment 0 0 power = cosineMomentIdentity power := by
  unfold cosineCubeIntegralMoment cosineCubeRawIntegrand
  unfold cosineCubeProductMeasure
  rw [Measure.pi_of_empty
    (fun _ : Fin 0 => cosineIntervalMeasure)
    (fun coordinate : Fin 0 => Fin.elim0 coordinate)]
  by_cases hpower : power = 0
  · subst power
    simp [cosineCubeScale, cosineCubeWeight, cosineMomentIdentity]
  · simp [cosineCubeScale, cosineCubeWeight,
      cosineMomentIdentity, hpower]

theorem cosineCubeIntegralMoment_minus_succ
    (minusPower power : ℕ) :
    cosineCubeIntegralMoment 0 (minusPower + 1) power =
      addCosineFactorIntegral false
        (cosineCubeIntegralMoment 0 minusPower) power := by
  unfold cosineCubeIntegralMoment
  rw [cosineCubeRawIntegral_minus_fubini]
  have hinner :
      (fun angle : ℝ =>
        ∫ tail : Fin (0 + minusPower) → ℝ,
          cosineCubeRawIntegrand 0 (minusPower + 1) power
            (cosineMinusCons minusPower angle tail)
          ∂cosineCubeProductMeasure (0 + minusPower)) =
      fun angle : ℝ =>
        cosineFactorWeight false angle *
          ∑ index : Fin (power + 1),
            (Nat.choose power index.val : ℝ) *
              (2 * Real.cos angle) ^ (power - index.val) *
              (∫ tail : Fin (0 + minusPower) → ℝ,
                cosineCubeRawIntegrand 0 minusPower index.val tail
                ∂cosineCubeProductMeasure (0 + minusPower)) := by
    funext angle
    exact cosineCubeRawInner_minus_expand minusPower power angle
  rw [hinner, integral_cosineIntervalMeasure_eq_interval]
  unfold addCosineFactorIntegral momentTranslate
  rw [show 0 + (minusPower + 1) = (0 + minusPower) + 1 by omega,
    pow_succ]
  rw [mul_comm ((1 / Real.pi) ^ (0 + minusPower)) (1 / Real.pi),
    mul_assoc]
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro angle _hangle
  dsimp only
  rw [← mul_assoc]
  rw [Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _hindex
  ring

end FibonacciRibbonKernel
