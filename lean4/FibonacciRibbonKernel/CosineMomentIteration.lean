import FibonacciRibbonKernel.FibonacciKernelLocalDomination

namespace FibonacciRibbonKernel

open MeasureTheory Real
open scoped BigOperators Interval

noncomputable def cosineFactorWeight (plusFactor : Bool) (angle : ℝ) : ℝ :=
  if plusFactor then 1 + Real.cos angle else 1 - Real.cos angle

noncomputable def cosineFactorMoment (plusFactor : Bool) (power : ℕ) : ℝ :=
  if plusFactor then besselPlusFactorialCoeffReal power
  else besselMinusFactorialCoeffReal power

noncomputable def momentTranslate
    (moment : ℕ → ℝ) (power : ℕ) (offset : ℝ) : ℝ :=
  ∑ index : Fin (power + 1),
    (Nat.choose power index.val : ℝ) * moment index.val *
      offset ^ (power - index.val)

noncomputable def addCosineFactorIntegral
    (plusFactor : Bool) (moment : ℕ → ℝ) (power : ℕ) : ℝ :=
  (1 / Real.pi) *
    ∫ angle in (0 : ℝ)..Real.pi,
      cosineFactorWeight plusFactor angle *
        momentTranslate moment power (2 * Real.cos angle)

theorem cosineFactorWeight_continuous (plusFactor : Bool) :
    Continuous (cosineFactorWeight plusFactor) := by
  unfold cosineFactorWeight
  split <;> fun_prop

theorem cosineFactorMoment_eq_integral
    (plusFactor : Bool) (power : ℕ) :
    cosineFactorMoment plusFactor power =
      (1 / Real.pi) *
        ∫ angle in (0 : ℝ)..Real.pi,
          (2 * Real.cos angle) ^ power *
            cosineFactorWeight plusFactor angle := by
  unfold cosineFactorMoment cosineFactorWeight
  split
  · exact besselPlusFactorialCoeffReal_eq_integral power
  · exact besselMinusFactorialCoeffReal_eq_integral power

theorem addCosineFactorIntegral_eq_binomialConvolution
    (plusFactor : Bool) (moment : ℕ → ℝ) (power : ℕ) :
    addCosineFactorIntegral plusFactor moment power =
      binomialConvolutionReal moment (cosineFactorMoment plusFactor) power := by
  let term : Fin (power + 1) → ℝ → ℝ := fun index angle =>
    ((Nat.choose power index.val : ℝ) * moment index.val) *
      ((2 * Real.cos angle) ^ (power - index.val) *
        cosineFactorWeight plusFactor angle)
  have hterm : ∀ index : Fin (power + 1),
      IntervalIntegrable (term index) volume 0 Real.pi := by
    intro index
    apply Continuous.intervalIntegrable
    exact continuous_const.mul
      (((continuous_const.mul Real.continuous_cos).pow _).mul
        (cosineFactorWeight_continuous plusFactor))
  calc
    addCosineFactorIntegral plusFactor moment power =
        (1 / Real.pi) *
          ∫ angle in (0 : ℝ)..Real.pi,
            ∑ index : Fin (power + 1), term index angle := by
      unfold addCosineFactorIntegral momentTranslate term
      congr 1
      apply intervalIntegral.integral_congr
      intro angle _hangle
      dsimp only
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro index _hindex
      ring
    _ = (1 / Real.pi) *
        ∑ index : Fin (power + 1),
          ∫ angle in (0 : ℝ)..Real.pi, term index angle := by
      rw [intervalIntegral.integral_finsetSum]
      intro index _hindex
      exact hterm index
    _ = ∑ index : Fin (power + 1),
        (Nat.choose power index.val : ℝ) * moment index.val *
          ((1 / Real.pi) *
            ∫ angle in (0 : ℝ)..Real.pi,
              (2 * Real.cos angle) ^ (power - index.val) *
                cosineFactorWeight plusFactor angle) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro index _hindex
      unfold term
      rw [intervalIntegral.integral_const_mul]
      ring
    _ = binomialConvolutionReal moment
        (cosineFactorMoment plusFactor) power := by
      unfold binomialConvolutionReal
      apply Finset.sum_congr rfl
      intro index _hindex
      rw [cosineFactorMoment_eq_integral]

end FibonacciRibbonKernel
