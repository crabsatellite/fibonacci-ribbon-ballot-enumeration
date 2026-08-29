import FibonacciRibbonKernel.CosineCubeIntegralRecurrence

namespace FibonacciRibbonKernel

theorem cosineCubeIntegralMoment_eq_cosineCubeMoment
    (plusPower minusPower power : ℕ) :
    cosineCubeIntegralMoment plusPower minusPower power =
      cosineCubeMoment plusPower minusPower power := by
  induction plusPower generalizing minusPower power with
  | zero =>
      induction minusPower generalizing power with
      | zero =>
          exact cosineCubeIntegralMoment_zero_zero power
      | succ minusPower inductionHypothesis =>
          rw [cosineCubeIntegralMoment_minus_succ,
            cosineCubeMoment_minus_succ]
          congr 1
          funext current
          exact inductionHypothesis current
  | succ plusPower inductionHypothesis =>
      rw [cosineCubeIntegralMoment_plus_succ,
        cosineCubeMoment_plus_succ]
      congr 1
      funext current
      exact inductionHypothesis minusPower current

theorem besselSpectralFactorialCoeffReal_eq_cosineCubeIntegral
    (degree coefficient : ℕ) (scaleIndex : Fin (degree + 1)) :
    (besselSpectralFactorialCoeff degree coefficient scaleIndex : ℝ) =
      cosineCubeIntegralMoment (degree - scaleIndex.val)
        scaleIndex.val coefficient := by
  rw [besselSpectralFactorialCoeffReal_eq_cosineCubeMoment,
    cosineCubeIntegralMoment_eq_cosineCubeMoment]

end FibonacciRibbonKernel
