import FibonacciRibbonKernel.BorelDfiniteTransport
import Mathlib.RingTheory.PowerSeries.Derivative

namespace FibonacciRibbonKernel

open PowerSeries
open scoped Classical

noncomputable def ribbonSubstitutionQ : ℚ⟦X⟧ :=
  PowerSeries.map (Int.castRingHom ℚ) ribbonSubstitution

noncomputable def ribbonInverseQuadraticQ : ℚ⟦X⟧ :=
  PowerSeries.map (Int.castRingHom ℚ) substitutionDenominator

noncomputable def ribbonQuadraticPlus : Polynomial ℚ :=
  1 + Polynomial.X ^ 2

noncomputable def ribbonQuadraticMinus : Polynomial ℚ :=
  1 - Polynomial.X ^ 2

theorem ribbonSubstitutionQ_eq :
    ribbonSubstitutionQ = X * ribbonInverseQuadraticQ := by
  simp [ribbonSubstitutionQ, ribbonInverseQuadraticQ,
    ribbonSubstitution, map_mul]

theorem ribbonInverseQuadraticQ_mul_plus :
    ribbonInverseQuadraticQ * (ribbonQuadraticPlus : ℚ⟦X⟧) = 1 := by
  have hmapped := congrArg (PowerSeries.map (Int.castRingHom ℚ))
    substitutionDenominator_mul_one_add_X_sq
  simpa [ribbonInverseQuadraticQ, ribbonQuadraticPlus,
    map_mul, map_add, map_pow] using hmapped

theorem ribbonSubstitutionQ_constantCoeff :
    PowerSeries.constantCoeff ribbonSubstitutionQ = 0 := by
  rw [ribbonSubstitutionQ_eq]
  simp

theorem ribbonSubstitutionQ_hasSubst :
    PowerSeries.HasSubst ribbonSubstitutionQ :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    ribbonSubstitutionQ_constantCoeff

theorem eulerDerivative_one :
    eulerDerivative (1 : ℚ⟦X⟧) = 0 := by
  simp [eulerDerivative]

theorem eulerDerivative_X :
    eulerDerivative (X : ℚ⟦X⟧) = X := by
  simp [eulerDerivative]

theorem eulerDerivative_ribbonQuadraticPlus :
    eulerDerivative (ribbonQuadraticPlus : ℚ⟦X⟧) =
      (2 : ℚ⟦X⟧) * X ^ 2 := by
  calc
    eulerDerivative (ribbonQuadraticPlus : ℚ⟦X⟧) =
        ((Polynomial.X * ribbonQuadraticPlus.derivative :
          Polynomial ℚ) : ℚ⟦X⟧) :=
      eulerDerivative_polynomial ribbonQuadraticPlus
    _ = ((Polynomial.C (2 : ℚ) * Polynomial.X ^ 2 :
          Polynomial ℚ) : ℚ⟦X⟧) := by
      congr 1
      unfold ribbonQuadraticPlus
      norm_num
      ring
    _ = (2 : ℚ⟦X⟧) * X ^ 2 := by
      rw [polynomial_coe_mul, Polynomial.coe_C,
        polynomial_coe_pow_ps, Polynomial.coe_X]
      congr 1

theorem eulerDerivative_ribbonInverseQuadraticQ :
    (ribbonQuadraticPlus : ℚ⟦X⟧) *
        eulerDerivative ribbonInverseQuadraticQ =
      -((2 : ℚ⟦X⟧) * X ^ 2 * ribbonInverseQuadraticQ) := by
  have hderivative := congrArg eulerDerivative
    ribbonInverseQuadraticQ_mul_plus
  rw [eulerDerivative_mul, eulerDerivative_one,
    eulerDerivative_ribbonQuadraticPlus] at hderivative
  linear_combination hderivative

theorem ribbonSubstitutionQ_euler_chain_factor :
    (ribbonQuadraticPlus : ℚ⟦X⟧) *
        eulerDerivative ribbonSubstitutionQ =
      (ribbonQuadraticMinus : ℚ⟦X⟧) * ribbonSubstitutionQ := by
  rw [ribbonSubstitutionQ_eq, eulerDerivative_mul,
    eulerDerivative_X]
  have hderivative := eulerDerivative_ribbonInverseQuadraticQ
  have hplus : (ribbonQuadraticPlus : ℚ⟦X⟧) = 1 + X ^ 2 := by
    simp [ribbonQuadraticPlus]
  have hminus : (ribbonQuadraticMinus : ℚ⟦X⟧) = 1 - X ^ 2 := by
    simp [ribbonQuadraticMinus]
  rw [hplus] at hderivative ⊢
  rw [hminus]
  linear_combination X * hderivative

/-- Exact chain rule for the manuscript substitution `X/(1+X²)`, in a
denominator-cleared Euler form. -/
theorem ribbonSubstitutionQ_euler_chain (series : ℚ⟦X⟧) :
    (ribbonQuadraticPlus : ℚ⟦X⟧) *
        eulerDerivative
          (PowerSeries.subst ribbonSubstitutionQ series) =
      (ribbonQuadraticMinus : ℚ⟦X⟧) *
        PowerSeries.subst ribbonSubstitutionQ
          (eulerDerivative series) := by
  rw [show PowerSeries.subst ribbonSubstitutionQ
        (eulerDerivative series) =
      ribbonSubstitutionQ *
        PowerSeries.subst ribbonSubstitutionQ
          (PowerSeries.derivative ℚ series) by
    unfold eulerDerivative
    rw [PowerSeries.subst_mul ribbonSubstitutionQ_hasSubst,
      PowerSeries.subst_X ribbonSubstitutionQ_hasSubst]]
  unfold eulerDerivative
  rw [PowerSeries.derivative_subst ℚ ribbonSubstitutionQ_hasSubst]
  have hfactor := ribbonSubstitutionQ_euler_chain_factor
  unfold eulerDerivative at hfactor
  linear_combination
    (PowerSeries.subst ribbonSubstitutionQ
      (PowerSeries.derivative ℚ series)) * hfactor

end FibonacciRibbonKernel
