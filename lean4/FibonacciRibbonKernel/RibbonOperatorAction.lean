import FibonacciRibbonKernel.RibbonOperatorPullback

namespace FibonacciRibbonKernel

open PowerSeries
open scoped Classical

theorem subst_eulerOperatorApply
    (operator : Polynomial (Polynomial ℚ)) (series : ℚ⟦X⟧) :
    PowerSeries.subst ribbonSubstitutionQ
        (eulerOperatorApply operator series) =
      operator.sum fun order coefficient =>
        PowerSeries.subst ribbonSubstitutionQ (coefficient : ℚ⟦X⟧) *
          PowerSeries.subst ribbonSubstitutionQ
            (eulerDerivative^[order] series) := by
  unfold eulerOperatorApply
  rw [Polynomial.sum_def]
  rw [← PowerSeries.coe_substAlgHom ribbonSubstitutionQ_hasSubst,
    map_sum]
  rw [Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro order horder
  rw [PowerSeries.coe_substAlgHom,
    PowerSeries.subst_mul ribbonSubstitutionQ_hasSubst]

theorem eulerOperatorApply_ribbonOperatorPullback
    (operator : Polynomial (Polynomial ℚ)) (series : ℚ⟦X⟧) :
    eulerOperatorApply (ribbonOperatorPullback operator) series =
      operator.sum fun order coefficient =>
        ((ribbonRationalNumerator
              (ribbonOperatorCoefficientBound operator) coefficient *
            ribbonQuadraticMinus ^
              (2 * (operator.natDegree - order)) : Polynomial ℚ) :
          ℚ⟦X⟧) *
          eulerOperatorApply (ribbonPullbackIterateOperator order) series := by
  unfold ribbonOperatorPullback
  dsimp only
  rw [Polynomial.sum_def]
  rw [eulerOperatorApply_finsetSum]
  rw [Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro order horder
  rw [eulerOperatorApply_C_mul]

/-- Exact whole-operator pullback identity.  Both polynomial denominators and
Euler-chain denominators are cleared, without a conditional adapter. -/
theorem ribbonOperatorPullback_exact
    (operator : Polynomial (Polynomial ℚ)) (series : ℚ⟦X⟧) :
    ribbonInverseQuadraticQ ^
        (ribbonOperatorCoefficientBound operator) *
      eulerOperatorApply (ribbonOperatorPullback operator)
        (PowerSeries.subst ribbonSubstitutionQ series) =
      (ribbonQuadraticMinus : ℚ⟦X⟧) ^
          (2 * operator.natDegree) *
        PowerSeries.subst ribbonSubstitutionQ
          (eulerOperatorApply operator series) := by
  rw [eulerOperatorApply_ribbonOperatorPullback,
    subst_eulerOperatorApply]
  rw [Polynomial.sum_def, Polynomial.sum_def,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro order horderSupport
  have horder : order ≤ operator.natDegree :=
    Polynomial.le_natDegree_of_mem_supp order horderSupport
  have hbound := operator_coefficient_natDegree_le_bound operator order
  have hnumerator := ribbonRationalNumerator_mul_inverse_pow
    (ribbonOperatorCoefficientBound operator)
      (operator.coeff order) hbound
  have hiterate := ribbonPullbackIterateOperator_exact order series
  have hexponent :
      2 * (operator.natDegree - order) + 2 * order =
        2 * operator.natDegree := by omega
  simp only [polynomial_coe_mul, polynomial_coe_pow_ps] at hnumerator ⊢
  calc
    ribbonInverseQuadraticQ ^
          (ribbonOperatorCoefficientBound operator) *
        ((ribbonRationalNumerator
              (ribbonOperatorCoefficientBound operator)
              (operator.coeff order) : ℚ⟦X⟧) *
          (ribbonQuadraticMinus : ℚ⟦X⟧) ^
              (2 * (operator.natDegree - order)) *
          eulerOperatorApply (ribbonPullbackIterateOperator order)
            (PowerSeries.subst ribbonSubstitutionQ series)) =
        ((ribbonRationalNumerator
              (ribbonOperatorCoefficientBound operator)
              (operator.coeff order) : ℚ⟦X⟧) *
            ribbonInverseQuadraticQ ^
              (ribbonOperatorCoefficientBound operator)) *
          ((ribbonQuadraticMinus : ℚ⟦X⟧) ^
              (2 * (operator.natDegree - order)) *
            eulerOperatorApply (ribbonPullbackIterateOperator order)
              (PowerSeries.subst ribbonSubstitutionQ series)) := by ring
    _ = PowerSeries.subst ribbonSubstitutionQ
            (operator.coeff order : ℚ⟦X⟧) *
          ((ribbonQuadraticMinus : ℚ⟦X⟧) ^
              (2 * (operator.natDegree - order)) *
            ((ribbonQuadraticMinus : ℚ⟦X⟧) ^ (2 * order) *
              PowerSeries.subst ribbonSubstitutionQ
                (eulerDerivative^[order] series))) := by
      rw [hnumerator, hiterate]
    _ = (ribbonQuadraticMinus : ℚ⟦X⟧) ^
            (2 * operator.natDegree) *
          (PowerSeries.subst ribbonSubstitutionQ
              (operator.coeff order : ℚ⟦X⟧) *
            PowerSeries.subst ribbonSubstitutionQ
              (eulerDerivative^[order] series)) := by
      have hpower :
          (ribbonQuadraticMinus : ℚ⟦X⟧) ^
                (2 * (operator.natDegree - order)) *
              (ribbonQuadraticMinus : ℚ⟦X⟧) ^ (2 * order) =
            (ribbonQuadraticMinus : ℚ⟦X⟧) ^
              (2 * operator.natDegree) := by
        rw [← pow_add, hexponent]
      calc
        PowerSeries.subst ribbonSubstitutionQ
              (operator.coeff order : ℚ⟦X⟧) *
            ((ribbonQuadraticMinus : ℚ⟦X⟧) ^
                (2 * (operator.natDegree - order)) *
              ((ribbonQuadraticMinus : ℚ⟦X⟧) ^ (2 * order) *
                PowerSeries.subst ribbonSubstitutionQ
                  (eulerDerivative^[order] series))) =
            ((ribbonQuadraticMinus : ℚ⟦X⟧) ^
                  (2 * (operator.natDegree - order)) *
                (ribbonQuadraticMinus : ℚ⟦X⟧) ^ (2 * order)) *
              (PowerSeries.subst ribbonSubstitutionQ
                  (operator.coeff order : ℚ⟦X⟧) *
                PowerSeries.subst ribbonSubstitutionQ
                  (eulerDerivative^[order] series)) := by ring
        _ = _ := by rw [hpower]

theorem ribbonInverseQuadraticQ_ne_zero :
    ribbonInverseQuadraticQ ≠ 0 := by
  intro hzero
  have hinverse := ribbonInverseQuadraticQ_mul_plus
  rw [hzero, zero_mul] at hinverse
  exact zero_ne_one hinverse

theorem EulerOperatorDFinite.subst_ribbonSubstitutionQ
    {series : ℚ⟦X⟧} (hfinite : EulerOperatorDFinite series) :
    EulerOperatorDFinite
      (PowerSeries.subst ribbonSubstitutionQ series) := by
  obtain ⟨operator, hoperator, hrelation⟩ := hfinite
  refine ⟨ribbonOperatorPullback operator,
    ribbonOperatorPullback_ne_zero hoperator, ?_⟩
  have hpullback := ribbonOperatorPullback_exact operator series
  rw [hrelation] at hpullback
  have hsubstZero :
      PowerSeries.subst ribbonSubstitutionQ (0 : ℚ⟦X⟧) = 0 := by
    rw [← PowerSeries.coe_substAlgHom ribbonSubstitutionQ_hasSubst]
    exact map_zero (PowerSeries.substAlgHom ribbonSubstitutionQ_hasSubst)
  rw [hsubstZero, mul_zero] at hpullback
  have hproduct :
      ribbonInverseQuadraticQ ^
          (ribbonOperatorCoefficientBound operator) *
        eulerOperatorApply (ribbonOperatorPullback operator)
          (PowerSeries.subst ribbonSubstitutionQ series) = 0 := by
    exact hpullback
  exact (mul_eq_zero.mp hproduct).resolve_left
    (pow_ne_zero _ ribbonInverseQuadraticQ_ne_zero)

theorem EulerDFinite.subst_ribbonSubstitutionQ
    {series : ℚ⟦X⟧} (hfinite : EulerDFinite series) :
    EulerDFinite (PowerSeries.subst ribbonSubstitutionQ series) := by
  rw [eulerDFinite_iff_operator] at hfinite ⊢
  exact EulerOperatorDFinite.subst_ribbonSubstitutionQ hfinite

end FibonacciRibbonKernel
