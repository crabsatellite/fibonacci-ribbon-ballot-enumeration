import FibonacciRibbonKernel.RibbonPullbackLeading

namespace FibonacciRibbonKernel

open PowerSeries
open scoped Classical

noncomputable def inverseRibbonSubstitutionQ : ℚ⟦X⟧ :=
  PowerSeries.map (Int.castRingHom ℚ) inverseRibbonSubstitution

theorem inverseRibbonSubstitutionQ_constantCoeff :
    PowerSeries.constantCoeff inverseRibbonSubstitutionQ = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    inverseRibbonSubstitutionQ, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply,
    inverseRibbonSubstitution_constantCoeff, map_zero]

theorem inverseRibbonSubstitutionQ_hasSubst :
    PowerSeries.HasSubst inverseRibbonSubstitutionQ :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    inverseRibbonSubstitutionQ_constantCoeff

theorem ribbonSubstitutionQ_subst_inverse :
    PowerSeries.subst inverseRibbonSubstitutionQ ribbonSubstitutionQ = X := by
  have hmapped := congrArg (PowerSeries.map (Int.castRingHom ℚ))
    ribbonSubstitution_subst_inverse
  calc
    PowerSeries.subst inverseRibbonSubstitutionQ ribbonSubstitutionQ =
        PowerSeries.map (Int.castRingHom ℚ)
          (PowerSeries.subst inverseRibbonSubstitution
            ribbonSubstitution) := by
      exact (PowerSeries.map_subst
        inverseRibbonSubstitution_hasSubst ribbonSubstitution).symm
    _ = X := by simpa using hmapped

theorem subst_ribbonSubstitutionQ_injective :
    Function.Injective (fun series : ℚ⟦X⟧ =>
      PowerSeries.subst ribbonSubstitutionQ series) := by
  intro left right hequal
  have hcomposed := congrArg
    (PowerSeries.subst inverseRibbonSubstitutionQ) hequal
  rw [PowerSeries.subst_comp_subst_apply
      ribbonSubstitutionQ_hasSubst inverseRibbonSubstitutionQ_hasSubst,
    PowerSeries.subst_comp_subst_apply
      ribbonSubstitutionQ_hasSubst inverseRibbonSubstitutionQ_hasSubst,
    ribbonSubstitutionQ_subst_inverse,
    PowerSeries.X_subst, PowerSeries.X_subst] at hcomposed
  exact hcomposed

noncomputable def ribbonRationalNumerator
    (bound : ℕ) (polynomial : Polynomial ℚ) : Polynomial ℚ :=
  polynomial.sum fun degree coefficient =>
    Polynomial.C coefficient * Polynomial.X ^ degree *
      ribbonQuadraticPlus ^ (bound - degree)

theorem ribbonQuadraticPlus_pow_mul_inverse_pow
    {degree bound : ℕ} (hdegree : degree ≤ bound) :
    (ribbonQuadraticPlus : ℚ⟦X⟧) ^ (bound - degree) *
        ribbonInverseQuadraticQ ^ bound =
      ribbonInverseQuadraticQ ^ degree := by
  have hsplit : degree + (bound - degree) = bound := by omega
  have hinverseSplit :
      ribbonInverseQuadraticQ ^ bound =
        ribbonInverseQuadraticQ ^ degree *
          ribbonInverseQuadraticQ ^ (bound - degree) := by
    rw [← pow_add, hsplit]
  calc
    (ribbonQuadraticPlus : ℚ⟦X⟧) ^ (bound - degree) *
        ribbonInverseQuadraticQ ^ bound =
        ribbonInverseQuadraticQ ^ degree *
          ((ribbonQuadraticPlus : ℚ⟦X⟧) *
            ribbonInverseQuadraticQ) ^ (bound - degree) := by
      rw [hinverseSplit, mul_pow]
      ring
    _ = ribbonInverseQuadraticQ ^ degree := by
      rw [show (ribbonQuadraticPlus : ℚ⟦X⟧) *
          ribbonInverseQuadraticQ = 1 by
        rw [mul_comm]
        exact ribbonInverseQuadraticQ_mul_plus]
      simp

theorem ribbonRationalNumerator_mul_inverse_pow
    (bound : ℕ) (polynomial : Polynomial ℚ)
    (hbound : polynomial.natDegree ≤ bound) :
    (ribbonRationalNumerator bound polynomial : ℚ⟦X⟧) *
        ribbonInverseQuadraticQ ^ bound =
      PowerSeries.subst ribbonSubstitutionQ (polynomial : ℚ⟦X⟧) := by
  rw [PowerSeries.subst_coe ribbonSubstitutionQ_hasSubst,
    Polynomial.aeval_def, Polynomial.eval₂_eq_sum]
  unfold ribbonRationalNumerator
  rw [Polynomial.sum_def]
  change Polynomial.coeToPowerSeries.ringHom
      (∑ degree ∈ polynomial.support,
        Polynomial.C (polynomial.coeff degree) * Polynomial.X ^ degree *
          ribbonQuadraticPlus ^ (bound - degree)) *
        ribbonInverseQuadraticQ ^ bound = _
  rw [map_sum, Finset.sum_mul]
  rw [Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro degree hdegreeSupport
  have hdegree : degree ≤ bound :=
    (Polynomial.le_natDegree_of_mem_supp degree hdegreeSupport).trans hbound
  simp only [map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_C, Polynomial.coe_X]
  rw [ribbonSubstitutionQ_eq, mul_pow,
    show PowerSeries.C (polynomial.coeff degree) * X ^ degree *
        (ribbonQuadraticPlus : ℚ⟦X⟧) ^ (bound - degree) *
          ribbonInverseQuadraticQ ^ bound =
      PowerSeries.C (polynomial.coeff degree) * X ^ degree *
        ((ribbonQuadraticPlus : ℚ⟦X⟧) ^ (bound - degree) *
          ribbonInverseQuadraticQ ^ bound) by ring,
    ribbonQuadraticPlus_pow_mul_inverse_pow hdegree]
  simp only [PowerSeries.algebraMap_eq]
  ring

theorem ribbonRationalNumerator_ne_zero
    {bound : ℕ} {polynomial : Polynomial ℚ}
    (hpolynomial : polynomial ≠ 0)
    (hbound : polynomial.natDegree ≤ bound) :
    ribbonRationalNumerator bound polynomial ≠ 0 := by
  intro hzero
  have htransport := ribbonRationalNumerator_mul_inverse_pow
    bound polynomial hbound
  rw [hzero, Polynomial.coe_zero, zero_mul] at htransport
  have hsubst :
      PowerSeries.subst ribbonSubstitutionQ (polynomial : ℚ⟦X⟧) =
        PowerSeries.subst ribbonSubstitutionQ (0 : ℚ⟦X⟧) := by
    have hsubstZero :
        PowerSeries.subst ribbonSubstitutionQ (0 : ℚ⟦X⟧) = 0 := by
      rw [← PowerSeries.coe_substAlgHom ribbonSubstitutionQ_hasSubst]
      exact map_zero
        (PowerSeries.substAlgHom ribbonSubstitutionQ_hasSubst)
    exact htransport.symm.trans hsubstZero.symm
  have hcoe : (polynomial : ℚ⟦X⟧) = 0 :=
    subst_ribbonSubstitutionQ_injective hsubst
  exact hpolynomial ((Polynomial.coe_injective ℚ) hcoe)

end FibonacciRibbonKernel
