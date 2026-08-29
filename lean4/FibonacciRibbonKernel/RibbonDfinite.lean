import FibonacciRibbonKernel.EulerPolynomialCancellation

namespace FibonacciRibbonKernel

open PowerSeries
open scoped Classical

noncomputable def ribbonGeneratingSeriesQ (rank : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.map (Int.castRingHom ℚ) (ribbonGeneratingSeries rank)

@[simp] theorem ribbonGeneratingSeriesQ_coeff (rank degree : ℕ) :
    PowerSeries.coeff degree (ribbonGeneratingSeriesQ rank) =
      (ribbonCount rank degree : ℚ) := by
  simp [ribbonGeneratingSeriesQ, PowerSeries.coeff_map,
    ribbonGeneratingSeries_coeff]

theorem exact_generating_substitutionQ
    {rank : ℕ} (hrank : 1 ≤ rank) :
    ribbonGeneratingSeriesQ rank =
      ribbonInverseQuadraticQ *
        PowerSeries.subst ribbonSubstitutionQ
          (generalUnrestrictedOrdinarySeriesQ rank) := by
  have hmapped := congrArg (PowerSeries.map (Int.castRingHom ℚ))
    (exact_generating_substitution hrank)
  calc
    ribbonGeneratingSeriesQ rank =
        PowerSeries.map (Int.castRingHom ℚ)
          (substitutionDenominator *
            PowerSeries.subst ribbonSubstitution
              (unrestrictedGeneratingSeries rank)) := by
      exact hmapped
    _ = ribbonInverseQuadraticQ *
        PowerSeries.subst ribbonSubstitutionQ
          (PowerSeries.map (Int.castRingHom ℚ)
            (unrestrictedGeneratingSeries rank)) := by
      rw [map_mul]
      change ribbonInverseQuadraticQ *
          PowerSeries.map (Int.castRingHom ℚ)
            (PowerSeries.subst ribbonSubstitution
              (unrestrictedGeneratingSeries rank)) = _
      congr 1
      exact PowerSeries.map_subst ribbonSubstitution_hasSubst
        (unrestrictedGeneratingSeries rank)
    _ = ribbonInverseQuadraticQ *
        PowerSeries.subst ribbonSubstitutionQ
          (generalUnrestrictedOrdinarySeriesQ rank) := by
      rw [unrestrictedGeneratingSeries_map_rat]

theorem ribbon_prefactor_mul_eulerDFinite
    {series : ℚ⟦X⟧} (hfinite : EulerDFinite series) :
    EulerDFinite (ribbonInverseQuadraticQ * series) := by
  have hproduct :
      (ribbonQuadraticPlus : ℚ⟦X⟧) *
          (ribbonInverseQuadraticQ * series) = series := by
    rw [← mul_assoc]
    rw [show (ribbonQuadraticPlus : ℚ⟦X⟧) *
        ribbonInverseQuadraticQ = 1 by
      rw [mul_comm]
      exact ribbonInverseQuadraticQ_mul_plus]
    simp
  rw [← hproduct] at hfinite
  exact EulerDFinite.cancel_polynomial_mul
    ribbonQuadraticPlus_ne_zero hfinite

/-- Kernel-only closure of the D-finite clause in `thm:substitution` for the
literal fixed-rank ribbon generating series. -/
theorem ribbonGeneratingSeriesQ_eulerDFinite
    {rank : ℕ} (hrank : 1 ≤ rank) :
    EulerDFinite (ribbonGeneratingSeriesQ rank) := by
  rw [exact_generating_substitutionQ hrank]
  exact ribbon_prefactor_mul_eulerDFinite
    (EulerDFinite.subst_ribbonSubstitutionQ
      (generalUnrestrictedOrdinarySeriesQ_eulerDFinite rank))

end FibonacciRibbonKernel
