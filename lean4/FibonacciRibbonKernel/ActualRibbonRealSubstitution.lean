import FibonacciRibbonKernel.CosineCubeFibonacciIntegral
import FibonacciRibbonKernel.RibbonDfinite

namespace FibonacciRibbonKernel

open PowerSeries

noncomputable def generalUnrestrictedOrdinarySeriesR (rank : ℕ) : ℝ⟦X⟧ :=
  PowerSeries.map (Rat.castHom ℝ) (generalUnrestrictedOrdinarySeriesQ rank)

noncomputable def ribbonGeneratingSeriesR (rank : ℕ) : ℝ⟦X⟧ :=
  PowerSeries.map (Rat.castHom ℝ) (ribbonGeneratingSeriesQ rank)

@[simp] theorem generalUnrestrictedOrdinarySeriesR_coeff
    (rank power : ℕ) :
    PowerSeries.coeff power (generalUnrestrictedOrdinarySeriesR rank) =
      (unrestrictedCount rank power : ℝ) := by
  simp [generalUnrestrictedOrdinarySeriesR,
    generalUnrestrictedOrdinarySeriesQ_coeff]

@[simp] theorem ribbonGeneratingSeriesR_coeff (rank power : ℕ) :
    PowerSeries.coeff power (ribbonGeneratingSeriesR rank) =
      (ribbonCount rank power : ℝ) := by
  simp [ribbonGeneratingSeriesR, ribbonGeneratingSeriesQ_coeff]

theorem exact_generating_substitutionR
    {rank : ℕ} (hrank : 1 ≤ rank) :
    ribbonGeneratingSeriesR rank =
      ribbonInverseQuadraticR *
        PowerSeries.subst ribbonSubstitutionR
          (generalUnrestrictedOrdinarySeriesR rank) := by
  have hmapped := congrArg (PowerSeries.map (Rat.castHom ℝ))
    (exact_generating_substitutionQ hrank)
  unfold ribbonGeneratingSeriesR ribbonInverseQuadraticR
  unfold ribbonSubstitutionR generalUnrestrictedOrdinarySeriesR
  rw [map_mul] at hmapped
  have hmapSubst :
      PowerSeries.map (Rat.castHom ℝ)
          (PowerSeries.subst ribbonSubstitutionQ
            (generalUnrestrictedOrdinarySeriesQ rank)) =
        PowerSeries.subst
          (PowerSeries.map (Rat.castHom ℝ) ribbonSubstitutionQ)
          (PowerSeries.map (Rat.castHom ℝ)
            (generalUnrestrictedOrdinarySeriesQ rank)) := by
    exact PowerSeries.map_subst ribbonSubstitutionQ_hasSubst
      (generalUnrestrictedOrdinarySeriesQ rank)
  rw [hmapSubst] at hmapped
  exact hmapped

end FibonacciRibbonKernel
