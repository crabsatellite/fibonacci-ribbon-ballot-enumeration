import FibonacciRibbonKernel.CosineCubeReindexing

namespace FibonacciRibbonKernel

open MeasureTheory

noncomputable def cosineFinSuccSplitEquiv (dimension : ℕ) :
    (Fin (dimension + 1) → ℝ) ≃ᵐ (ℝ × (Fin dimension → ℝ)) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (dimension + 1) => ℝ) 0

theorem cosineFinSuccSplitEquiv_symm_apply
    (dimension : ℕ) (angle : ℝ) (tail : Fin dimension → ℝ) :
    (cosineFinSuccSplitEquiv dimension).symm (angle, tail) =
      Fin.cons angle tail := by
  funext coordinate
  unfold cosineFinSuccSplitEquiv
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv]

theorem measurePreserving_cosineFinSuccSplitEquiv (dimension : ℕ) :
    MeasurePreserving (cosineFinSuccSplitEquiv dimension)
      (cosineCubeProductMeasure (dimension + 1))
      (cosineIntervalMeasure.prod (cosineCubeProductMeasure dimension)) := by
  unfold cosineFinSuccSplitEquiv cosineCubeProductMeasure
  exact measurePreserving_piFinSuccAbove
    (fun _ : Fin (dimension + 1) => cosineIntervalMeasure) 0

theorem cosineCubeRawIntegral_plus_fubini
    (plusPower minusPower power : ℕ) :
    (∫ angles : Fin ((plusPower + 1) + minusPower) → ℝ,
        cosineCubeRawIntegrand (plusPower + 1) minusPower power angles
        ∂cosineCubeProductMeasure ((plusPower + 1) + minusPower)) =
      ∫ angle : ℝ,
        ∫ tail : Fin (plusPower + minusPower) → ℝ,
          cosineCubeRawIntegrand (plusPower + 1) minusPower power
            (cosinePlusCons plusPower minusPower angle tail)
          ∂cosineCubeProductMeasure (plusPower + minusPower)
        ∂cosineIntervalMeasure := by
  let reindex := cosinePlusReindexEquiv plusPower minusPower
  let split := cosineFinSuccSplitEquiv (plusPower + minusPower)
  let reindexed : (Fin ((plusPower + minusPower) + 1) → ℝ) → ℝ :=
    fun angles => cosineCubeRawIntegrand (plusPower + 1) minusPower power
      (reindex.symm angles)
  have hreindex := measurePreserving_cosinePlusReindexEquiv plusPower minusPower
  have htransport := hreindex.integral_comp' reindexed
  have htransport' :
      (∫ angles : Fin ((plusPower + 1) + minusPower) → ℝ,
          cosineCubeRawIntegrand (plusPower + 1) minusPower power angles
          ∂cosineCubeProductMeasure ((plusPower + 1) + minusPower)) =
        ∫ angles : Fin ((plusPower + minusPower) + 1) → ℝ,
          reindexed angles
          ∂cosineCubeProductMeasure ((plusPower + minusPower) + 1) := by
    simpa only [Function.comp_apply, reindexed, reindex,
      MeasurableEquiv.symm_apply_apply] using htransport
  rw [htransport']
  have hsplit := measurePreserving_cosineFinSuccSplitEquiv
    (plusPower + minusPower)
  have hsplitIntegral := hsplit.symm.integral_comp' reindexed
  have hreindexed : Integrable reindexed
      (cosineCubeProductMeasure ((plusPower + minusPower) + 1)) := by
    have hcomp : reindexed ∘ reindex =
        cosineCubeRawIntegrand (plusPower + 1) minusPower power := by
      funext angles
      simp only [Function.comp_apply, reindexed, reindex,
        MeasurableEquiv.symm_apply_apply]
    apply (hreindex.integrable_comp_emb reindex.measurableEmbedding).mp
    rw [hcomp]
    exact integrable_cosineCubeRawIntegrand (plusPower + 1) minusPower power
  have hproductIntegrable : Integrable
      (fun pair : ℝ × (Fin (plusPower + minusPower) → ℝ) =>
        reindexed (split.symm pair))
      (cosineIntervalMeasure.prod
        (cosineCubeProductMeasure (plusPower + minusPower))) := by
    exact (hsplit.symm.integrable_comp_emb split.symm.measurableEmbedding).mpr
      hreindexed
  calc
    (∫ angles : Fin ((plusPower + minusPower) + 1) → ℝ,
        reindexed angles
        ∂cosineCubeProductMeasure ((plusPower + minusPower) + 1)) =
      ∫ pair : ℝ × (Fin (plusPower + minusPower) → ℝ),
        reindexed (split.symm pair)
        ∂(cosineIntervalMeasure.prod
          (cosineCubeProductMeasure (plusPower + minusPower))) :=
      hsplitIntegral.symm
    _ = ∫ angle : ℝ,
        ∫ tail : Fin (plusPower + minusPower) → ℝ,
          reindexed (split.symm (angle, tail))
          ∂cosineCubeProductMeasure (plusPower + minusPower)
        ∂cosineIntervalMeasure := by
      exact integral_prod
        (fun pair : ℝ × (Fin (plusPower + minusPower) → ℝ) =>
          reindexed (split.symm pair)) hproductIntegrable
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with angle
      apply integral_congr_ae
      filter_upwards with tail
      rw [cosineFinSuccSplitEquiv_symm_apply]
      dsimp only [reindexed, reindex]
      rw [
        cosinePlusReindexEquiv_symm_finCons]

theorem cosineCubeRawIntegral_minus_fubini
    (minusPower power : ℕ) :
    (∫ angles : Fin (0 + (minusPower + 1)) → ℝ,
        cosineCubeRawIntegrand 0 (minusPower + 1) power angles
        ∂cosineCubeProductMeasure (0 + (minusPower + 1))) =
      ∫ angle : ℝ,
        ∫ tail : Fin (0 + minusPower) → ℝ,
          cosineCubeRawIntegrand 0 (minusPower + 1) power
            (cosineMinusCons minusPower angle tail)
          ∂cosineCubeProductMeasure (0 + minusPower)
        ∂cosineIntervalMeasure := by
  let reindex := cosineMinusReindexEquiv minusPower
  let split := cosineFinSuccSplitEquiv (0 + minusPower)
  let reindexed : (Fin ((0 + minusPower) + 1) → ℝ) → ℝ :=
    fun angles => cosineCubeRawIntegrand 0 (minusPower + 1) power
      (reindex.symm angles)
  have hreindex := measurePreserving_cosineMinusReindexEquiv minusPower
  have htransport := hreindex.integral_comp' reindexed
  have htransport' :
      (∫ angles : Fin (0 + (minusPower + 1)) → ℝ,
          cosineCubeRawIntegrand 0 (minusPower + 1) power angles
          ∂cosineCubeProductMeasure (0 + (minusPower + 1))) =
        ∫ angles : Fin ((0 + minusPower) + 1) → ℝ,
          reindexed angles
          ∂cosineCubeProductMeasure ((0 + minusPower) + 1) := by
    simpa only [Function.comp_apply, reindexed, reindex,
      MeasurableEquiv.symm_apply_apply] using htransport
  rw [htransport']
  have hsplit := measurePreserving_cosineFinSuccSplitEquiv (0 + minusPower)
  have hsplitIntegral := hsplit.symm.integral_comp' reindexed
  have hreindexed : Integrable reindexed
      (cosineCubeProductMeasure ((0 + minusPower) + 1)) := by
    have hcomp : reindexed ∘ reindex =
        cosineCubeRawIntegrand 0 (minusPower + 1) power := by
      funext angles
      simp only [Function.comp_apply, reindexed, reindex,
        MeasurableEquiv.symm_apply_apply]
    apply (hreindex.integrable_comp_emb reindex.measurableEmbedding).mp
    rw [hcomp]
    exact integrable_cosineCubeRawIntegrand 0 (minusPower + 1) power
  have hproductIntegrable : Integrable
      (fun pair : ℝ × (Fin (0 + minusPower) → ℝ) =>
        reindexed (split.symm pair))
      (cosineIntervalMeasure.prod
        (cosineCubeProductMeasure (0 + minusPower))) := by
    exact (hsplit.symm.integrable_comp_emb split.symm.measurableEmbedding).mpr
      hreindexed
  calc
    (∫ angles : Fin ((0 + minusPower) + 1) → ℝ,
        reindexed angles
        ∂cosineCubeProductMeasure ((0 + minusPower) + 1)) =
      ∫ pair : ℝ × (Fin (0 + minusPower) → ℝ),
        reindexed (split.symm pair)
        ∂(cosineIntervalMeasure.prod
          (cosineCubeProductMeasure (0 + minusPower))) :=
      hsplitIntegral.symm
    _ = ∫ angle : ℝ,
        ∫ tail : Fin (0 + minusPower) → ℝ,
          reindexed (split.symm (angle, tail))
          ∂cosineCubeProductMeasure (0 + minusPower)
        ∂cosineIntervalMeasure := by
      exact integral_prod
        (fun pair : ℝ × (Fin (0 + minusPower) → ℝ) =>
          reindexed (split.symm pair)) hproductIntegrable
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with angle
      apply integral_congr_ae
      filter_upwards with tail
      rw [cosineFinSuccSplitEquiv_symm_apply]
      dsimp only [reindexed, reindex]
      rw [cosineMinusReindexEquiv_symm_finCons]

end FibonacciRibbonKernel
