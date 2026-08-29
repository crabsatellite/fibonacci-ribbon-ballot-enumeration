import FibonacciRibbonKernel.RegevMehtaStandardChamber

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped Classical

def mehtaBlockInputChamber (rank : ℕ) :
    Set ((Fin rank ⊕ Fin 1) → ℝ) :=
  mehtaBlockPair rank ⁻¹'
    ((regevChamber rank) ×ˢ (Set.univ : Set ℝ))

theorem mehtaCenterBlockLinearMap_preimage_chamber (rank : ℕ) :
    mehtaCenterBlockLinearMap rank ⁻¹'
        standardMehtaBlockChamber rank =
      mehtaBlockInputChamber rank := by
  ext input
  let pair := mehtaBlockPair rank input
  have hinput : mehtaBlockInput rank pair = input :=
    mehtaBlockInput_pair rank input
  have hcenter := mehtaBlockOutput_centerLinearMap rank pair
  rw [hinput] at hcenter
  unfold standardMehtaBlockChamber standardMehtaChamber
  unfold mehtaBlockInputChamber
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_prod,
    Set.mem_univ, and_true]
  rw [hcenter]
  change Antitone (mehtaCenterTransform rank pair) ↔
    Antitone (tracelessExtend pair.1)
  exact mehtaCenterTransform_antitone_iff rank pair

noncomputable def mehtaBlockInputChamberIntegral (rank : ℕ) : ℝ :=
  ∫ input in mehtaBlockInputChamber rank,
    standardMehtaIntegrand (rank + 1)
      (mehtaBlockOutput rank (mehtaCenterBlockLinearMap rank input))

theorem mehtaBlockInputChamberIntegral_eq_centered (rank : ℕ) :
    mehtaBlockInputChamberIntegral rank =
      centeredMehtaChamberIntegral rank := by
  unfold mehtaBlockInputChamberIntegral mehtaBlockInputChamber
  unfold centeredMehtaChamberIntegral
  have hchange := MeasurePreserving.setIntegral_preimage_emb
      (volume_preserving_mehtaBlockPair rank)
      (measurableEmbedding_mehtaBlockPair rank)
      (fun pair : (Fin rank → ℝ) × ℝ =>
        standardMehtaIntegrand (rank + 1)
          (mehtaCenterTransform rank pair))
      ((regevChamber rank) ×ˢ (Set.univ : Set ℝ))
  calc
    (∫ input in mehtaBlockPair rank ⁻¹'
          ((regevChamber rank) ×ˢ (Set.univ : Set ℝ)),
        standardMehtaIntegrand (rank + 1)
          (mehtaBlockOutput rank
            (mehtaCenterBlockLinearMap rank input))) =
      ∫ input in mehtaBlockPair rank ⁻¹'
          ((regevChamber rank) ×ˢ (Set.univ : Set ℝ)),
        standardMehtaIntegrand (rank + 1)
          (mehtaCenterTransform rank (mehtaBlockPair rank input)) := by
        apply setIntegral_congr_fun
        · exact (measurableEmbedding_mehtaBlockPair rank).measurable
            ((regevChamber_isClosed rank).measurableSet.prod
              MeasurableSet.univ)
        · intro input hinput
          have hpair := mehtaBlockOutput_centerLinearMap rank
            (mehtaBlockPair rank input)
          rw [mehtaBlockInput_pair] at hpair
          change standardMehtaIntegrand (rank + 1)
              (mehtaBlockOutput rank
                (mehtaCenterBlockLinearMap rank input)) =
            standardMehtaIntegrand (rank + 1)
              (mehtaCenterTransform rank (mehtaBlockPair rank input))
          rw [hpair]
    _ = _ := hchange

end FibonacciRibbonKernel
