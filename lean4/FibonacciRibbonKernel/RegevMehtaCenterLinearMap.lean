import FibonacciRibbonKernel.RegevMehtaCenterJacobian
import Mathlib.MeasureTheory.Constructions.Pi

namespace FibonacciRibbonKernel

open MeasureTheory
open scoped Classical Matrix

noncomputable def mehtaCenterBlockLinearMap (rank : ℕ) :
    ((Fin rank ⊕ Fin 1) → ℝ) →ₗ[ℝ] ((Fin rank ⊕ Fin 1) → ℝ) :=
  Matrix.toLin' (mehtaCenterBlockMatrix rank)

noncomputable def mehtaBlockInput (rank : ℕ)
    (input : (Fin rank → ℝ) × ℝ) : (Fin rank ⊕ Fin 1) → ℝ :=
  Sum.elim input.1 (fun _ => input.2)

noncomputable def mehtaBlockOutput (rank : ℕ)
    (output : (Fin rank ⊕ Fin 1) → ℝ) : Fin (rank + 1) → ℝ :=
  fun row => output (finSumFinEquiv.symm row)

noncomputable def mehtaBlockOutputEquiv (rank : ℕ) :
    ((Fin rank ⊕ Fin 1) → ℝ) ≃ᵐ (Fin (rank + 1) → ℝ) :=
  MeasurableEquiv.piCongrLeft
    (fun _ : Fin (rank + 1) => ℝ) finSumFinEquiv

theorem mehtaBlockOutputEquiv_apply (rank : ℕ)
    (output : (Fin rank ⊕ Fin 1) → ℝ) :
    mehtaBlockOutputEquiv rank output = mehtaBlockOutput rank output := by
  funext row
  obtain ⟨index, rfl⟩ := finSumFinEquiv.surjective row
  change (MeasurableEquiv.piCongrLeft
      (fun _ : Fin (rank + 1) => ℝ) finSumFinEquiv)
        output (finSumFinEquiv index) = _
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  simp [mehtaBlockOutput]

theorem volume_preserving_mehtaBlockOutput (rank : ℕ) :
    MeasurePreserving (mehtaBlockOutput rank)
      (volume : Measure ((Fin rank ⊕ Fin 1) → ℝ))
      (volume : Measure (Fin (rank + 1) → ℝ)) := by
  have hpreserving := volume_measurePreserving_piCongrLeft
    (fun _ : Fin (rank + 1) => ℝ) finSumFinEquiv
  have hfunction :
      ⇑(MeasurableEquiv.piCongrLeft
        (fun _ : Fin (rank + 1) => ℝ) finSumFinEquiv) =
      mehtaBlockOutput rank := by
    funext output
    exact mehtaBlockOutputEquiv_apply rank output
  rw [hfunction] at hpreserving
  exact hpreserving

theorem measurableEmbedding_mehtaBlockOutput (rank : ℕ) :
    MeasurableEmbedding (mehtaBlockOutput rank) := by
  have hfunction : ⇑(mehtaBlockOutputEquiv rank) =
      mehtaBlockOutput rank := by
    funext output
    exact mehtaBlockOutputEquiv_apply rank output
  rw [← hfunction]
  exact (mehtaBlockOutputEquiv rank).measurableEmbedding

noncomputable def mehtaBlockPair (rank : ℕ)
    (input : (Fin rank ⊕ Fin 1) → ℝ) : (Fin rank → ℝ) × ℝ :=
  (fun row => input (Sum.inl row), input (Sum.inr 0))

noncomputable def mehtaBlockPairEquiv (rank : ℕ) :
    ((Fin rank ⊕ Fin 1) → ℝ) ≃ᵐ (Fin rank → ℝ) × ℝ :=
  (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Fin rank ⊕ Fin 1 => ℝ)).trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl (Fin rank → ℝ))
      (MeasurableEquiv.funUnique (Fin 1) ℝ))

theorem mehtaBlockPairEquiv_apply (rank : ℕ)
    (input : (Fin rank ⊕ Fin 1) → ℝ) :
    mehtaBlockPairEquiv rank input = mehtaBlockPair rank input := by
  apply Prod.ext
  · rfl
  · rfl

theorem mehtaBlockInput_pair (rank : ℕ)
    (input : (Fin rank ⊕ Fin 1) → ℝ) :
    mehtaBlockInput rank (mehtaBlockPair rank input) = input := by
  funext index
  cases index with
  | inl row => rfl
  | inr row =>
      rw [Fin.eq_zero row]
      rfl

theorem volume_preserving_mehtaBlockPair (rank : ℕ) :
    MeasurePreserving (mehtaBlockPair rank)
      (volume : Measure ((Fin rank ⊕ Fin 1) → ℝ))
      ((volume : Measure (Fin rank → ℝ)).prod volume) := by
  let split := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Fin rank ⊕ Fin 1 => ℝ)
  have hsplit := volume_measurePreserving_sumPiEquivProdPi
    (fun _ : Fin rank ⊕ Fin 1 => ℝ)
  have hsecond := volume_preserving_funUnique (Fin 1) ℝ
  have hproduct := MeasurePreserving.prod
    (MeasurePreserving.id (volume : Measure (Fin rank → ℝ))) hsecond
  have hcomposed := hproduct.comp hsplit
  convert hcomposed using 1
  funext input
  apply Prod.ext
  · rfl
  · rfl

theorem measurableEmbedding_mehtaBlockPair (rank : ℕ) :
    MeasurableEmbedding (mehtaBlockPair rank) := by
  have hfunction : ⇑(mehtaBlockPairEquiv rank) =
      mehtaBlockPair rank := by
    funext input
    exact mehtaBlockPairEquiv_apply rank input
  rw [← hfunction]
  exact (mehtaBlockPairEquiv rank).measurableEmbedding

theorem mehtaCenterBlockLinearMap_inl (rank : ℕ)
    (input : (Fin rank ⊕ Fin 1) → ℝ) (row : Fin rank) :
    mehtaCenterBlockLinearMap rank input (Sum.inl row) =
      input (Sum.inl row) + input (Sum.inr 0) := by
  rw [mehtaCenterBlockLinearMap, Matrix.toLin'_apply]
  unfold Matrix.mulVec dotProduct
  rw [Fintype.sum_sum_type]
  simp [mehtaCenterBlockMatrix, Matrix.one_apply]

theorem mehtaCenterBlockLinearMap_inr (rank : ℕ)
    (input : (Fin rank ⊕ Fin 1) → ℝ) :
    mehtaCenterBlockLinearMap rank input (Sum.inr 0) =
      -(∑ row : Fin rank, input (Sum.inl row)) + input (Sum.inr 0) := by
  rw [mehtaCenterBlockLinearMap, Matrix.toLin'_apply]
  unfold Matrix.mulVec dotProduct
  rw [Fintype.sum_sum_type]
  simp [mehtaCenterBlockMatrix, Finset.sum_neg_distrib]

theorem mehtaBlockOutput_centerLinearMap (rank : ℕ)
    (input : (Fin rank → ℝ) × ℝ) :
    mehtaBlockOutput rank
        (mehtaCenterBlockLinearMap rank (mehtaBlockInput rank input)) =
      mehtaCenterTransform rank input := by
  funext row
  cases row using Fin.lastCases with
  | last =>
      rw [mehtaBlockOutput, finSumFinEquiv_symm_last,
        mehtaCenterBlockLinearMap_inr]
      simp [mehtaBlockInput, mehtaCenterTransform,
        tracelessExtend_last]
  | cast row =>
      rw [mehtaBlockOutput,
        finSumFinEquiv_symm_apply_castSucc,
        mehtaCenterBlockLinearMap_inl]
      simp [mehtaBlockInput, mehtaCenterTransform,
        tracelessExtend_castSucc]

theorem mehtaCenterBlockLinearMap_det (rank : ℕ) :
    LinearMap.det (mehtaCenterBlockLinearMap rank) =
      ((rank + 1 : ℕ) : ℝ) := by
  unfold mehtaCenterBlockLinearMap
  rw [LinearMap.det_toLin']
  exact mehtaCenterBlockMatrix_det rank

end FibonacciRibbonKernel
