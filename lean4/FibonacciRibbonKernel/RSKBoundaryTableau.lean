import FibonacciRibbonKernel.RSKForward
import FibonacciRibbonKernel.StandardTableaux

namespace FibonacciRibbonKernel

open scoped Classical

def GrowthStep.AddData
    {height : ℕ} {base : GrowthShape height} (_step : GrowthStep base) :=
  PSigma fun row : Fin height => base.Addable row

noncomputable def GrowthStep.addData
    {height : ℕ} {base : GrowthShape height}
    (step : GrowthStep base) (hadd : step ≠ GrowthStep.stay) :
    step.AddData := by
  cases step with
  | stay => exact (hadd rfl).elim
  | add row hrow => exact ⟨row, hrow⟩

theorem GrowthStep.eq_add_addData
    {height : ℕ} {base : GrowthShape height}
    (step : GrowthStep base) (hadd : step ≠ GrowthStep.stay) :
    step = GrowthStep.add (step.addData hadd).1 (step.addData hadd).2 := by
  cases step with
  | stay => exact (hadd rfl).elim
  | add row hrow => rfl

theorem List.take_ofFn_eq_ofFn
    {α : Type*} {size : ℕ} (function : Fin size → α)
    (prefixLength : ℕ) (hprefix : prefixLength ≤ size) :
    (List.ofFn function).take prefixLength =
      List.ofFn (fun index : Fin prefixLength =>
        function ⟨index.val, lt_of_lt_of_le index.isLt hprefix⟩) := by
  induction size with
  | zero =>
      have hzero : prefixLength = 0 := by omega
      subst prefixLength
      simp
  | succ size ih =>
      by_cases hall : prefixLength = size + 1
      · subst prefixLength
        rw [List.take_of_length_le (by simp)]
      · have hsmall : prefixLength ≤ size := by omega
        rw [List.ofFn_succ']
        rw [List.concat_eq_append]
        rw [List.take_append_of_le_length (by simpa using hsmall)]
        simpa using ih (fun index : Fin size => function index.castSucc) hsmall

noncomputable def finalGrowthBoundary
    (size : ℕ) (permutation : Equiv.Perm (Fin size)) :
    GrowthBoundary size permutation size :=
  growthBoundaryAfter size permutation size le_rfl

theorem finalGrowthBoundary_edge_ne_stay
    (size : ℕ) (permutation : Equiv.Perm (Fin size))
    (column : Fin size) :
    (finalGrowthBoundary size permutation).edges column ≠ GrowthStep.stay := by
  intro hstay
  have hbound := ((finalGrowthBoundary size permutation).edge_stay_iff column).mp hstay
  have hinverse := (permutation.symm column).isLt
  omega

noncomputable def finalBoundaryRow
    (size : ℕ) (permutation : Equiv.Perm (Fin size))
    (column : Fin size) : Fin (size + 1) :=
  (((finalGrowthBoundary size permutation).edges column).addData
    (finalGrowthBoundary_edge_ne_stay size permutation column)).1

theorem finalBoundary_vertex_rows_succ
    (size : ℕ) (permutation : Equiv.Perm (Fin size))
    (column : Fin size) (row : Fin (size + 1)) :
    ((finalGrowthBoundary size permutation).vertices column.succ).rows row =
      ((finalGrowthBoundary size permutation).vertices column.castSucc).rows row +
        if row = finalBoundaryRow size permutation column then 1 else 0 := by
  let boundary := finalGrowthBoundary size permutation
  let step := boundary.edges column
  let hnon := finalGrowthBoundary_edge_ne_stay size permutation column
  have hstep := step.eq_add_addData hnon
  have htarget := boundary.edge_target column
  change step.target = boundary.vertices column.succ at htarget
  rw [hstep] at htarget
  have hrows := congrArg (fun shape : GrowthShape (size + 1) => shape.rows row) htarget
  dsimp [finalBoundaryRow, boundary, step] at hrows ⊢
  rw [← hrows]
  by_cases heq : row =
      (((finalGrowthBoundary size permutation).edges column).addData hnon).1
  · simp [GrowthShape.add, heq]
  · simp [GrowthShape.add, heq]

theorem finalBoundary_prefix_count
    (size : ℕ) (permutation : Equiv.Perm (Fin size))
    (prefixLength : ℕ) (hprefix : prefixLength ≤ size) (row : Fin (size + 1)) :
    (List.ofFn (fun column : Fin prefixLength =>
      finalBoundaryRow size permutation
        ⟨column.val, lt_of_lt_of_le column.isLt hprefix⟩)).count row =
      ((finalGrowthBoundary size permutation).vertices
        ⟨prefixLength, by omega⟩).rows row := by
  induction prefixLength with
  | zero =>
      change 0 = ((finalGrowthBoundary size permutation).vertices 0).rows row
      rw [(finalGrowthBoundary size permutation).left_empty]
      rfl
  | succ prior ih =>
      have hsmall : prior ≤ size := by omega
      let column : Fin size := ⟨prior, by omega⟩
      rw [List.ofFn_succ']
      have hinduction := ih hsmall
      have hnext := finalBoundary_vertex_rows_succ size permutation column row
      have hcurrent :
          ((finalGrowthBoundary size permutation).vertices
            ⟨prior, by omega⟩).rows row =
          ((finalGrowthBoundary size permutation).vertices column.castSucc).rows row := by
        rfl
      have hfuture :
          ((finalGrowthBoundary size permutation).vertices
            ⟨prior + 1, by omega⟩).rows row =
          ((finalGrowthBoundary size permutation).vertices column.succ).rows row := by
        rfl
      have hword :
          List.ofFn (fun index : Fin prior =>
            finalBoundaryRow size permutation
              ⟨index.castSucc.val, by omega⟩) =
            List.ofFn (fun index : Fin prior =>
              finalBoundaryRow size permutation
                ⟨index.val, by omega⟩) := by
        rfl
      have hlast :
          finalBoundaryRow size permutation
              ⟨(Fin.last prior).val, by omega⟩ =
            finalBoundaryRow size permutation column := by
        rfl
      rw [List.concat_eq_append, List.count_append, List.count_singleton,
        hword, hlast, hinduction, hcurrent, hfuture, hnext]
      by_cases heq : row = finalBoundaryRow size permutation column
      · simp [heq]
      · simp [heq, Ne.symm heq]

noncomputable def finalBoundaryTableau
    (size : ℕ) (permutation : Equiv.Perm (Fin size)) :
    StandardRowWordTableau size size where
  word := List.ofFn (finalBoundaryRow size permutation)
  length_eq := List.length_ofFn
  ballot := by
    intro initial hinitial
    rw [runPlusWord_eq_add_wordWeight]
    intro row
    simp only [Pi.add_apply, Pi.zero_apply, zero_add, wordWeight_apply]
    have hlength : initial.length ≤ size := by
      simpa using List.IsPrefix.length_le hinitial
    have htake := (List.prefix_iff_eq_take.mp hinitial)
    rw [htake, List.take_ofFn_eq_ofFn _ initial.length hlength]
    have hlower := finalBoundary_prefix_count size permutation initial.length
      hlength row.succ
    have hupper := finalBoundary_prefix_count size permutation initial.length
      hlength row.castSucc
    have hanti := ((finalGrowthBoundary size permutation).vertices
      ⟨initial.length, by omega⟩).rows_antitone
        row.castSucc row.succ (by
          simp only [Fin.val_castSucc, Fin.val_succ]
          omega)
    rw [hlower, hupper]
    omega

theorem finalBoundaryTableau_shape_row
    (size : ℕ) (permutation : Equiv.Perm (Fin size))
    (row : Fin (size + 1)) :
    ((finalBoundaryTableau size permutation).shape.1 row).val =
      ((finalGrowthBoundary size permutation).vertices (Fin.last size)).rows row := by
  change (List.ofFn (finalBoundaryRow size permutation)).count row = _
  have hcount := finalBoundary_prefix_count size permutation size le_rfl row
  change (List.ofFn (fun column : Fin size =>
    finalBoundaryRow size permutation column)).count row =
      ((finalGrowthBoundary size permutation).vertices
        ⟨size, by omega⟩).rows row
  exact hcount

theorem finalBoundaryShape_inverse_eq
    (size : ℕ) (permutation : Equiv.Perm (Fin size)) :
    (finalBoundaryTableau size permutation.symm).shape =
      (finalBoundaryTableau size permutation).shape := by
  have hshapes := PermutationGrowthDiagram.shapes_unique
    (forwardPermutationGrowthDiagram size permutation.symm)
    (forwardPermutationGrowthDiagram size permutation).transpose
  have hfinal := congrFun (congrFun hshapes (Fin.last size)) (Fin.last size)
  apply Subtype.ext
  funext row
  apply Fin.ext
  rw [finalBoundaryTableau_shape_row, finalBoundaryTableau_shape_row]
  change
    ((growthBoundaryAfter size permutation.symm size le_rfl).vertices
        (Fin.last size)).rows row =
      ((growthBoundaryAfter size permutation size le_rfl).vertices
        (Fin.last size)).rows row
  exact congrArg (fun shape : GrowthShape (size + 1) => shape.rows row) hfinal

structure RSKTableauPair (size : ℕ) where
  insertion : StandardRowWordTableau size size
  recording : StandardRowWordTableau size size
  same_shape : insertion.shape = recording.shape

@[ext] theorem RSKTableauPair.ext
    {size : ℕ} {left right : RSKTableauPair size}
    (hinsertion : left.insertion = right.insertion)
    (hrecording : left.recording = right.recording) : left = right := by
  cases left
  cases right
  simp_all

noncomputable def forwardRSK
    (size : ℕ) (permutation : Equiv.Perm (Fin size)) : RSKTableauPair size where
  insertion := finalBoundaryTableau size permutation
  recording := finalBoundaryTableau size permutation.symm
  same_shape := (finalBoundaryShape_inverse_eq size permutation).symm

theorem permutation_symm_eq_of_involutive
    {size : ℕ} (permutation : Equiv.Perm (Fin size))
    (hinvolutive : Function.Involutive permutation) :
    permutation.symm = permutation := by
  apply Equiv.ext
  intro value
  apply permutation.injective
  rw [permutation.apply_symm_apply]
  exact (hinvolutive value).symm

theorem forwardRSK_diagonal_of_involutive
    (size : ℕ) (permutation : Equiv.Perm (Fin size))
    (hinvolutive : Function.Involutive permutation) :
    (forwardRSK size permutation).insertion =
      (forwardRSK size permutation).recording := by
  change finalBoundaryTableau size permutation =
    finalBoundaryTableau size permutation.symm
  rw [permutation_symm_eq_of_involutive permutation hinvolutive]

def RSKTableauPair.swap
    {size : ℕ} (pair : RSKTableauPair size) : RSKTableauPair size where
  insertion := pair.recording
  recording := pair.insertion
  same_shape := pair.same_shape.symm

theorem forwardRSK_symm
    (size : ℕ) (permutation : Equiv.Perm (Fin size)) :
    forwardRSK size permutation.symm = (forwardRSK size permutation).swap := by
  apply RSKTableauPair.ext
  · rfl
  · simp [forwardRSK, RSKTableauPair.swap]

end FibonacciRibbonKernel
