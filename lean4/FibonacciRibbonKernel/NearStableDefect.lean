import FibonacciRibbonKernel.PartitionConjugation

namespace FibonacciRibbonKernel

open scoped Classical

noncomputable def fullTableauSum (size : ℕ) : ℕ :=
  ∑ shape : BoundedPartition size size, standardTableauNumber shape

noncomputable def missingTableauSum (height size : ℕ) : ℕ :=
  ∑ shape : BoundedPartition size size,
    if height < shape.youngDiagram.colLen 0 then
      standardTableauNumber shape
    else 0

theorem unrestrictedCount_eq_full_height_sum (rank columns : ℕ) :
    unrestrictedCount rank columns =
      ∑ shape : BoundedPartition columns columns,
        if shape.youngDiagram.colLen 0 ≤ rank + 1 then
          standardTableauNumber shape
        else 0 := by
  rw [unrestrictedCount_eq_sum_standardTableauNumbers]
  let equivalence := boundedPartitionFullHeightEquiv rank columns
  calc
    (∑ shape : BoundedPartition rank columns,
        standardTableauNumber shape) =
        ∑ shape : {shape : BoundedPartition columns columns //
          shape.youngDiagram.colLen 0 ≤ rank + 1},
          standardTableauNumber shape.1 := by
      apply Fintype.sum_equiv equivalence
      intro shape
      exact (boundedPartitionFullHeightEquiv_preserves_number shape).symm
    _ = ∑ shape ∈ (Finset.univ : Finset (BoundedPartition columns columns)).filter
          (fun shape => shape.youngDiagram.colLen 0 ≤ rank + 1),
          standardTableauNumber shape := by
      symm
      apply Finset.sum_subtype
      intro shape
      simp
    _ = ∑ shape : BoundedPartition columns columns,
          if shape.youngDiagram.colLen 0 ≤ rank + 1 then
            standardTableauNumber shape
          else 0 := by
      rw [← Finset.sum_filter]

theorem fullTableauSum_eq_unrestrictedCount (size : ℕ) :
    fullTableauSum size = unrestrictedCount size size := by
  rw [unrestrictedCount_eq_full_height_sum]
  unfold fullTableauSum
  apply Finset.sum_congr rfl
  intro shape hshape
  rw [if_pos]
  have h := FibonacciRibbonKernel.YoungDiagram.colLen_zero_le_card
    shape.youngDiagram
  rw [shape.youngDiagram_card] at h
  omega

theorem fullTableauSum_eq_restricted_add_missing
    (rank columns : ℕ) :
    fullTableauSum columns =
      unrestrictedCount rank columns + missingTableauSum (rank + 1) columns := by
  rw [unrestrictedCount_eq_full_height_sum]
  unfold fullTableauSum missingTableauSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro shape hshape
  by_cases hheight : shape.youngDiagram.colLen 0 ≤ rank + 1
  · rw [if_pos hheight, if_neg (by omega)]
    omega
  · rw [if_neg hheight, if_pos (by omega)]
    omega

theorem fullTableauSum_sub_unrestrictedCount
    (rank columns : ℕ) :
    fullTableauSum columns - unrestrictedCount rank columns =
      missingTableauSum (rank + 1) columns := by
  have h := fullTableauSum_eq_restricted_add_missing rank columns
  omega

theorem BoundedPartition.conjugate_colLen_zero
    {size : ℕ} (shape : BoundedPartition size size) :
    shape.conjugate.youngDiagram.colLen 0 = shape.firstRow := by
  have h := shape.conjugate.conjugate_firstRow
  rw [shape.conjugate_conjugate] at h
  exact h.symm

theorem missingTableauSum_eq_tailTableauSum
    (height tailBound size : ℕ)
    (hbalance : height + tailBound + 1 = size) :
    missingTableauSum height size = tailTableauSum tailBound size := by
  unfold missingTableauSum tailTableauSum
  let conjugation := boundedPartitionConjugationEquiv size
  let weight : BoundedPartition size size → ℕ := fun shape =>
    if height < shape.youngDiagram.colLen 0 then
      standardTableauNumber shape
    else 0
  calc
    (∑ shape : BoundedPartition size size, weight shape) =
        ∑ shape : BoundedPartition size size,
          weight (conjugation shape) := by
      exact (Equiv.sum_comp conjugation _).symm
    _ = ∑ shape : BoundedPartition size size,
          if size - shape.firstRow ≤ tailBound then
            standardTableauNumber shape
          else 0 := by
      apply Finset.sum_congr rfl
      intro shape hshape
      change (if height < shape.conjugate.youngDiagram.colLen 0 then
          standardTableauNumber shape.conjugate else 0) = _
      rw [shape.conjugate_colLen_zero,
        shape.standardTableauNumber_conjugate]
      have hfirst : shape.firstRow ≤ size := by
        have hbound := (shape.1 0).isLt
        unfold BoundedPartition.firstRow
        omega
      by_cases htail : size - shape.firstRow ≤ tailBound
      · rw [if_pos htail, if_pos (by omega)]
      · rw [if_neg htail, if_neg (by omega)]

theorem missingTableauSum_eq_zero_of_size_le_height
    (height size : ℕ) (hsize : size ≤ height) :
    missingTableauSum height size = 0 := by
  unfold missingTableauSum
  apply Finset.sum_eq_zero
  intro shape hshape
  rw [if_neg]
  have h := FibonacciRibbonKernel.YoungDiagram.colLen_zero_le_card
    shape.youngDiagram
  rw [shape.youngDiagram_card] at h
  omega

theorem unrestrictedCount_eq_fullTableauSum_of_columns_le_height
    (rank columns : ℕ) (hheight : columns ≤ rank + 1) :
    unrestrictedCount rank columns = fullTableauSum columns := by
  have hsplit := fullTableauSum_eq_restricted_add_missing rank columns
  have hzero := missingTableauSum_eq_zero_of_size_le_height
    (rank + 1) columns hheight
  rw [hzero, add_zero] at hsplit
  exact hsplit.symm

/-- Stable inclusion--exclusion before the RSK identification of the full
tableau sum with involutions. -/
noncomputable def tableauStableSignedNumber (size : ℕ) : ℤ :=
  ∑ edges ∈ Finset.range (size / 2 + 1),
    (-1 : ℤ) ^ edges *
      (Nat.choose (size - edges) edges : ℤ) *
      (fullTableauSum (size - 2 * edges) : ℤ)

/-- Exact conjugate-tail defect identity underlying
`eq:near-stable-defect`.  The separate RSK bridge identifies
`tableauStableSignedNumber` with the actual stable involution number. -/
theorem tableauStableSignedNumber_sub_ribbonCount
    (defect size : ℕ) (hsize : defect + 2 ≤ size) :
    tableauStableSignedNumber size -
        (ribbonCount (size - defect - 1) size : ℤ) =
      ∑ edges ∈ Finset.range ((defect + 1) / 2),
        (-1 : ℤ) ^ edges *
          (Nat.choose (size - edges) edges : ℤ) *
          (tailTableauSum (defect - 2 * edges - 1)
            (size - 2 * edges) : ℤ) := by
  have hrank : 1 ≤ size - defect - 1 := by omega
  rw [ribbonCount_main_formula hrank]
  unfold tableauStableSignedNumber
  rw [← Finset.sum_sub_distrib]
  let term : ℕ → ℤ := fun edges =>
    (-1 : ℤ) ^ edges *
      (Nat.choose (size - edges) edges : ℤ) *
      (missingTableauSum (size - defect) (size - 2 * edges) : ℤ)
  have hterm (edges : ℕ) :
      ((-1 : ℤ) ^ edges *
          (Nat.choose (size - edges) edges : ℤ) *
          (fullTableauSum (size - 2 * edges) : ℤ) -
        (-1 : ℤ) ^ edges *
          (Nat.choose (size - edges) edges : ℤ) *
          (∑ shape : BoundedPartition (size - defect - 1)
            (size - 2 * edges),
            (standardTableauNumber shape : ℤ))) = term edges := by
    have hfull := fullTableauSum_eq_restricted_add_missing
      (size - defect - 1) (size - 2 * edges)
    have hheight : size - defect - 1 + 1 = size - defect := by omega
    rw [hheight] at hfull
    have hcast :
        (fullTableauSum (size - 2 * edges) : ℤ) =
          (∑ shape : BoundedPartition (size - defect - 1)
            (size - 2 * edges),
            (standardTableauNumber shape : ℤ)) +
          missingTableauSum (size - defect) (size - 2 * edges) := by
      rw [unrestrictedCount_eq_sum_standardTableauNumbers] at hfull
      exact_mod_cast hfull
    dsimp [term]
    linear_combination
      ((-1 : ℤ) ^ edges * (Nat.choose (size - edges) edges : ℤ)) * hcast
  simp_rw [hterm]
  have hcutoff : (defect + 1) / 2 ≤ size / 2 + 1 := by omega
  symm
  apply Finset.sum_subset_zero_on_sdiff (Finset.range_mono hcutoff)
  · intro edges hdiff
    simp only [Finset.mem_sdiff, Finset.mem_range] at hdiff
    have hlong : defect ≤ 2 * edges := by
      have hnot : ¬ edges < (defect + 1) / 2 := hdiff.2
      have hiff := Nat.lt_div_iff_mul_lt (x := edges) (y := defect + 1)
        (k := 2) (by omega)
      omega
    have hzero := missingTableauSum_eq_zero_of_size_le_height
      (size - defect) (size - 2 * edges) (by omega)
    simp [term, hzero]
  · intro edges hshort
    simp only [Finset.mem_range] at hshort
    have htwice : 2 * edges < defect := by
      have hiff := Nat.lt_div_iff_mul_lt (x := edges) (y := defect + 1)
        (k := 2) (by omega)
      omega
    have htail := missingTableauSum_eq_tailTableauSum
      (size - defect) (defect - 2 * edges - 1)
      (size - 2 * edges) (by omega)
    dsimp [term]
    rw [htail]
  
theorem tableauStableSignedNumber_sub_ribbonCount_tail
    (defect size : ℕ) (hsize : defect + 2 ≤ size) :
    tableauStableSignedNumber size -
        (ribbonCount (size - defect - 1) size : ℤ) =
      ∑ edges ∈ Finset.range ((defect + 1) / 2),
        (-1 : ℤ) ^ edges *
          (Nat.choose (size - edges) edges : ℤ) *
          (tailTableauSum (defect - 2 * edges - 1)
            (size - 2 * edges) : ℤ) := by
  exact tableauStableSignedNumber_sub_ribbonCount defect size hsize

end FibonacciRibbonKernel
