import FibonacciRibbonKernel.GordonEvenDeterminantFactorization

namespace FibonacciRibbonKernel

open PowerSeries
open scoped Matrix

noncomputable def gordonOddGesselEntry (row column : ℕ) : ℚ⟦X⟧ :=
  (if row ≤ column then literalBesselJ (column - row)
    else literalBesselJ (row - column)) -
  literalBesselJ (row + column + 2)

noncomputable def gordonOddCumulativeEntry (row column : ℕ) : ℚ⟦X⟧ :=
  2 * generalBesselPairQ (column + 1) -
    gordonSkewQ row column -
      generalBesselPairQ (row + column + 2)

theorem gordonOddCumulativeEntry_zero (column : ℕ) :
    gordonOddCumulativeEntry 0 column =
      gordonOddGesselEntry 0 column := by
  by_cases hzero : column = 0
  · subst column
    have hq := generalBesselPairQ_succ 1 (by omega)
    simp [gordonOddCumulativeEntry, gordonOddGesselEntry,
      gordonSkewQ, generalBesselPairQ_one]
    rw [hq, generalBesselPairQ_one]
    ring
  · have hpositive : 1 ≤ column := Nat.one_le_iff_ne_zero.mpr hzero
    have hcol : 0 < column := by omega
    have hnext := generalBesselPairQ_succ column hpositive
    have hnextTwo := generalBesselPairQ_succ (column + 1) (by omega)
    have hnextTwo' :
        generalBesselPairQ (column + 2) =
          generalBesselPairQ (column + 1) +
            literalBesselJ (column + 1) + literalBesselJ (column + 2) := by
      simpa [show column + 1 + 1 = column + 2 by omega] using hnextTwo
    simp [gordonOddCumulativeEntry, gordonOddGesselEntry,
      gordonSkewQ, hcol]
    rw [hnext, hnextTwo', hnext]
    ring

theorem gordonOddCumulativeEntry_succ (row column : ℕ) :
    gordonOddCumulativeEntry (row + 1) column =
      gordonOddCumulativeEntry row column +
        gordonOddGesselEntry (row + 1) column +
        gordonOddGesselEntry row column := by
  by_cases hleft : row + 1 < column
  · have hleftPrevious : row < column := by omega
    have hgap : 1 ≤ column - (row + 1) := by omega
    have hhigh := generalBesselPairQ_succ (row + column + 2) (by omega)
    have hlow := generalBesselPairQ_succ (column - (row + 1)) hgap
    have hsub : column - row = column - (row + 1) + 1 := by omega
    simp only [gordonOddCumulativeEntry, gordonOddGesselEntry,
      gordonSkewQ]
    rw [if_pos hleft, if_pos hleftPrevious,
      if_pos (by omega : row + 1 ≤ column),
      if_pos (by omega : row ≤ column)]
    rw [show row + 1 + column + 2 = row + column + 2 + 1 by omega,
      hsub, hhigh, hlow]
    ring
  · by_cases heq : row + 1 = column
    · subst column
      have hhigh := generalBesselPairQ_succ (row + row + 2) (by omega)
      have hnext := generalBesselPairQ_succ (row + row + 3) (by omega)
      simp [gordonOddCumulativeEntry, gordonOddGesselEntry,
        gordonSkewQ, generalBesselPairQ_one]
      rw [show row + 1 + (row + 1) + 2 = row + row + 2 + 1 + 1 by omega,
        show row + (row + 1) + 2 = row + row + 2 + 1 by omega,
        hnext, hhigh]
      ring
    · have hright : column < row + 1 := by omega
      by_cases hadjacent : column = row
      · subst column
        have hhigh := generalBesselPairQ_succ (row + row + 2) (by omega)
        have hnext := generalBesselPairQ_succ (row + row + 3) (by omega)
        simp [gordonOddCumulativeEntry, gordonOddGesselEntry,
          gordonSkewQ, generalBesselPairQ_one]
        rw [show row + 1 + row + 2 = row + row + 2 + 1 by omega,
          hhigh]
        ring
      · have hrightPrevious : column < row := by omega
        have hgap : 1 ≤ row - column := by omega
        have hhigh := generalBesselPairQ_succ (row + column + 2) (by omega)
        have hlow := generalBesselPairQ_succ (row - column) hgap
        have hsub : row + 1 - column = row - column + 1 := by omega
        simp only [gordonOddCumulativeEntry, gordonOddGesselEntry,
          gordonSkewQ]
        rw [if_neg (by omega : ¬row + 1 < column), if_pos hright,
          if_neg (by omega : ¬row < column), if_pos hrightPrevious,
          if_neg (by omega : ¬row + 1 ≤ column),
          if_neg (by omega : ¬row ≤ column)]
        rw [show row + 1 + column + 2 = row + column + 2 + 1 by omega,
          hsub, hhigh, hlow]
        ring

theorem gordonOddCumulativeEntry_eq_gessel_sum (row column : ℕ) :
    gordonOddCumulativeEntry row column =
      gordonOddGesselEntry row column +
        2 * ∑ prior ∈ Finset.range row,
          gordonOddGesselEntry prior column := by
  induction row with
  | zero =>
      rw [gordonOddCumulativeEntry_zero]
      simp
  | succ row ih =>
      rw [gordonOddCumulativeEntry_succ, ih, Finset.sum_range_succ]
      ring

noncomputable def gordonOddGesselMatrix (dimension : ℕ) :
    Matrix (Fin dimension) (Fin dimension) ℚ⟦X⟧ :=
  fun row column => gordonOddGesselEntry row.val column.val

noncomputable def gordonOddCumulativeMatrix (dimension : ℕ) :
    Matrix (Fin dimension) (Fin dimension) ℚ⟦X⟧ :=
  fun row column => gordonOddCumulativeEntry row.val column.val

theorem gordonOddGessel_transpose_mul_upper_apply
    (dimension : ℕ) (row column : Fin dimension) :
    ((gordonOddGesselMatrix dimension)ᵀ *
        gordonUpperMatrix dimension) row column =
      gordonOddGesselEntry column.val row.val +
        2 * ∑ prior ∈ Finset.range column.val,
          gordonOddGesselEntry prior row.val := by
  rw [Matrix.mul_apply]
  unfold gordonUpperMatrix
  change (∑ j : Fin dimension,
      gordonOddGesselEntry j.val row.val *
        gordonUpperNat j.val column.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun value : ℕ =>
    gordonOddGesselEntry value row.val *
      gordonUpperNat value column.val)]
  have hsubset : Finset.range (column.val + 1) ⊆
      Finset.range dimension := by
    intro value hvalue
    rw [Finset.mem_range] at hvalue ⊢
    omega
  have hsum :
      (∑ value ∈ Finset.range (column.val + 1),
        gordonOddGesselEntry value row.val *
          gordonUpperNat value column.val) =
      ∑ value ∈ Finset.range dimension,
        gordonOddGesselEntry value row.val *
          gordonUpperNat value column.val := by
    apply Finset.sum_subset hsubset
    intro value hvalueDimension hvalueOutside
    have hvalueGe : column.val + 1 ≤ value := by
      rw [Finset.mem_range] at hvalueOutside
      omega
    have hgt : column.val < value := by omega
    have hne : value ≠ column.val := Nat.ne_of_gt hgt
    have hnot : ¬value < column.val := Nat.not_lt_of_ge (Nat.le_of_lt hgt)
    simp [gordonUpperNat, hne, hnot]
  rw [← hsum, Finset.sum_range_succ]
  rw [show gordonUpperNat column.val column.val = 1 by
    simp [gordonUpperNat], mul_one]
  rw [show (∑ value ∈ Finset.range column.val,
      gordonOddGesselEntry value row.val *
        gordonUpperNat value column.val) =
      ∑ value ∈ Finset.range column.val,
        2 * gordonOddGesselEntry value row.val by
    apply Finset.sum_congr rfl
    intro value hvalue
    rw [Finset.mem_range] at hvalue
    simp [gordonUpperNat, hvalue, Nat.ne_of_lt hvalue]
    ring]
  rw [← Finset.mul_sum]
  ring

theorem gordonOddCumulativeMatrix_transpose_eq_mul (dimension : ℕ) :
    (gordonOddCumulativeMatrix dimension)ᵀ =
      (gordonOddGesselMatrix dimension)ᵀ * gordonUpperMatrix dimension := by
  apply Matrix.ext
  intro row column
  rw [gordonOddGessel_transpose_mul_upper_apply]
  exact gordonOddCumulativeEntry_eq_gessel_sum column.val row.val

theorem gordonOddCumulativeMatrix_det (dimension : ℕ) :
    (gordonOddCumulativeMatrix dimension).det =
      (gordonOddGesselMatrix dimension).det := by
  rw [← Matrix.det_transpose (gordonOddCumulativeMatrix dimension),
    gordonOddCumulativeMatrix_transpose_eq_mul, Matrix.det_mul,
    Matrix.det_transpose, gordonUpperMatrix_det, mul_one]

theorem gordonOddGesselMatrix_eq_oddFormal (dimension : ℕ) :
    gordonOddGesselMatrix dimension = oddFormalGesselMatrixQ dimension := by
  apply Matrix.ext
  intro row column
  unfold gordonOddGesselMatrix gordonOddGesselEntry oddFormalGesselMatrixQ
    symmetricLiteralBesselJ
  simp only [Int.natAbs_natCast]
  by_cases h : row.val ≤ column.val
  · rw [if_pos h]
    have habs : Int.natAbs ((row.val : ℤ) - column.val) =
        column.val - row.val := by
      have heq : (row.val : ℤ) - column.val =
          -((column.val - row.val : ℕ) : ℤ) := by omega
      rw [heq, Int.natAbs_neg]
      simp
    rw [habs]
  · rw [if_neg h]
    have habs : Int.natAbs ((row.val : ℤ) - column.val) =
        row.val - column.val := by
      have heq : (row.val : ℤ) - column.val =
          ((row.val - column.val : ℕ) : ℤ) := by omega
      rw [heq]
      simp
    rw [habs]

theorem gordonOddCumulativeMatrix_det_eq_formalGessel (dimension : ℕ) :
    (gordonOddCumulativeMatrix dimension).det =
      (oddFormalGesselMatrixQ dimension).det := by
  rw [gordonOddCumulativeMatrix_det,
    gordonOddGesselMatrix_eq_oddFormal]

end FibonacciRibbonKernel
