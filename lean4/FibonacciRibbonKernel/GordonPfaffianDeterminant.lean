import FibonacciRibbonKernel.GeneralGesselActualTarget

namespace FibonacciRibbonKernel

open PowerSeries

noncomputable def gordonGesselEntry (row column : ℕ) : ℚ⟦X⟧ :=
  (if row ≤ column then literalBesselJ (column - row)
    else literalBesselJ (row - column)) +
  literalBesselJ (row + column + 1)

noncomputable def gordonCumulativeEntry (row column : ℕ) : ℚ⟦X⟧ :=
  if row < column then
    generalBesselPairQ (row + column + 1) +
      generalBesselPairQ (column - row)
  else if column < row then
    generalBesselPairQ (row + column + 1) -
      generalBesselPairQ (row - column)
  else
    generalBesselPairQ (row + column + 1)

theorem generalBesselPairQ_zero : generalBesselPairQ 0 = 0 := by
  simp [generalBesselPairQ]

theorem gordonCumulativeEntry_zero (row : ℕ) :
    gordonCumulativeEntry row 0 = gordonGesselEntry row 0 := by
  by_cases hr : row = 0
  · subst row
    simp [gordonCumulativeEntry, gordonGesselEntry,
      generalBesselPairQ_one]
  · have hp : 1 ≤ row := Nat.one_le_iff_ne_zero.2 hr
    have hrp : 0 < row := Nat.zero_lt_of_ne_zero hr
    have hq := generalBesselPairQ_succ row hp
    simp [gordonCumulativeEntry, gordonGesselEntry, hr, hrp, hq]
    ring

theorem gordonCumulativeEntry_succ
    (row column : ℕ) :
    gordonCumulativeEntry row (column + 1) =
      gordonCumulativeEntry row column +
        gordonGesselEntry row (column + 1) +
        gordonGesselEntry row column := by
  by_cases hleft : row < column
  · have hleftSucc : row < column + 1 := by omega
    have hgap : 1 ≤ column - row := by omega
    have hhigh := generalBesselPairQ_succ (row + column + 1) (by omega)
    have hlow := generalBesselPairQ_succ (column - row) hgap
    have hsub : column + 1 - row = column - row + 1 := by omega
    simp only [gordonCumulativeEntry, gordonGesselEntry,
      if_pos hleft, if_pos hleftSucc,
      if_pos (by omega : row ≤ column),
      if_pos (by omega : row ≤ column + 1)]
    rw [show row + (column + 1) + 1 = row + column + 1 + 1 by omega,
      hsub, hhigh, hlow]
    ring
  · by_cases heq : row = column
    · subst row
      have hhigh := generalBesselPairQ_succ (column + column + 1) (by omega)
      simp [gordonCumulativeEntry, gordonGesselEntry,
        generalBesselPairQ_one]
      rw [show column + (column + 1) + 1 =
        column + column + 1 + 1 by omega, hhigh]
      ring
    · have hright : column < row := by omega
      by_cases hadjacent : column + 1 = row
      · subst row
        have hhigh := generalBesselPairQ_succ (column + column + 1) (by omega)
        have hnext := generalBesselPairQ_succ (column + column + 2) (by omega)
        simp [gordonCumulativeEntry, gordonGesselEntry,
          generalBesselPairQ_one]
        rw [show column + 1 + (column + 1) + 1 =
            column + column + 1 + 1 + 1 by omega,
          show column + 1 + column + 1 = column + column + 1 + 1 by omega,
          hnext, hhigh]
        ring
      · have hrightSucc : column + 1 < row := by omega
        have hgapSucc : 1 ≤ row - (column + 1) := by omega
        have hhigh := generalBesselPairQ_succ (row + column + 1) (by omega)
        have hlow := generalBesselPairQ_succ (row - (column + 1)) hgapSucc
        have hsub : row - column = row - (column + 1) + 1 := by omega
        simp only [gordonCumulativeEntry, gordonGesselEntry]
        rw [if_neg (by omega : ¬row < column), if_pos hright,
          if_neg (by omega : ¬row < column + 1), if_pos hrightSucc,
          if_neg (by omega : ¬row ≤ column),
          if_neg (by omega : ¬row ≤ column + 1)]
        rw [show row + (column + 1) + 1 =
            row + column + 1 + 1 by omega,
          hsub, hhigh, hlow]
        ring

theorem gordonCumulativeEntry_eq_gessel_sum
    (row column : ℕ) :
    gordonCumulativeEntry row column =
      gordonGesselEntry row column +
        2 * ∑ prior ∈ Finset.range column,
          gordonGesselEntry row prior := by
  induction column with
  | zero =>
      rw [gordonCumulativeEntry_zero]
      simp
  | succ column ih =>
      rw [gordonCumulativeEntry_succ, ih, Finset.sum_range_succ]
      ring

noncomputable def gordonGesselMatrix
    (dimension : ℕ) : Matrix (Fin dimension) (Fin dimension) ℚ⟦X⟧ :=
  fun row column => gordonGesselEntry row.val column.val

noncomputable def gordonCumulativeMatrix
    (dimension : ℕ) : Matrix (Fin dimension) (Fin dimension) ℚ⟦X⟧ :=
  fun row column => gordonCumulativeEntry row.val column.val

noncomputable def gordonUpperNat (row column : ℕ) : ℚ⟦X⟧ :=
  if row = column then 1 else if row < column then 2 else 0

noncomputable def gordonUpperMatrix
    (dimension : ℕ) : Matrix (Fin dimension) (Fin dimension) ℚ⟦X⟧ :=
  fun row column => gordonUpperNat row.val column.val

theorem gordonUpperMatrix_apply_lt
    {dimension : ℕ} {row column : Fin dimension} (h : row < column) :
    gordonUpperMatrix dimension row column = 2 := by
  change row.val < column.val at h
  have hne : row.val ≠ column.val := Nat.ne_of_lt h
  simp [gordonUpperMatrix, gordonUpperNat, hne, h]

theorem gordonUpperMatrix_apply_eq
    {dimension : ℕ} (column : Fin dimension) :
    gordonUpperMatrix dimension column column = 1 := by
  simp [gordonUpperMatrix, gordonUpperNat]

theorem gordonUpperMatrix_apply_gt
    {dimension : ℕ} {row column : Fin dimension} (h : column < row) :
    gordonUpperMatrix dimension row column = 0 := by
  change column.val < row.val at h
  have hne : row.val ≠ column.val := Nat.ne_of_gt h
  have hnot : ¬row.val < column.val := Nat.not_lt_of_ge (Nat.le_of_lt h)
  simp [gordonUpperMatrix, gordonUpperNat, hne, hnot]

theorem gordonGessel_mul_upper_apply
    (dimension : ℕ) (row column : Fin dimension) :
    (gordonGesselMatrix dimension * gordonUpperMatrix dimension) row column =
      gordonGesselEntry row.val column.val +
        2 * ∑ prior ∈ Finset.range column.val,
          gordonGesselEntry row.val prior := by
  rw [Matrix.mul_apply]
  unfold gordonGesselMatrix gordonUpperMatrix
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    gordonGesselEntry row.val j *
      gordonUpperNat j column.val)]
  have hsubset : Finset.range (column.val + 1) ⊆ Finset.range dimension := by
    intro value hvalue
    rw [Finset.mem_range] at hvalue ⊢
    omega
  have hsum :
      (∑ value ∈ Finset.range (column.val + 1),
        gordonGesselEntry row.val value *
          gordonUpperNat value column.val) =
      ∑ value ∈ Finset.range dimension,
        gordonGesselEntry row.val value *
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
  rw [show (∑ x ∈ Finset.range column.val,
      gordonGesselEntry row.val x *
        gordonUpperNat x column.val) =
      ∑ x ∈ Finset.range column.val,
        2 * gordonGesselEntry row.val x by
    apply Finset.sum_congr rfl
    intro value hvalue
    rw [Finset.mem_range] at hvalue
    simp [gordonUpperNat, hvalue, Nat.ne_of_lt hvalue]
    ring]
  rw [← Finset.mul_sum]
  ring

theorem gordonCumulativeMatrix_eq_mul (dimension : ℕ) :
    gordonCumulativeMatrix dimension =
      gordonGesselMatrix dimension * gordonUpperMatrix dimension := by
  apply Matrix.ext
  intro row column
  rw [gordonGessel_mul_upper_apply]
  exact gordonCumulativeEntry_eq_gessel_sum row.val column.val

theorem gordonUpperMatrix_det (dimension : ℕ) :
    (gordonUpperMatrix dimension).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [gordonUpperMatrix, gordonUpperNat]
  · intro row column hrow
    exact gordonUpperMatrix_apply_gt hrow

theorem gordonCumulativeMatrix_det (dimension : ℕ) :
    (gordonCumulativeMatrix dimension).det =
      (gordonGesselMatrix dimension).det := by
  rw [gordonCumulativeMatrix_eq_mul, Matrix.det_mul,
    gordonUpperMatrix_det, mul_one]

theorem gordonGesselMatrix_eq_evenFormal (dimension : ℕ) :
    gordonGesselMatrix dimension = evenFormalGesselMatrixQ dimension := by
  apply Matrix.ext
  intro row column
  unfold gordonGesselMatrix gordonGesselEntry evenFormalGesselMatrixQ
    symmetricLiteralBesselJ
  simp only [Int.natAbs_natCast]
  by_cases h : row.val ≤ column.val
  · rw [if_pos h]
    have habs : Int.natAbs ((row.val : ℤ) - column.val) =
        column.val - row.val := by
      have heq : (row.val : ℤ) - column.val =
          -((column.val - row.val : ℕ) : ℤ) := by
        omega
      rw [heq, Int.natAbs_neg]
      simp
    rw [habs]
  · rw [if_neg h]
    have habs : Int.natAbs ((row.val : ℤ) - column.val) =
        row.val - column.val := by
      have heq : (row.val : ℤ) - column.val =
          ((row.val - column.val : ℕ) : ℤ) := by
        omega
      rw [heq]
      simp
    rw [habs]

theorem gordonCumulativeMatrix_det_eq_formalGessel (dimension : ℕ) :
    (gordonCumulativeMatrix dimension).det =
      (evenFormalGesselMatrixQ dimension).det := by
  rw [gordonCumulativeMatrix_det, gordonGesselMatrix_eq_evenFormal]

end FibonacciRibbonKernel
