import FibonacciRibbonKernel.GeneralFactorialRows
import Mathlib.LinearAlgebra.Vandermonde

namespace FibonacciRibbonKernel

open scoped Classical

abbrev StrictFinPair (dimension : ℕ) :=
  {pair : Fin dimension × Fin dimension // pair.1 < pair.2}

def strictFinPairRev (dimension : ℕ) :
    StrictFinPair dimension ≃ StrictFinPair dimension where
  toFun pair :=
    ⟨(pair.val.2.rev, pair.val.1.rev),
      Fin.rev_lt_rev.mpr pair.prop⟩
  invFun pair :=
    ⟨(pair.val.2.rev, pair.val.1.rev),
      Fin.rev_lt_rev.mpr pair.prop⟩
  left_inv pair := by ext <;> simp
  right_inv pair := by ext <;> simp

theorem prod_strictFinPair_eq_nested
    {dimension : ℕ} {M : Type*} [CommMonoid M]
    (function : Fin dimension → Fin dimension → M) :
    (∏ pair : StrictFinPair dimension,
        function pair.val.1 pair.val.2) =
      ∏ row : Fin dimension, ∏ next ∈ Finset.Ioi row,
        function row next := by
  classical
  let pairs := ((Finset.univ : Finset (Fin dimension)).product
    (Finset.univ : Finset (Fin dimension))).filter
      (fun pair => pair.1 < pair.2)
  calc
    (∏ pair : StrictFinPair dimension,
        function pair.val.1 pair.val.2) =
        ∏ pair ∈ pairs, function pair.1 pair.2 := by
      symm
      apply Finset.prod_subtype pairs
      intro pair
      simp [pairs]
    _ = ∏ row : Fin dimension, ∏ next ∈ Finset.Ioi row,
        function row next := by
      simp only [pairs, Finset.prod_filter]
      calc
        (∏ pair ∈ (Finset.univ : Finset (Fin dimension)).product
            (Finset.univ : Finset (Fin dimension)),
            if pair.1 < pair.2 then function pair.1 pair.2 else 1) =
            ∏ row : Fin dimension, ∏ next : Fin dimension,
              if row < next then function row next else 1 :=
          Finset.prod_product _ _ _
        _ = _ := by
          apply Finset.prod_congr rfl
          intro row hrow
          rw [← Finset.prod_filter]
          congr 1
          ext next
          simp

theorem vandermonde_reversed_pair_product
    {dimension : ℕ} (values : Fin dimension → ℕ) :
    (∏ row : Fin dimension, ∏ next ∈ Finset.Ioi row,
        ((values next.rev : ℚ) - (values row.rev : ℚ))) =
      ∏ row : Fin dimension, ∏ next ∈ Finset.Ioi row,
        ((values row : ℚ) - (values next : ℚ)) := by
  rw [← prod_strictFinPair_eq_nested,
    ← prod_strictFinPair_eq_nested]
  let function : StrictFinPair dimension → ℚ := fun pair =>
    (values pair.val.2.rev : ℚ) - (values pair.val.1.rev : ℚ)
  have hreindex := Equiv.prod_comp (strictFinPairRev dimension) function
  change (∏ pair : StrictFinPair dimension, function pair) =
    ∏ pair : StrictFinPair dimension,
      ((values pair.val.1 : ℚ) - (values pair.val.2 : ℚ))
  rw [← hreindex]
  apply Finset.prod_congr rfl
  intro pair hpair
  simp [function, strictFinPairRev]

theorem reciprocalFactorialInt_eq_descPochhammer_div_factorial
    (value degree : ℕ) :
    reciprocalFactorialInt ((value : ℤ) - (degree : ℤ)) =
      (descPochhammer ℚ degree).eval (value : ℚ) /
        (value.factorial : ℚ) := by
  by_cases hdegree : degree ≤ value
  · rw [reciprocalFactorialInt_nat_sub hdegree,
      descPochhammer_eval_eq_descFactorial]
    have hfactorial := Nat.factorial_mul_descFactorial hdegree
    have hfactorialQ :
        ((value - degree).factorial : ℚ) *
            (value.descFactorial degree : ℚ) =
          (value.factorial : ℚ) := by
      exact_mod_cast hfactorial
    have hleft : ((value - degree).factorial : ℚ) ≠ 0 := by positivity
    have hright : (value.factorial : ℚ) ≠ 0 := by positivity
    field_simp
    nlinarith
  · have hlt : value < degree := by omega
    rw [reciprocalFactorialInt_nat_sub_eq_zero hlt,
      descPochhammer_eval_eq_descFactorial,
      Nat.descFactorial_eq_zero_iff_lt.mpr hlt]
    simp

noncomputable def reversedPochhammerMatrix
    {dimension : ℕ} (values : Fin dimension → ℕ) :
    Matrix (Fin dimension) (Fin dimension) ℚ :=
  fun row column =>
    (descPochhammer ℚ column.val).eval
      (values row.rev : ℚ)

noncomputable def reversedFactorialScale
    {dimension : ℕ} (values : Fin dimension → ℕ) :
    Fin dimension → ℚ :=
  fun row => ((values row.rev).factorial : ℚ)⁻¹

theorem generalFactorialScalarMatrix_reindex_factor
    {dimension : ℕ} (values : Fin dimension → ℕ) :
    (generalFactorialScalarMatrix values).submatrix
        Fin.revPerm Fin.revPerm =
      Matrix.diagonal (reversedFactorialScale values) *
        reversedPochhammerMatrix values := by
  apply Matrix.ext
  intro row column
  rw [Matrix.diagonal_mul]
  unfold generalFactorialScalarMatrix generalFactorialScalarRow
  unfold reversedFactorialScale reversedPochhammerMatrix
  simp only [Matrix.submatrix_apply, Fin.revPerm_apply, Fin.rev_rev]
  rw [reciprocalFactorialInt_eq_descPochhammer_div_factorial]
  field_simp

theorem det_reversedPochhammerMatrix
    {dimension : ℕ} (values : Fin dimension → ℕ) :
    Matrix.det (reversedPochhammerMatrix values) =
      Matrix.det (Matrix.vandermonde
        (fun row : Fin dimension => (values row.rev : ℚ))) := by
  have hmatrix : reversedPochhammerMatrix values =
      Matrix.of (fun row column : Fin dimension =>
        (descPochhammer ℚ column.val).eval
          (values row.rev : ℚ)) := by
    rfl
  rw [hmatrix]
  exact (Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
      (fun row : Fin dimension => (values row.rev : ℚ))
      (fun column : Fin dimension =>
        descPochhammer ℚ column.val)
      (fun column => descPochhammer_natDegree ℚ column.val)
      (fun column => monic_descPochhammer ℚ column.val)).symm

theorem det_generalFactorialScalarMatrix_vandermonde
    {dimension : ℕ} (values : Fin dimension → ℕ) :
    Matrix.det (generalFactorialScalarMatrix values) =
      (∏ row : Fin dimension,
          ((values row).factorial : ℚ)⁻¹) *
        ∏ row : Fin dimension, ∏ next ∈ Finset.Ioi row,
          ((values next.rev : ℚ) - (values row.rev : ℚ)) := by
  calc
    Matrix.det (generalFactorialScalarMatrix values) =
        Matrix.det ((generalFactorialScalarMatrix values).submatrix
          Fin.revPerm Fin.revPerm) := by
      symm
      exact Matrix.det_submatrix_equiv_self Fin.revPerm _
    _ = Matrix.det
        (Matrix.diagonal (reversedFactorialScale values) *
          reversedPochhammerMatrix values) := by
      rw [generalFactorialScalarMatrix_reindex_factor]
    _ = (∏ row : Fin dimension, reversedFactorialScale values row) *
        Matrix.det (reversedPochhammerMatrix values) := by
      rw [Matrix.det_mul, Matrix.det_diagonal]
    _ = (∏ row : Fin dimension,
          ((values row).factorial : ℚ)⁻¹) *
        Matrix.det (Matrix.vandermonde
          (fun row : Fin dimension => (values row.rev : ℚ))) := by
      rw [det_reversedPochhammerMatrix]
      congr 1
      exact Equiv.prod_comp Fin.revPerm
        (fun row : Fin dimension => ((values row).factorial : ℚ)⁻¹)
    _ = _ := by
      rw [Matrix.det_vandermonde]

theorem det_generalFactorialScalarMatrix_matsumoto
    {dimension : ℕ} (values : Fin dimension → ℕ) :
    Matrix.det (generalFactorialScalarMatrix values) =
      (∏ row : Fin dimension,
          ((values row).factorial : ℚ)⁻¹) *
        ∏ row : Fin dimension, ∏ next ∈ Finset.Ioi row,
          ((values row : ℚ) - (values next : ℚ)) := by
  rw [det_generalFactorialScalarMatrix_vandermonde,
    vandermonde_reversed_pair_product]

theorem shiftedTuple_pair_difference_eq_matsumoto
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (row next : Fin (rank + 1)) :
    (shape.toStrictShiftedTuple.values row : ℚ) -
        shape.toStrictShiftedTuple.values next =
      ((shape.1 row).val : ℚ) - (shape.1 next).val +
        (next.val : ℚ) - row.val := by
  rw [BoundedPartition.toStrictShiftedTuple_values,
    BoundedPartition.toStrictShiftedTuple_values]
  have hrow : row.rev.val + row.val = rank := by
    simp [Fin.rev]
    omega
  have hnext : next.rev.val + next.val = rank := by
    simp [Fin.rev]
    omega
  have hrowQ : (row.rev.val : ℚ) + row.val = rank := by
    exact_mod_cast hrow
  have hnextQ : (next.rev.val : ℚ) + next.val = rank := by
    exact_mod_cast hnext
  push_cast
  linarith

theorem standardTableauNumber_eq_matsumoto_product
    {rank size : ℕ} (shape : BoundedPartition rank size) :
    (standardTableauNumber shape : ℚ) =
      (size.factorial : ℚ) *
        ((∏ row : Fin (rank + 1),
            ((shape.toStrictShiftedTuple.values row).factorial : ℚ)⁻¹) *
          ∏ row : Fin (rank + 1), ∏ next ∈ Finset.Ioi row,
            ((shape.toStrictShiftedTuple.values row : ℚ) -
              shape.toStrictShiftedTuple.values next)) := by
  rw [standardTableauNumber_eq_factorial_mul_boundedFactorialDeterminant,
    boundedFactorialDeterminant_eq_generalStrictMatrix,
    det_generalFactorialScalarMatrix_matsumoto]

/-- Matsumoto's displayed hook product in the literal row coordinates:
`lambda_i-lambda_j+j-i` divided by the shifted row factorials. -/
theorem standardTableauNumber_eq_matsumoto_row_product
    {rank size : ℕ} (shape : BoundedPartition rank size) :
    (standardTableauNumber shape : ℚ) =
      (size.factorial : ℚ) *
        ((∏ row : Fin (rank + 1),
            (((shape.1 row).val + row.rev.val).factorial : ℚ)⁻¹) *
          ∏ row : Fin (rank + 1), ∏ next ∈ Finset.Ioi row,
            (((shape.1 row).val : ℚ) - (shape.1 next).val +
              (next.val : ℚ) - row.val)) := by
  rw [standardTableauNumber_eq_matsumoto_product]
  congr 2
  apply Finset.prod_congr rfl
  intro row hrow
  apply Finset.prod_congr rfl
  intro next hnext
  exact shiftedTuple_pair_difference_eq_matsumoto shape row next

/-- Exact finite lattice sum to which Matsumoto applies the local Stirling
limit and dominated Riemann-sum argument. -/
theorem unrestrictedCount_eq_matsumoto_lattice_sum
    (rank size : ℕ) :
    (unrestrictedCount rank size : ℚ) =
      ∑ shape : BoundedPartition rank size,
        (size.factorial : ℚ) *
          ((∏ row : Fin (rank + 1),
              (((shape.1 row).val + row.rev.val).factorial : ℚ)⁻¹) *
            ∏ row : Fin (rank + 1), ∏ next ∈ Finset.Ioi row,
              (((shape.1 row).val : ℚ) - (shape.1 next).val +
                (next.val : ℚ) - row.val)) := by
  rw [unrestrictedCount_eq_sum_standardTableauNumbers]
  push_cast
  apply Finset.sum_congr rfl
  intro shape hshape
  exact standardTableauNumber_eq_matsumoto_row_product shape

end FibonacciRibbonKernel
