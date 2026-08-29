import FibonacciRibbonKernel.DixonAndersonJacobianMatrix
import Mathlib.LinearAlgebra.Vandermonde

namespace FibonacciRibbonKernel

open scoped Classical Matrix

noncomputable def cauchyBasis {dimension : ℕ}
    (nodes : Fin dimension → ℝ) (column : Fin dimension) : Polynomial ℝ :=
  ∏ other ∈ Finset.univ.erase column,
    (Polynomial.X - Polynomial.C (nodes other))

noncomputable def cauchyEvaluationMatrix {dimension : ℕ}
    (rows columns : Fin dimension → ℝ) :
    Matrix (Fin dimension) (Fin dimension) ℝ :=
  fun row column => (cauchyBasis columns column).eval (rows row)

noncomputable def cauchyCoefficientMatrix {dimension : ℕ}
    (columns : Fin dimension → ℝ) :
    Matrix (Fin dimension) (Fin dimension) ℝ :=
  fun degree column => (cauchyBasis columns column).coeff degree

noncomputable def cauchyMatrix {dimension : ℕ}
    (rows columns : Fin dimension → ℝ) :
    Matrix (Fin dimension) (Fin dimension) ℝ :=
  fun row column => (rows row - columns column)⁻¹

noncomputable def cauchyRowDenominator {dimension : ℕ}
    (rows columns : Fin dimension → ℝ) (row : Fin dimension) : ℝ :=
  ∏ column, (rows row - columns column)

noncomputable def cauchyNodeDenominator {dimension : ℕ}
    (nodes : Fin dimension → ℝ) (node : Fin dimension) : ℝ :=
  ∏ other ∈ Finset.univ.erase node, (nodes node - nodes other)

theorem cauchyBasis_natDegree_le {dimension : ℕ}
    (nodes : Fin dimension → ℝ) (column : Fin dimension) :
    (cauchyBasis nodes column).natDegree < dimension := by
  by_cases hdimension : dimension = 0
  · exact (Fin.elim0 (hdimension ▸ column))
  · have hmonic : (cauchyBasis nodes column).Monic := by
      unfold cauchyBasis
      exact Polynomial.monic_prod_X_sub_C nodes (Finset.univ.erase column)
    unfold cauchyBasis at hmonic ⊢
    rw [Polynomial.natDegree_prod_of_monic]
    · simp
      exact Nat.zero_lt_of_lt column.isLt
    · intro other hother
      exact Polynomial.monic_X_sub_C (nodes other)

theorem cauchyEvaluationMatrix_factorization {dimension : ℕ}
    (rows columns : Fin dimension → ℝ) :
    cauchyEvaluationMatrix rows columns =
      Matrix.vandermonde rows * cauchyCoefficientMatrix columns := by
  ext row column
  unfold cauchyEvaluationMatrix cauchyCoefficientMatrix
  rw [Matrix.mul_apply]
  change (cauchyBasis columns column).eval (rows row) =
    ∑ degree : Fin dimension,
      rows row ^ degree.val *
        (cauchyBasis columns column).coeff degree.val
  rw [Polynomial.eval_eq_sum]
  rw [(cauchyBasis columns column).sum_over_range'
    (fun _ => by simp) dimension
    (cauchyBasis_natDegree_le columns column)]
  calc
    (∑ degree ∈ Finset.range dimension,
        (cauchyBasis columns column).coeff degree * rows row ^ degree) =
      ∑ degree ∈ Finset.range dimension,
        rows row ^ degree * (cauchyBasis columns column).coeff degree := by
      apply Finset.sum_congr rfl
      intro degree hdegree
      ring
    _ = _ := (Fin.sum_univ_eq_sum_range
      (fun degree => rows row ^ degree *
        (cauchyBasis columns column).coeff degree) dimension).symm

theorem cauchyBasis_eval_self {dimension : ℕ}
    (nodes : Fin dimension → ℝ) (node : Fin dimension) :
    (cauchyBasis nodes node).eval (nodes node) =
      cauchyNodeDenominator nodes node := by
  unfold cauchyBasis cauchyNodeDenominator
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro other hother
  simp

theorem cauchyBasis_eval_other {dimension : ℕ}
    (nodes : Fin dimension → ℝ) {row column : Fin dimension}
    (hne : row ≠ column) :
    (cauchyBasis nodes column).eval (nodes row) = 0 := by
  unfold cauchyBasis
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (i := row)
  · simp [hne]
  · simp

theorem cauchyEvaluationMatrix_self_eq_diagonal {dimension : ℕ}
    (nodes : Fin dimension → ℝ) :
    cauchyEvaluationMatrix nodes nodes =
      Matrix.diagonal (cauchyNodeDenominator nodes) := by
  ext row column
  by_cases heq : row = column
  · subst column
    rw [cauchyEvaluationMatrix, cauchyBasis_eval_self]
    simp
  · rw [cauchyEvaluationMatrix,
      cauchyBasis_eval_other nodes heq]
    simp [heq]

theorem cauchyEvaluationMatrix_self_det {dimension : ℕ}
    (nodes : Fin dimension → ℝ) :
    (cauchyEvaluationMatrix nodes nodes).det =
      ∏ node, cauchyNodeDenominator nodes node := by
  rw [cauchyEvaluationMatrix_self_eq_diagonal,
    Matrix.det_diagonal]

theorem cauchyEvaluationMatrix_eq_diagonal_mul_cauchy
    {dimension : ℕ}
    (rows columns : Fin dimension → ℝ)
    (hcross : ∀ row column, rows row ≠ columns column) :
    cauchyEvaluationMatrix rows columns =
      Matrix.diagonal (cauchyRowDenominator rows columns) *
        cauchyMatrix rows columns := by
  ext row column
  rw [Matrix.diagonal_mul]
  unfold cauchyEvaluationMatrix cauchyBasis
  rw [Polynomial.eval_prod]
  unfold cauchyRowDenominator cauchyMatrix
  have hfactor : rows row - columns column ≠ 0 :=
    sub_ne_zero.mpr (hcross row column)
  have hproduct := Finset.prod_erase_mul
    (s := (Finset.univ : Finset (Fin dimension)))
    (f := fun other => rows row - columns other)
    (Finset.mem_univ column)
  have heval :
      (∏ other ∈ Finset.univ.erase column,
        Polynomial.eval (rows row)
          (Polynomial.X - Polynomial.C (columns other))) =
      ∏ other ∈ Finset.univ.erase column,
        (rows row - columns other) := by
    apply Finset.prod_congr rfl
    intro other hother
    simp
  rw [heval]
  rw [← hproduct]
  field_simp [hfactor]

theorem cauchyEvaluationMatrix_det_factorization {dimension : ℕ}
    (rows columns : Fin dimension → ℝ) :
    (cauchyEvaluationMatrix rows columns).det =
      (Matrix.vandermonde rows).det *
        (cauchyCoefficientMatrix columns).det := by
  rw [cauchyEvaluationMatrix_factorization,
    Matrix.det_mul]

theorem cauchyEvaluationMatrix_det_cauchy {dimension : ℕ}
    (rows columns : Fin dimension → ℝ)
    (hcross : ∀ row column, rows row ≠ columns column) :
    (cauchyEvaluationMatrix rows columns).det =
      (∏ row, cauchyRowDenominator rows columns row) *
        (cauchyMatrix rows columns).det := by
  rw [cauchyEvaluationMatrix_eq_diagonal_mul_cauchy
    rows columns hcross, Matrix.det_mul, Matrix.det_diagonal]

end FibonacciRibbonKernel
