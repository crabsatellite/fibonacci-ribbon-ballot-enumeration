import FibonacciRibbonKernel.CauchyDeterminantAlgebra
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace FibonacciRibbonKernel

open scoped Classical Matrix BigOperators

noncomputable def cauchyAbsoluteVandermonde {dimension : ℕ}
    (nodes : Fin dimension → ℝ) : ℝ :=
  ∏ i : Fin dimension, ∏ j ∈ Finset.Ioi i, |nodes j - nodes i|

noncomputable def cauchyAbsoluteCrossProduct {dimension : ℕ}
    (rows columns : Fin dimension → ℝ) : ℝ :=
  ∏ row, ∏ column, |rows row - columns column|

theorem abs_det_vandermonde_eq_cauchyAbsoluteVandermonde
    {dimension : ℕ} (nodes : Fin dimension → ℝ) :
    |(Matrix.vandermonde nodes).det| =
      cauchyAbsoluteVandermonde nodes := by
  rw [Matrix.det_vandermonde]
  unfold cauchyAbsoluteVandermonde
  simp only [Finset.abs_prod]

theorem abs_prod_cauchyNodeDenominator_eq_sq
    {dimension : ℕ} (nodes : Fin dimension → ℝ) :
    |∏ node, cauchyNodeDenominator nodes node| =
      cauchyAbsoluteVandermonde nodes ^ 2 := by
  unfold cauchyNodeDenominator cauchyAbsoluteVandermonde
  simp only [Finset.abs_prod]
  calc
    (∏ node, ∏ other ∈ Finset.univ.erase node,
        |nodes node - nodes other|) =
        ∏ node, ∏ other ∈ ({node}ᶜ : Finset (Fin dimension)),
          |nodes node - nodes other| := by
      apply Finset.prod_congr rfl
      intro node hnode
      congr 1
      ext other
      simp [eq_comm]
    _ = ∏ i, ∏ j ∈ Finset.Ioi i,
        (|nodes i - nodes j| * |nodes j - nodes i|) := by
      rw [Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag
        (fun j i : Fin dimension => |nodes i - nodes j|)]
    _ = (∏ i, ∏ j ∈ Finset.Ioi i, |nodes j - nodes i|) ^ 2 := by
      rw [pow_two, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j hj
      rw [abs_sub_comm]

theorem abs_det_cauchyCoefficientMatrix
    {dimension : ℕ} (nodes : Fin dimension → ℝ)
    (hinjective : Function.Injective nodes) :
    |(cauchyCoefficientMatrix nodes).det| =
      cauchyAbsoluteVandermonde nodes := by
  have hdet :
      (∏ node, cauchyNodeDenominator nodes node) =
        (Matrix.vandermonde nodes).det *
          (cauchyCoefficientMatrix nodes).det := by
    rw [← cauchyEvaluationMatrix_self_det]
    exact cauchyEvaluationMatrix_det_factorization nodes nodes
  have habs := congrArg abs hdet
  rw [abs_mul,
    abs_prod_cauchyNodeDenominator_eq_sq,
    abs_det_vandermonde_eq_cauchyAbsoluteVandermonde] at habs
  have hvandermonde : cauchyAbsoluteVandermonde nodes ≠ 0 := by
    rw [← abs_det_vandermonde_eq_cauchyAbsoluteVandermonde]
    exact abs_ne_zero.mpr
      (Matrix.det_vandermonde_ne_zero_iff.mpr hinjective)
  rw [pow_two] at habs
  exact mul_left_cancel₀ hvandermonde habs.symm

theorem abs_prod_cauchyRowDenominator
    {dimension : ℕ} (rows columns : Fin dimension → ℝ) :
    |∏ row, cauchyRowDenominator rows columns row| =
      cauchyAbsoluteCrossProduct rows columns := by
  unfold cauchyRowDenominator cauchyAbsoluteCrossProduct
  simp only [Finset.abs_prod]

theorem cauchyAbsoluteCrossProduct_mul_abs_det
    {dimension : ℕ} (rows columns : Fin dimension → ℝ)
    (hcolumns : Function.Injective columns)
    (hcross : ∀ row column, rows row ≠ columns column) :
    cauchyAbsoluteCrossProduct rows columns *
        |(cauchyMatrix rows columns).det| =
      cauchyAbsoluteVandermonde rows *
        cauchyAbsoluteVandermonde columns := by
  have hdet :
      (Matrix.vandermonde rows).det *
          (cauchyCoefficientMatrix columns).det =
        (∏ row, cauchyRowDenominator rows columns row) *
          (cauchyMatrix rows columns).det := by
    rw [← cauchyEvaluationMatrix_det_factorization]
    exact cauchyEvaluationMatrix_det_cauchy rows columns hcross
  have habs := congrArg abs hdet
  rw [abs_mul, abs_mul,
    abs_det_vandermonde_eq_cauchyAbsoluteVandermonde,
    abs_det_cauchyCoefficientMatrix columns hcolumns,
    abs_prod_cauchyRowDenominator] at habs
  exact habs.symm

theorem abs_det_cauchyMatrix
    {dimension : ℕ} (rows columns : Fin dimension → ℝ)
    (hcolumns : Function.Injective columns)
    (hcross : ∀ row column, rows row ≠ columns column) :
    |(cauchyMatrix rows columns).det| =
      cauchyAbsoluteVandermonde rows *
          cauchyAbsoluteVandermonde columns /
        cauchyAbsoluteCrossProduct rows columns := by
  have hcrossProduct : cauchyAbsoluteCrossProduct rows columns ≠ 0 := by
    unfold cauchyAbsoluteCrossProduct
    apply Finset.prod_ne_zero_iff.mpr
    intro row hrow
    apply Finset.prod_ne_zero_iff.mpr
    intro column hcolumn
    exact abs_ne_zero.mpr (sub_ne_zero.mpr (hcross row column))
  apply (eq_div_iff hcrossProduct).mpr
  rw [mul_comm]
  exact cauchyAbsoluteCrossProduct_mul_abs_det
    rows columns hcolumns hcross

end FibonacciRibbonKernel
