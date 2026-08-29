import FibonacciRibbonKernel.DixonAndersonWeightSurjective
import Mathlib.Analysis.Calculus.FDeriv.Mul

namespace FibonacciRibbonKernel

open scoped Classical

noncomputable def andersonWeightDenominator {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (anchor : Fin (dimension + 1)) : ℝ :=
  ∏ other ∈ Finset.univ.erase anchor,
    (anchors anchor - anchors other)

noncomputable def andersonCoordinateProjection {dimension : ℕ}
    (index : Fin dimension) :
    (Fin dimension → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin dimension => ℝ) index

noncomputable def andersonWeightRowDerivative {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ) (anchor : Fin (dimension + 1)) :
    (Fin dimension → ℝ) →L[ℝ] ℝ :=
  ∑ index : Fin dimension,
    (-(∏ other ∈ Finset.univ.erase index,
      (anchors anchor - roots other)) /
        andersonWeightDenominator anchors anchor) •
      andersonCoordinateProjection index

noncomputable def andersonWeightChartDerivative {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ) :
    (Fin dimension → ℝ) →L[ℝ] (Fin dimension → ℝ) :=
  ContinuousLinearMap.pi fun anchor : Fin dimension =>
    andersonWeightRowDerivative anchors roots anchor.castSucc

theorem andersonRootPolynomial_eval_eq_product {dimension : ℕ}
    (roots : Fin dimension → ℝ) (value : ℝ) :
    (andersonRootPolynomial roots).eval value =
      ∏ index : Fin dimension, (value - roots index) := by
  unfold andersonRootPolynomial
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro index hindex
  simp

theorem andersonWeight_eq_product {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ) (anchor : Fin (dimension + 1)) :
    andersonWeight anchors roots anchor =
      (∏ index : Fin dimension, (anchors anchor - roots index)) /
        andersonWeightDenominator anchors anchor := by
  unfold andersonWeight andersonWeightDenominator
  rw [andersonRootPolynomial_eval_eq_product]

theorem hasFDerivAt_anchor_sub_apply {dimension : ℕ}
    (anchorValue : ℝ) (index : Fin dimension)
    (roots : Fin dimension → ℝ) :
    HasFDerivAt (fun current : Fin dimension → ℝ =>
      anchorValue - current index)
      (-(andersonCoordinateProjection index)) roots := by
  have hconstant : HasFDerivAt
      (fun _ : Fin dimension → ℝ => anchorValue)
      (0 : (Fin dimension → ℝ) →L[ℝ] ℝ) roots :=
    hasFDerivAt_const anchorValue roots
  have happly : HasFDerivAt
      (fun current : Fin dimension → ℝ => current index)
      (andersonCoordinateProjection index) roots := by
    exact hasFDerivAt_apply (𝕜 := ℝ) index roots
  change HasFDerivAt
    ((fun _ : Fin dimension → ℝ => anchorValue) -
      fun current => current index)
    (-(andersonCoordinateProjection index)) roots
  exact (hconstant.sub happly).congr_fderiv (by simp)

theorem hasFDerivAt_andersonWeight
    {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ) (anchor : Fin (dimension + 1)) :
    HasFDerivAt (fun current : Fin dimension → ℝ =>
      andersonWeight anchors current anchor)
      (andersonWeightRowDerivative anchors roots anchor) roots := by
  have hproduct := HasFDerivAt.finsetProd
    (u := (Finset.univ : Finset (Fin dimension)))
    (g := fun index : Fin dimension => fun current : Fin dimension → ℝ =>
      anchors anchor - current index)
    (g' := fun index : Fin dimension =>
      -(andersonCoordinateProjection index))
    (fun index hindex =>
      hasFDerivAt_anchor_sub_apply (anchors anchor) index roots)
  have hdivided := hproduct.mul_const
    (andersonWeightDenominator anchors anchor)⁻¹
  have hderivative :
      andersonWeightRowDerivative anchors roots anchor =
        (andersonWeightDenominator anchors anchor)⁻¹ •
          (∑ index : Fin dimension,
            (∏ other ∈ Finset.univ.erase index,
              (anchors anchor - roots other)) •
                (-(andersonCoordinateProjection index))) := by
    unfold andersonWeightRowDerivative
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro index hindex
    apply ContinuousLinearMap.ext
    intro direction
    simp only [smul_apply, neg_apply]
    simp [andersonCoordinateProjection]
    unfold andersonWeightDenominator
    rw [div_eq_mul_inv]
    ring
  rw [show (fun current : Fin dimension → ℝ =>
      andersonWeight anchors current anchor) =
    fun current =>
      (∏ index : Fin dimension, (anchors anchor - current index)) /
        andersonWeightDenominator anchors anchor by
      funext current
      exact andersonWeight_eq_product anchors current anchor]
  simp only [div_eq_mul_inv]
  rw [hderivative]
  exact hdivided

theorem hasFDerivAt_andersonWeightChart
    {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ) :
    HasFDerivAt (andersonWeightChart anchors)
      (andersonWeightChartDerivative anchors roots) roots := by
  unfold andersonWeightChart andersonWeightChartDerivative
  rw [hasFDerivAt_pi]
  intro anchor
  exact hasFDerivAt_andersonWeight anchors roots anchor.castSucc

end FibonacciRibbonKernel
