import FibonacciRibbonKernel.DixonAndersonWeightDerivative

namespace FibonacciRibbonKernel

open scoped Classical Matrix

noncomputable def andersonWeightJacobianMatrix {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ) : Matrix (Fin dimension) (Fin dimension) ℝ :=
  fun anchor root =>
    -(∏ other ∈ Finset.univ.erase root,
      (anchors anchor.castSucc - roots other)) /
        andersonWeightDenominator anchors anchor.castSucc

noncomputable def andersonWeightJacobianCLM {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ) :
    (Fin dimension → ℝ) →L[ℝ] (Fin dimension → ℝ) :=
  LinearMap.toContinuousLinearMap
    (Matrix.toLin' (andersonWeightJacobianMatrix anchors roots))

noncomputable def andersonCauchyMatrix {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ) : Matrix (Fin dimension) (Fin dimension) ℝ :=
  fun anchor root =>
    (anchors anchor.castSucc - roots root)⁻¹

noncomputable def andersonWeightDiagonal {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ) : Matrix (Fin dimension) (Fin dimension) ℝ :=
  Matrix.diagonal fun anchor =>
    -andersonWeight anchors roots anchor.castSucc

theorem andersonWeightChartDerivative_eq_toLin {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ) :
    andersonWeightChartDerivative anchors roots =
      andersonWeightJacobianCLM anchors roots := by
  apply ContinuousLinearMap.ext
  intro direction
  funext anchor
  unfold andersonWeightChartDerivative andersonWeightRowDerivative
  rw [ContinuousLinearMap.pi_apply]
  rw [_root_.sum_apply]
  simp_rw [smul_apply, andersonCoordinateProjection]
  change (∑ index : Fin dimension,
      ((-(∏ other ∈ Finset.univ.erase index,
        (anchors anchor.castSucc - roots other)) /
          andersonWeightDenominator anchors anchor.castSucc) *
        direction index)) =
    (andersonWeightJacobianCLM anchors roots) direction anchor
  unfold andersonWeightJacobianCLM
  simp only [LinearMap.coe_toContinuousLinearMap']
  rw [Matrix.toLin'_apply]
  unfold Matrix.mulVec dotProduct andersonWeightJacobianMatrix
  rfl

theorem anchor_sub_root_ne_zero_of_interlacing {dimension : ℕ}
    {anchors : Fin (dimension + 1) → ℝ}
    {roots : Fin dimension → ℝ}
    (hanchors : StrictAnti anchors)
    (hinterlace : DixonAndersonInterlacing anchors roots)
    (anchor : Fin (dimension + 1)) (root : Fin dimension) :
    anchors anchor - roots root ≠ 0 := by
  by_cases hlt : root.val < anchor.val
  · linarith [root_lt_anchor_of_lt hanchors hinterlace hlt]
  · have hle : anchor.val ≤ root.val := by omega
    linarith [anchor_gt_root_of_le hanchors hinterlace hle]

theorem andersonWeightJacobianMatrix_entry_cauchy {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ)
    (hanchors : StrictAnti anchors)
    (hinterlace : DixonAndersonInterlacing anchors roots)
    (anchor root : Fin dimension) :
    andersonWeightJacobianMatrix anchors roots anchor root =
      -andersonWeight anchors roots anchor.castSucc *
        (anchors anchor.castSucc - roots root)⁻¹ := by
  let factor := anchors anchor.castSucc - roots root
  have hfactor : factor ≠ 0 :=
    anchor_sub_root_ne_zero_of_interlacing
      hanchors hinterlace anchor.castSucc root
  have hproduct := Finset.prod_erase_mul
    (s := (Finset.univ : Finset (Fin dimension)))
    (f := fun other => anchors anchor.castSucc - roots other)
    (Finset.mem_univ root)
  unfold andersonWeightJacobianMatrix
  rw [andersonWeight_eq_product]
  change -(∏ other ∈ Finset.univ.erase root,
      (anchors anchor.castSucc - roots other)) /
        andersonWeightDenominator anchors anchor.castSucc =
    -((∏ index, (anchors anchor.castSucc - roots index)) /
        andersonWeightDenominator anchors anchor.castSucc) * factor⁻¹
  rw [← hproduct]
  field_simp [hfactor]
  ring

theorem andersonWeightJacobianMatrix_eq_diagonal_mul_cauchy
    {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ)
    (hanchors : StrictAnti anchors)
    (hinterlace : DixonAndersonInterlacing anchors roots) :
    andersonWeightJacobianMatrix anchors roots =
      andersonWeightDiagonal anchors roots *
        andersonCauchyMatrix anchors roots := by
  ext anchor root
  rw [andersonWeightJacobianMatrix_entry_cauchy
    anchors roots hanchors hinterlace]
  unfold andersonWeightDiagonal andersonCauchyMatrix
  rw [Matrix.diagonal_mul]

theorem fderiv_andersonWeightChart {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ) :
    fderiv ℝ (andersonWeightChart anchors) roots =
      andersonWeightJacobianCLM anchors roots := by
  rw [(hasFDerivAt_andersonWeightChart anchors roots).fderiv,
    andersonWeightChartDerivative_eq_toLin]

end FibonacciRibbonKernel
