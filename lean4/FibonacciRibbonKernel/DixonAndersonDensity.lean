import FibonacciRibbonKernel.DixonAndersonJacobianDeterminant
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

namespace FibonacciRibbonKernel

open scoped Classical Matrix BigOperators

noncomputable def dixonAndersonAbsoluteCrossProduct {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ) : ℝ :=
  ∏ root, ∏ anchor, |roots root - anchors anchor|

theorem cauchyAbsoluteVandermonde_eq_orderedVandermonde
    {dimension : ℕ} (nodes : Fin dimension → ℝ)
    (hnodes : StrictAnti nodes) :
    cauchyAbsoluteVandermonde nodes =
      ∏ first : Fin dimension, ∏ next ∈ Finset.Ioi first,
        (nodes first - nodes next) := by
  unfold cauchyAbsoluteVandermonde
  apply Finset.prod_congr rfl
  intro first hfirst
  apply Finset.prod_congr rfl
  intro next hnext
  rw [abs_sub_comm, abs_of_pos]
  exact sub_pos.mpr (hnodes (Finset.mem_Ioi.mp hnext))

theorem abs_prod_andersonWeight_all
    {dimension : ℕ} (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ) :
    |∏ anchor, andersonWeight anchors roots anchor| =
      dixonAndersonAbsoluteCrossProduct anchors roots /
        cauchyAbsoluteVandermonde anchors ^ 2 := by
  have hweights :
      (∏ anchor, andersonWeight anchors roots anchor) =
      (∏ anchor, ∏ root, (anchors anchor - roots root)) /
        (∏ anchor, andersonWeightDenominator anchors anchor) := by
    simp_rw [andersonWeight_eq_product]
    exact Finset.prod_div_distrib
      (s := (Finset.univ : Finset (Fin (dimension + 1))))
      (fun anchor : Fin (dimension + 1) =>
        ∏ root : Fin dimension, (anchors anchor - roots root))
      (fun anchor : Fin (dimension + 1) =>
        andersonWeightDenominator anchors anchor)
  have hnumerator :
      |∏ anchor, ∏ root, (anchors anchor - roots root)| =
        dixonAndersonAbsoluteCrossProduct anchors roots := by
    unfold dixonAndersonAbsoluteCrossProduct
    simp only [Finset.abs_prod]
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro root hroot
    apply Finset.prod_congr rfl
    intro anchor hanchor
    rw [abs_sub_comm]
  have hdenominator :
      |∏ anchor, andersonWeightDenominator anchors anchor| =
        cauchyAbsoluteVandermonde anchors ^ 2 := by
    change |∏ anchor, cauchyNodeDenominator anchors anchor| = _
    exact abs_prod_cauchyNodeDenominator_eq_sq anchors
  rw [hweights, abs_div, hnumerator, hdenominator]

theorem prod_andersonWeight_all
    {dimension : ℕ} (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ)
    (hanchors : StrictAnti anchors)
    (hinterlace : DixonAndersonInterlacing anchors roots) :
    (∏ anchor, andersonWeight anchors roots anchor) =
      dixonAndersonAbsoluteCrossProduct anchors roots /
        cauchyAbsoluteVandermonde anchors ^ 2 := by
  rw [← abs_prod_andersonWeight_all anchors roots]
  rw [abs_of_pos]
  apply Finset.prod_pos
  intro anchor hanchor
  exact andersonWeight_pos anchors roots hanchors hinterlace anchor

theorem dirichletHalfIntegrand_andersonWeightChart
    {dimension : ℕ} (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ)
    (hanchors : Function.Injective anchors) :
    dirichletHalfIntegrand dimension
        (andersonWeightChart anchors roots) =
      ∏ anchor : Fin (dimension + 1),
        andersonWeight anchors roots anchor ^ (-1 / 2 : ℝ) := by
  have hextend := congrFun
    (simplexExtend_andersonWeightChart anchors roots hanchors)
    (Fin.last dimension)
  rw [simplexExtend_last] at hextend
  have hextend' :
      1 - ∑ index : Fin dimension,
          andersonWeight anchors roots index.castSucc =
        andersonWeight anchors roots (Fin.last dimension) := by
    simpa only [andersonWeightChart] using hextend
  unfold dirichletHalfIntegrand andersonWeightChart
  rw [hextend', Fin.prod_univ_castSucc]

theorem dixonAndersonCrossProduct_rpow
    {dimension : ℕ} (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ) (exponent : ℝ) :
    (∏ root : Fin dimension, ∏ anchor : Fin (dimension + 1),
        |roots root - anchors anchor| ^ exponent) =
      dixonAndersonAbsoluteCrossProduct anchors roots ^ exponent := by
  unfold dixonAndersonAbsoluteCrossProduct
  calc
    (∏ root : Fin dimension, ∏ anchor : Fin (dimension + 1),
        |roots root - anchors anchor| ^ exponent) =
      ∏ root : Fin dimension,
        (∏ anchor : Fin (dimension + 1),
          |roots root - anchors anchor|) ^ exponent := by
      apply Finset.prod_congr rfl
      intro root hroot
      exact Real.finsetProd_rpow
        (Finset.univ : Finset (Fin (dimension + 1)))
        (fun anchor => |roots root - anchors anchor|)
        (fun anchor hanchor => abs_nonneg _) exponent
    _ = (∏ root : Fin dimension,
        ∏ anchor : Fin (dimension + 1),
          |roots root - anchors anchor|) ^ exponent := by
      exact Real.finsetProd_rpow
        (Finset.univ : Finset (Fin dimension))
        (fun root => ∏ anchor : Fin (dimension + 1),
          |roots root - anchors anchor|)
        (fun root hroot => Finset.prod_nonneg fun anchor hanchor =>
          abs_nonneg _) exponent

theorem cauchyAbsoluteVandermonde_pos_of_injective
    {dimension : ℕ} {nodes : Fin dimension → ℝ}
    (hinjective : Function.Injective nodes) :
    0 < cauchyAbsoluteVandermonde nodes := by
  rw [← abs_det_vandermonde_eq_cauchyAbsoluteVandermonde]
  exact abs_pos.mpr
    (Matrix.det_vandermonde_ne_zero_iff.mpr hinjective)

theorem dixonAndersonAbsoluteCrossProduct_pos
    {dimension : ℕ} (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ)
    (hanchors : StrictAnti anchors)
    (hinterlace : DixonAndersonInterlacing anchors roots) :
    0 < dixonAndersonAbsoluteCrossProduct anchors roots := by
  unfold dixonAndersonAbsoluteCrossProduct
  apply Finset.prod_pos
  intro root hroot
  apply Finset.prod_pos
  intro anchor hanchor
  apply abs_pos.mpr
  apply sub_ne_zero.mpr
  exact (sub_ne_zero.mp
    (anchor_sub_root_ne_zero_of_interlacing
      hanchors hinterlace anchor root)).symm

theorem rpow_neg_half_div_sq
    {cross vandermonde : ℝ} (hcross : 0 ≤ cross)
    (hvandermonde : 0 < vandermonde) :
    (cross / vandermonde ^ 2) ^ (-1 / 2 : ℝ) =
      vandermonde * cross ^ (-1 / 2 : ℝ) := by
  have hvandermondeNonneg : 0 ≤ vandermonde := hvandermonde.le
  have hsquareNonneg : 0 ≤ vandermonde ^ 2 := sq_nonneg vandermonde
  rw [Real.div_rpow hcross hsquareNonneg]
  have hsquare :
      (vandermonde ^ 2) ^ (-1 / 2 : ℝ) = vandermonde⁻¹ := by
    rw [← Real.rpow_two]
    rw [← Real.rpow_mul hvandermondeNonneg]
    norm_num
    rw [Real.rpow_neg_one]
  rw [hsquare]
  field_simp [hvandermonde.ne']

theorem andersonJacobian_mul_dirichletHalfIntegrand
    {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ)
    (hanchors : StrictAnti anchors)
    (hinterlace : DixonAndersonInterlacing anchors roots) :
    |(andersonWeightJacobianMatrix anchors roots).det| *
        dirichletHalfIntegrand dimension
          (andersonWeightChart anchors roots) =
      dixonAndersonHalfIntegrand dimension anchors roots := by
  have hroots : StrictAnti roots :=
    roots_strictAnti_of_interlacing hanchors hinterlace
  have hcrossPos := dixonAndersonAbsoluteCrossProduct_pos
    anchors roots hanchors hinterlace
  have hvandermondePos : 0 < cauchyAbsoluteVandermonde anchors :=
    cauchyAbsoluteVandermonde_pos_of_injective hanchors.injective
  rw [abs_det_andersonWeightJacobianMatrix
    anchors roots hanchors hinterlace]
  rw [dirichletHalfIntegrand_andersonWeightChart
    anchors roots hanchors.injective]
  rw [Real.finsetProd_rpow
    (Finset.univ : Finset (Fin (dimension + 1)))
    (fun anchor => andersonWeight anchors roots anchor)
    (fun anchor hanchor =>
      (andersonWeight_pos anchors roots hanchors hinterlace anchor).le)
    (-1 / 2 : ℝ)]
  rw [prod_andersonWeight_all anchors roots hanchors hinterlace]
  rw [rpow_neg_half_div_sq hcrossPos.le hvandermondePos]
  unfold dixonAndersonHalfIntegrand
  rw [← cauchyAbsoluteVandermonde_eq_orderedVandermonde
    roots hroots]
  rw [dixonAndersonCrossProduct_rpow
    anchors roots (-1 / 2 : ℝ)]
  field_simp [hvandermondePos.ne']

end FibonacciRibbonKernel
