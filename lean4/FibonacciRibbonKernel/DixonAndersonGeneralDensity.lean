import FibonacciRibbonKernel.DirichletGeneralFubini
import FibonacciRibbonKernel.DixonAndersonChangeVariables

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped Classical Matrix BigOperators

noncomputable def dixonAndersonGeneralCrossProduct {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (parameters : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ) : ℝ :=
  ∏ root, ∏ anchor,
    |roots root - anchors anchor| ^ (parameters anchor - 1)

noncomputable def dixonAndersonGeneralAnchorFactor {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (parameters : Fin (dimension + 1) → ℝ) : ℝ :=
  ∏ first, ∏ next ∈ Finset.Ioi first,
    (anchors first - anchors next) ^
      (parameters first + parameters next - 1)

noncomputable def dixonAndersonGeneralIntegrand {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (parameters : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ) : ℝ :=
  (∏ first : Fin dimension, ∏ next ∈ Finset.Ioi first,
    (roots first - roots next)) *
      dixonAndersonGeneralCrossProduct anchors parameters roots

theorem prod_abs_nodeDenominator_rpow_pair
    {dimension : ℕ} (anchors : Fin (dimension + 1) → ℝ)
    (parameters : Fin (dimension + 1) → ℝ)
    (hanchors : StrictAnti anchors) :
    (∏ anchor,
      |cauchyNodeDenominator anchors anchor| ^
        (parameters anchor - 1)) =
      ∏ first, ∏ next ∈ Finset.Ioi first,
        (anchors first - anchors next) ^
          (parameters first + parameters next - 2) := by
  have hnode (anchor : Fin (dimension + 1)) :
      |cauchyNodeDenominator anchors anchor| ^
          (parameters anchor - 1) =
        ∏ other ∈ Finset.univ.erase anchor,
          |anchors anchor - anchors other| ^
            (parameters anchor - 1) := by
    unfold cauchyNodeDenominator
    rw [Finset.abs_prod]
    exact (Real.finsetProd_rpow
      (Finset.univ.erase anchor)
      (fun other => |anchors anchor - anchors other|)
      (fun other hother => abs_nonneg _)
      (parameters anchor - 1)).symm
  calc
    (∏ anchor,
      |cauchyNodeDenominator anchors anchor| ^
        (parameters anchor - 1)) =
      ∏ anchor, ∏ other ∈ Finset.univ.erase anchor,
        |anchors anchor - anchors other| ^
          (parameters anchor - 1) := by
      apply Finset.prod_congr rfl
      intro anchor hanchor
      exact hnode anchor
    _ = ∏ anchor,
        ∏ other ∈ ({anchor}ᶜ : Finset (Fin (dimension + 1))),
          |anchors anchor - anchors other| ^
            (parameters anchor - 1) := by
      apply Finset.prod_congr rfl
      intro anchor hanchor
      congr 1
      ext other
      simp [eq_comm]
    _ = ∏ first, ∏ next ∈ Finset.Ioi first,
        (|anchors first - anchors next| ^ (parameters first - 1) *
          |anchors next - anchors first| ^
            (parameters next - 1)) := by
      rw [Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag
        (fun next first : Fin (dimension + 1) =>
          |anchors first - anchors next| ^
            (parameters first - 1))]
    _ = ∏ first, ∏ next ∈ Finset.Ioi first,
        (anchors first - anchors next) ^
          (parameters first + parameters next - 2) := by
      apply Finset.prod_congr rfl
      intro first hfirst
      apply Finset.prod_congr rfl
      intro next hnext
      have hdifference : 0 < anchors first - anchors next :=
        sub_pos.mpr (hanchors (Finset.mem_Ioi.mp hnext))
      have habsolute :
          |anchors next - anchors first| =
            anchors first - anchors next := by
        rw [abs_sub_comm, abs_of_pos hdifference]
      rw [habsolute, abs_of_pos hdifference]
      rw [← Real.rpow_add hdifference]
      congr 1
      ring

theorem anchorFactor_eq_vandermonde_mul_denominators
    {dimension : ℕ} (anchors : Fin (dimension + 1) → ℝ)
    (parameters : Fin (dimension + 1) → ℝ)
    (hanchors : StrictAnti anchors) :
    dixonAndersonGeneralAnchorFactor anchors parameters =
      cauchyAbsoluteVandermonde anchors *
        ∏ anchor,
          |cauchyNodeDenominator anchors anchor| ^
            (parameters anchor - 1) := by
  rw [cauchyAbsoluteVandermonde_eq_orderedVandermonde
    anchors hanchors]
  rw [prod_abs_nodeDenominator_rpow_pair
    anchors parameters hanchors]
  unfold dixonAndersonGeneralAnchorFactor
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro first hfirst
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro next hnext
  have hdifference : 0 < anchors first - anchors next :=
    sub_pos.mpr (hanchors (Finset.mem_Ioi.mp hnext))
  symm
  calc
    (anchors first - anchors next) *
        (anchors first - anchors next) ^
          (parameters first + parameters next - 2) =
      (anchors first - anchors next) ^ (1 : ℝ) *
        (anchors first - anchors next) ^
          (parameters first + parameters next - 2) := by
            rw [Real.rpow_one]
    _ = (anchors first - anchors next) ^
        ((1 : ℝ) + (parameters first + parameters next - 2)) := by
          rw [Real.rpow_add hdifference]
    _ = (anchors first - anchors next) ^
        (parameters first + parameters next - 1) := by
          congr 1
          ring

theorem dirichletBarycentric_eq_simplexExtend {dimension : ℕ}
    (coordinates : Fin dimension → ℝ) :
    dirichletBarycentric dimension coordinates =
      simplexExtend coordinates := by
  rfl

theorem dirichletGeneralIntegrand_andersonWeightChart
    {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (parameters : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ)
    (hanchors : Function.Injective anchors) :
    dirichletGeneralIntegrand dimension parameters
        (andersonWeightChart anchors roots) =
      ∏ anchor,
        andersonWeight anchors roots anchor ^
          (parameters anchor - 1) := by
  unfold dirichletGeneralIntegrand
  rw [dirichletBarycentric_eq_simplexExtend]
  rw [simplexExtend_andersonWeightChart anchors roots hanchors]

theorem andersonWeight_eq_abs_product_div_abs_denominator
    {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ)
    (hanchors : StrictAnti anchors)
    (hinterlace : DixonAndersonInterlacing anchors roots)
    (anchor : Fin (dimension + 1)) :
    andersonWeight anchors roots anchor =
      (∏ root, |roots root - anchors anchor|) /
        |cauchyNodeDenominator anchors anchor| := by
  rw [← abs_of_pos
    (andersonWeight_pos anchors roots hanchors hinterlace anchor)]
  rw [andersonWeight_eq_product, abs_div]
  change
    |∏ root, (anchors anchor - roots root)| /
        |cauchyNodeDenominator anchors anchor| = _
  rw [Finset.abs_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro root hroot
  rw [abs_sub_comm]

theorem andersonWeight_rpow_eq
    {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ)
    (hanchors : StrictAnti anchors)
    (hinterlace : DixonAndersonInterlacing anchors roots)
    (anchor : Fin (dimension + 1)) (exponent : ℝ) :
    andersonWeight anchors roots anchor ^ exponent =
      (∏ root, |roots root - anchors anchor|) ^ exponent /
        |cauchyNodeDenominator anchors anchor| ^ exponent := by
  rw [andersonWeight_eq_abs_product_div_abs_denominator
    anchors roots hanchors hinterlace anchor]
  exact Real.div_rpow
    (Finset.prod_nonneg fun root hroot => abs_nonneg _)
    (abs_nonneg _) exponent

theorem dirichletGeneralIntegrand_chart_eq_cross_div_denominators
    {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (parameters : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ)
    (hanchors : StrictAnti anchors)
    (hinterlace : DixonAndersonInterlacing anchors roots) :
    dirichletGeneralIntegrand dimension parameters
        (andersonWeightChart anchors roots) =
      dixonAndersonGeneralCrossProduct anchors parameters roots /
        ∏ anchor,
          |cauchyNodeDenominator anchors anchor| ^
            (parameters anchor - 1) := by
  have hcolumn (anchor : Fin (dimension + 1)) :
      (∏ root, |roots root - anchors anchor|) ^
          (parameters anchor - 1) =
        ∏ root, |roots root - anchors anchor| ^
          (parameters anchor - 1) := by
    exact (Real.finsetProd_rpow
      (Finset.univ : Finset (Fin dimension))
      (fun root => |roots root - anchors anchor|)
      (fun root hroot => abs_nonneg _)
      (parameters anchor - 1)).symm
  rw [dirichletGeneralIntegrand_andersonWeightChart
    anchors parameters roots hanchors.injective]
  simp_rw [andersonWeight_rpow_eq
    anchors roots hanchors hinterlace]
  rw [Finset.prod_div_distrib]
  simp_rw [hcolumn]
  unfold dixonAndersonGeneralCrossProduct
  rw [Finset.prod_comm]

theorem prod_abs_nodeDenominator_rpow_pos
    {dimension : ℕ} (anchors : Fin (dimension + 1) → ℝ)
    (parameters : Fin (dimension + 1) → ℝ)
    (hanchors : StrictAnti anchors) :
    0 < ∏ anchor,
      |cauchyNodeDenominator anchors anchor| ^
        (parameters anchor - 1) := by
  apply Finset.prod_pos
  intro anchor hanchor
  apply Real.rpow_pos_of_pos
  apply abs_pos.mpr
  unfold cauchyNodeDenominator
  apply Finset.prod_ne_zero_iff.mpr
  intro other hother
  have hne : other ≠ anchor := Finset.ne_of_mem_erase hother
  exact sub_ne_zero.mpr (hanchors.injective.ne hne.symm)

theorem anchorFactor_mul_jacobian_mul_dirichlet_eq_generalIntegrand
    {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (parameters : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ)
    (hanchors : StrictAnti anchors)
    (hinterlace : DixonAndersonInterlacing anchors roots) :
    dixonAndersonGeneralAnchorFactor anchors parameters *
        (|(andersonWeightJacobianMatrix anchors roots).det| *
          dirichletGeneralIntegrand dimension parameters
            (andersonWeightChart anchors roots)) =
      dixonAndersonGeneralIntegrand anchors parameters roots := by
  let denominatorProduct := ∏ anchor,
    |cauchyNodeDenominator anchors anchor| ^
      (parameters anchor - 1)
  have hroots : StrictAnti roots :=
    roots_strictAnti_of_interlacing hanchors hinterlace
  have hvandermondeAnchors :
      cauchyAbsoluteVandermonde anchors ≠ 0 :=
    cauchyAbsoluteVandermonde_ne_zero_of_injective hanchors.injective
  have hdenominatorProduct : denominatorProduct ≠ 0 :=
    (prod_abs_nodeDenominator_rpow_pos
      anchors parameters hanchors).ne'
  rw [anchorFactor_eq_vandermonde_mul_denominators
    anchors parameters hanchors]
  rw [abs_det_andersonWeightJacobianMatrix
    anchors roots hanchors hinterlace]
  rw [dirichletGeneralIntegrand_chart_eq_cross_div_denominators
    anchors parameters roots hanchors hinterlace]
  unfold dixonAndersonGeneralIntegrand
  rw [← cauchyAbsoluteVandermonde_eq_orderedVandermonde
    roots hroots]
  change
    (cauchyAbsoluteVandermonde anchors * denominatorProduct) *
      (cauchyAbsoluteVandermonde roots /
        cauchyAbsoluteVandermonde anchors *
        (dixonAndersonGeneralCrossProduct anchors parameters roots /
          denominatorProduct)) = _
  field_simp [hvandermondeAnchors, hdenominatorProduct]

end FibonacciRibbonKernel
