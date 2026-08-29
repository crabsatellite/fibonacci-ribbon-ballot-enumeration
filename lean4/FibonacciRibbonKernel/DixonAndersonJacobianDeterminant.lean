import FibonacciRibbonKernel.CauchyDeterminantAbsolute

namespace FibonacciRibbonKernel

open scoped Classical Matrix BigOperators

theorem cauchyAbsoluteVandermonde_castSucc_factor
    {dimension : ℕ} (nodes : Fin (dimension + 1) → ℝ) :
    cauchyAbsoluteVandermonde nodes =
      cauchyAbsoluteVandermonde (fun index : Fin dimension =>
        nodes index.castSucc) *
        ∏ index : Fin dimension,
          |nodes index.castSucc - nodes (Fin.last dimension)| := by
  unfold cauchyAbsoluteVandermonde
  rw [Fin.prod_univ_castSucc]
  have hlast :
      (∏ next ∈ Finset.Ioi (Fin.last dimension),
        |nodes next - nodes (Fin.last dimension)|) = 1 := by
    apply Finset.prod_eq_one
    intro next hnext
    have hlt := Finset.mem_Ioi.mp hnext
    exact (not_lt_of_ge next.le_last hlt).elim
  rw [hlast, mul_one]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro index hindex
  rw [show (∏ next ∈ Finset.Ioi index.castSucc,
      |nodes next - nodes index.castSucc|) =
      (∏ next ∈ Finset.Ioi index,
        |nodes next.castSucc - nodes index.castSucc|) *
          |nodes (Fin.last dimension) - nodes index.castSucc| by
    change (∏ next ∈ Finset.Ioc index.castSucc (⊤ : Fin (dimension + 1)),
      |nodes next - nodes index.castSucc|) = _
    have htop : (⊤ : Fin (dimension + 1)) = Fin.last dimension := by
      rfl
    rw [htop]
    rw [← Finset.prod_Ioo_mul_eq_prod_Ioc (Fin.castSucc_lt_last index)]
    congr 1
    rw [← Fin.map_castSuccEmb_Ioi]
    rw [Finset.prod_map]
    rfl]
  rw [abs_sub_comm]

theorem abs_andersonWeightDenominator_castSucc
    {dimension : ℕ} (anchors : Fin (dimension + 1) → ℝ)
    (anchor : Fin dimension) :
    |andersonWeightDenominator anchors anchor.castSucc| =
      |cauchyNodeDenominator
          (fun index : Fin dimension => anchors index.castSucc) anchor| *
        |anchors anchor.castSucc - anchors (Fin.last dimension)| := by
  unfold andersonWeightDenominator cauchyNodeDenominator
  rw [Fin.univ_castSuccEmb]
  simp only [Finset.cons_eq_insert]
  simp only [Finset.abs_prod]
  have hset :
      (insert (Fin.last dimension)
          ((Finset.univ : Finset (Fin dimension)).map Fin.castSuccEmb)).erase
        anchor.castSucc =
      insert (Fin.last dimension)
        ((Finset.univ.erase anchor).map Fin.castSuccEmb) := by
    rw [Finset.erase_insert_of_ne anchor.castSucc_ne_last.symm]
    rw [Finset.map_erase]
    simp only [Fin.castSuccEmb_apply]
  rw [hset, Finset.prod_insert]
  · rw [Finset.prod_map]
    simp only [Fin.castSuccEmb_apply]
    ring
  · simp

theorem abs_prod_andersonWeightDenominator_castSucc
    {dimension : ℕ} (anchors : Fin (dimension + 1) → ℝ) :
    |∏ anchor : Fin dimension,
        andersonWeightDenominator anchors anchor.castSucc| =
      cauchyAbsoluteVandermonde
          (fun index : Fin dimension => anchors index.castSucc) *
        cauchyAbsoluteVandermonde anchors := by
  let firstAnchors := fun index : Fin dimension => anchors index.castSucc
  let lastFactors := ∏ index : Fin dimension,
    |anchors index.castSucc - anchors (Fin.last dimension)|
  have hnode :
      (∏ anchor : Fin dimension,
        |cauchyNodeDenominator firstAnchors anchor|) =
      cauchyAbsoluteVandermonde firstAnchors ^ 2 := by
    rw [← Finset.abs_prod]
    exact abs_prod_cauchyNodeDenominator_eq_sq firstAnchors
  have hsplit :
      (∏ anchor : Fin dimension,
        |andersonWeightDenominator anchors anchor.castSucc|) =
      (∏ anchor : Fin dimension,
        |cauchyNodeDenominator firstAnchors anchor|) * lastFactors := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro anchor hanchor
    exact abs_andersonWeightDenominator_castSucc anchors anchor
  rw [Finset.abs_prod, hsplit, hnode]
  rw [cauchyAbsoluteVandermonde_castSucc_factor anchors]
  change cauchyAbsoluteVandermonde firstAnchors ^ 2 * lastFactors =
    cauchyAbsoluteVandermonde firstAnchors *
      (cauchyAbsoluteVandermonde firstAnchors * lastFactors)
  ring

theorem abs_prod_andersonWeight_castSucc
    {dimension : ℕ} (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ) :
    |∏ anchor : Fin dimension,
        andersonWeight anchors roots anchor.castSucc| =
      cauchyAbsoluteCrossProduct
          (fun anchor : Fin dimension => anchors anchor.castSucc) roots /
        (cauchyAbsoluteVandermonde
            (fun anchor : Fin dimension => anchors anchor.castSucc) *
          cauchyAbsoluteVandermonde anchors) := by
  have hweights :
      (∏ anchor : Fin dimension,
        andersonWeight anchors roots anchor.castSucc) =
      (∏ anchor : Fin dimension,
        ∏ root : Fin dimension,
          (anchors anchor.castSucc - roots root)) /
        (∏ anchor : Fin dimension,
          andersonWeightDenominator anchors anchor.castSucc) := by
    simp_rw [andersonWeight_eq_product]
    exact Finset.prod_div_distrib
      (s := (Finset.univ : Finset (Fin dimension)))
      (fun anchor : Fin dimension =>
        ∏ root : Fin dimension,
          (anchors anchor.castSucc - roots root))
      (fun anchor : Fin dimension =>
        andersonWeightDenominator anchors anchor.castSucc)
  rw [hweights, abs_div,
    abs_prod_andersonWeightDenominator_castSucc]
  unfold cauchyAbsoluteCrossProduct
  simp only [Finset.abs_prod]

theorem cauchyAbsoluteVandermonde_ne_zero_of_injective
    {dimension : ℕ} {nodes : Fin dimension → ℝ}
    (hinjective : Function.Injective nodes) :
    cauchyAbsoluteVandermonde nodes ≠ 0 := by
  rw [← abs_det_vandermonde_eq_cauchyAbsoluteVandermonde]
  exact abs_ne_zero.mpr
    (Matrix.det_vandermonde_ne_zero_iff.mpr hinjective)

theorem cauchyAbsoluteCrossProduct_ne_zero
    {dimension : ℕ} {rows columns : Fin dimension → ℝ}
    (hcross : ∀ row column, rows row ≠ columns column) :
    cauchyAbsoluteCrossProduct rows columns ≠ 0 := by
  unfold cauchyAbsoluteCrossProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro row hrow
  apply Finset.prod_ne_zero_iff.mpr
  intro column hcolumn
  exact abs_ne_zero.mpr (sub_ne_zero.mpr (hcross row column))

theorem abs_det_andersonWeightDiagonal
    {dimension : ℕ} (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ) :
    |(andersonWeightDiagonal anchors roots).det| =
      |∏ anchor : Fin dimension,
        andersonWeight anchors roots anchor.castSucc| := by
  unfold andersonWeightDiagonal
  rw [Matrix.det_diagonal]
  simp only [Finset.abs_prod, abs_neg]

theorem abs_det_andersonWeightJacobianMatrix
    {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ)
    (hanchors : StrictAnti anchors)
    (hinterlace : DixonAndersonInterlacing anchors roots) :
    |(andersonWeightJacobianMatrix anchors roots).det| =
      cauchyAbsoluteVandermonde roots /
        cauchyAbsoluteVandermonde anchors := by
  let firstAnchors := fun anchor : Fin dimension => anchors anchor.castSucc
  have hfirst : StrictAnti firstAnchors := by
    intro first next hlt
    exact hanchors (Fin.castSucc_lt_castSucc_iff.mpr hlt)
  have hroots : StrictAnti roots :=
    roots_strictAnti_of_interlacing hanchors hinterlace
  have hcross : ∀ anchor root,
      firstAnchors anchor ≠ roots root := by
    intro anchor root
    exact sub_ne_zero.mp
      (anchor_sub_root_ne_zero_of_interlacing
        hanchors hinterlace anchor.castSucc root)
  have hvandFirst : cauchyAbsoluteVandermonde firstAnchors ≠ 0 :=
    cauchyAbsoluteVandermonde_ne_zero_of_injective hfirst.injective
  have hvandAnchors : cauchyAbsoluteVandermonde anchors ≠ 0 :=
    cauchyAbsoluteVandermonde_ne_zero_of_injective hanchors.injective
  have hcrossProduct :
      cauchyAbsoluteCrossProduct firstAnchors roots ≠ 0 :=
    cauchyAbsoluteCrossProduct_ne_zero hcross
  rw [andersonWeightJacobianMatrix_eq_diagonal_mul_cauchy
    anchors roots hanchors hinterlace,
    Matrix.det_mul, abs_mul,
    abs_det_andersonWeightDiagonal,
    abs_prod_andersonWeight_castSucc]
  change
    (cauchyAbsoluteCrossProduct firstAnchors roots /
        (cauchyAbsoluteVandermonde firstAnchors *
          cauchyAbsoluteVandermonde anchors)) *
      |(cauchyMatrix firstAnchors roots).det| = _
  rw [abs_det_cauchyMatrix firstAnchors roots
    hroots.injective hcross]
  field_simp [hvandFirst, hvandAnchors, hcrossProduct]

end FibonacciRibbonKernel
