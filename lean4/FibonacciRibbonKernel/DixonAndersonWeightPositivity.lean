import FibonacciRibbonKernel.DixonAndersonWeights
import Mathlib.Data.Sign.Basic

namespace FibonacciRibbonKernel

open scoped Classical

theorem sign_prod_eq_neg_one_pow_card_filter_neg
    {indexType : Type*} [DecidableEq indexType]
    (indices : Finset indexType) (values : indexType → ℝ)
    (hnonzero : ∀ index ∈ indices, values index ≠ 0) :
    SignType.sign (∏ index ∈ indices, values index) =
      (-1 : SignType) ^
        (indices.filter fun index => values index < 0).card := by
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices hindex ih =>
      rw [Finset.prod_insert hindex, sign_mul]
      by_cases hnegative : values index < 0
      · rw [sign_neg hnegative]
        rw [Finset.filter_insert, if_pos hnegative,
          Finset.card_insert_of_notMem]
        · rw [ih (fun current hcurrent =>
            hnonzero current (Finset.mem_insert_of_mem hcurrent))]
          rw [pow_succ']
        · exact fun hmem => hindex (Finset.mem_filter.mp hmem).1
      · have hpositive : 0 < values index := by
          have hnonneg : 0 ≤ values index := le_of_not_gt hnegative
          exact lt_of_le_of_ne hnonneg
            (Ne.symm (hnonzero index (Finset.mem_insert_self index indices)))
        rw [sign_pos hpositive, one_mul]
        rw [Finset.filter_insert, if_neg hnegative]
        exact ih (fun current hcurrent =>
          hnonzero current (Finset.mem_insert_of_mem hcurrent))

theorem card_fin_filter_val_lt {dimension : ℕ}
    (anchor : Fin (dimension + 1)) :
    ((Finset.univ : Finset (Fin dimension)).filter
      fun index => index.val < anchor.val).card = anchor.val := by
  let source := (Finset.univ : Finset (Fin dimension)).filter
    fun index => index.val < anchor.val
  let target := Finset.range anchor.val
  have hcard : source.card = target.card := by
    apply Finset.card_nbij (fun index : Fin dimension => index.val)
    · intro index hindex
      simp [source, target] at hindex ⊢
      exact hindex
    · intro first hfirst second hsecond hequal
      exact Fin.ext hequal
    · intro value hvalue
      simp [target] at hvalue
      have hbound : value < dimension := by
        exact lt_of_lt_of_le hvalue (Nat.le_of_lt_succ anchor.isLt)
      refine ⟨⟨value, hbound⟩, ?_, rfl⟩
      simp [source, hvalue]
  simpa [source, target] using hcard

theorem root_lt_anchor_of_lt {dimension : ℕ}
    {anchors : Fin (dimension + 1) → ℝ}
    {roots : Fin dimension → ℝ}
    (hanchors : StrictAnti anchors)
    (hinterlace : DixonAndersonInterlacing anchors roots)
    {root : Fin dimension} {anchor : Fin (dimension + 1)}
    (hlt : root.val < anchor.val) :
    roots root > anchors anchor := by
  have hindex : root.succ ≤ anchor := by
    exact_mod_cast hlt
  exact (hanchors.antitone hindex).trans_lt (hinterlace root).2

theorem anchor_gt_root_of_le {dimension : ℕ}
    {anchors : Fin (dimension + 1) → ℝ}
    {roots : Fin dimension → ℝ}
    (hanchors : StrictAnti anchors)
    (hinterlace : DixonAndersonInterlacing anchors roots)
    {root : Fin dimension} {anchor : Fin (dimension + 1)}
    (hle : anchor.val ≤ root.val) :
    anchors anchor > roots root := by
  have hindex : anchor ≤ root.castSucc := by
    exact_mod_cast hle
  exact (hinterlace root).1.trans_le (hanchors.antitone hindex)

theorem anchor_sub_root_neg_iff {dimension : ℕ}
    {anchors : Fin (dimension + 1) → ℝ}
    {roots : Fin dimension → ℝ}
    (hanchors : StrictAnti anchors)
    (hinterlace : DixonAndersonInterlacing anchors roots)
    (root : Fin dimension) (anchor : Fin (dimension + 1)) :
    anchors anchor - roots root < 0 ↔ root.val < anchor.val := by
  constructor
  · intro hnegative
    by_contra hnot
    have hle : anchor.val ≤ root.val := by omega
    linarith [anchor_gt_root_of_le hanchors hinterlace hle]
  · intro hlt
    linarith [root_lt_anchor_of_lt hanchors hinterlace hlt]

theorem anchor_sub_anchor_neg_iff {dimension : ℕ}
    {anchors : Fin (dimension + 1) → ℝ}
    (hanchors : StrictAnti anchors)
    (anchor other : Fin (dimension + 1)) (hne : other ≠ anchor) :
    anchors anchor - anchors other < 0 ↔ other < anchor := by
  constructor
  · intro hnegative
    by_contra hnot
    have hle : anchor < other := lt_of_le_of_ne
      (le_of_not_gt hnot) hne.symm
    linarith [hanchors hle]
  · intro hlt
    linarith [hanchors hlt]

theorem andersonRootNumerator_sign {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ)
    (hanchors : StrictAnti anchors)
    (hinterlace : DixonAndersonInterlacing anchors roots)
    (anchor : Fin (dimension + 1)) :
    SignType.sign ((andersonRootPolynomial roots).eval (anchors anchor)) =
      (-1 : SignType) ^ anchor.val := by
  rw [show (andersonRootPolynomial roots).eval (anchors anchor) =
      ∏ root : Fin dimension, (anchors anchor - roots root) by
    unfold andersonRootPolynomial
    rw [Polynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro root hroot
    simp]
  rw [sign_prod_eq_neg_one_pow_card_filter_neg]
  · congr 1
    rw [show ((Finset.univ : Finset (Fin dimension)).filter
        fun root => anchors anchor - roots root < 0) =
      (Finset.univ : Finset (Fin dimension)).filter
        fun root => root.val < anchor.val by
      ext root
      simp [anchor_sub_root_neg_iff hanchors hinterlace]]
    exact card_fin_filter_val_lt anchor
  · intro root hroot
    by_cases hlt : root.val < anchor.val
    · linarith [root_lt_anchor_of_lt hanchors hinterlace hlt]
    · have hle : anchor.val ≤ root.val := by omega
      linarith [anchor_gt_root_of_le hanchors hinterlace hle]

theorem andersonDenominator_sign {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (hanchors : StrictAnti anchors)
    (anchor : Fin (dimension + 1)) :
    SignType.sign (∏ other ∈ Finset.univ.erase anchor,
      (anchors anchor - anchors other)) =
      (-1 : SignType) ^ anchor.val := by
  rw [sign_prod_eq_neg_one_pow_card_filter_neg]
  · congr 1
    have hfilter :
        ((Finset.univ.erase anchor).filter fun other =>
          anchors anchor - anchors other < 0) = Finset.Iio anchor := by
      ext other
      by_cases heq : other = anchor
      · subst other
        simp
      · simp only [Finset.mem_filter, Finset.mem_erase,
          Finset.mem_univ, and_true, Finset.mem_Iio]
        constructor
        · rintro ⟨hne, hnegative⟩
          exact (anchor_sub_anchor_neg_iff hanchors anchor other hne).mp hnegative
        · intro hlt
          exact ⟨heq,
            (anchor_sub_anchor_neg_iff hanchors anchor other heq).mpr hlt⟩
    rw [hfilter, Fin.card_Iio]
  · intro other hother
    have hne : other ≠ anchor := Finset.ne_of_mem_erase hother
    exact sub_ne_zero.mpr (hanchors.injective.ne hne.symm)

theorem andersonWeight_pos {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ)
    (hanchors : StrictAnti anchors)
    (hinterlace : DixonAndersonInterlacing anchors roots)
    (anchor : Fin (dimension + 1)) :
    0 < andersonWeight anchors roots anchor := by
  let numerator := (andersonRootPolynomial roots).eval (anchors anchor)
  let denominator := ∏ other ∈ Finset.univ.erase anchor,
    (anchors anchor - anchors other)
  have hsignNumerator : SignType.sign numerator =
      (-1 : SignType) ^ anchor.val :=
    andersonRootNumerator_sign anchors roots hanchors hinterlace anchor
  have hsignDenominator : SignType.sign denominator =
      (-1 : SignType) ^ anchor.val :=
    andersonDenominator_sign anchors hanchors anchor
  have hproductSign : SignType.sign (numerator * denominator) = 1 := by
    rw [sign_mul, hsignNumerator, hsignDenominator]
    rw [← pow_add]
    exact SignType.pow_even (-1)
      ⟨anchor.val, by omega⟩ (by norm_num)
  have hproductPos : 0 < numerator * denominator :=
    sign_eq_one_iff.mp hproductSign
  unfold andersonWeight
  change 0 < numerator / denominator
  rcases mul_pos_iff.mp hproductPos with hsame | hsame
  · exact div_pos hsame.1 hsame.2
  · exact div_pos_of_neg_of_neg hsame.1 hsame.2

end FibonacciRibbonKernel
