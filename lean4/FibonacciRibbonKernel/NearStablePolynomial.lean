import FibonacciRibbonKernel.TailStrips
import FibonacciRibbonKernel.DiscretePolynomial
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace FibonacciRibbonKernel

open scoped Classical

abbrev TailPartition (tail : ℕ) := BoundedPartition tail tail

theorem BoundedPartition.firstRow_le_size
    {rank size : ℕ} (shape : BoundedPartition rank size) :
    shape.firstRow ≤ size := by
  unfold BoundedPartition.firstRow
  have hbound := (shape.1 0).isLt
  omega

theorem BoundedPartition.youngDiagram_rowLens_sum
    {rank size : ℕ} (shape : BoundedPartition rank size) :
    shape.youngDiagram.rowLens.sum = size := by
  rw [← YoungDiagram.card_eq_sum_rowLens, shape.youngDiagram_card]

theorem BoundedPartition.youngDiagram_rowLens_head_le_size
    {rank size : ℕ} (shape : BoundedPartition rank size)
    {value : ℕ} (hvalue : value ∈ shape.youngDiagram.rowLens) :
    value ≤ size := by
  have hpos := shape.youngDiagram.pos_of_mem_rowLens value hvalue
  have hsum := shape.youngDiagram_rowLens_sum
  have hle := List.le_sum_of_mem hvalue
  omega

theorem cons_tailRows_sorted
    (tail : ℕ) (partition : TailPartition tail)
    (total : ℕ) (hlarge : 2 * tail < total) :
    ((total - tail) :: partition.youngDiagram.rowLens).SortedGE := by
  apply List.Pairwise.sortedGE
  rw [List.pairwise_cons]
  constructor
  · intro value hvalue
    have hle := partition.youngDiagram_rowLens_head_le_size hvalue
    omega
  · exact partition.youngDiagram.rowLens_sorted.pairwise

noncomputable def extendedTailDiagram
    (tail : ℕ) (partition : TailPartition tail)
    (total : ℕ) (hlarge : 2 * tail < total) : YoungDiagram :=
  YoungDiagram.ofRowLens
    ((total - tail) :: partition.youngDiagram.rowLens)
    (cons_tailRows_sorted tail partition total hlarge)

@[simp] theorem extendedTailDiagram_rowLens
    (tail : ℕ) (partition : TailPartition tail)
    (total : ℕ) (hlarge : 2 * tail < total) :
    (extendedTailDiagram tail partition total hlarge).rowLens =
      (total - tail) :: partition.youngDiagram.rowLens := by
  unfold extendedTailDiagram
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  intro value hvalue
  simp only [List.mem_cons] at hvalue
  rcases hvalue with rfl | hvalue
  · omega
  · exact partition.youngDiagram.pos_of_mem_rowLens value hvalue

@[simp] theorem extendedTailDiagram_card
    (tail : ℕ) (partition : TailPartition tail)
    (total : ℕ) (hlarge : 2 * tail < total) :
    (extendedTailDiagram tail partition total hlarge).card = total := by
  rw [YoungDiagram.card_eq_sum_rowLens, extendedTailDiagram_rowLens]
  simp only [List.sum_cons]
  rw [partition.youngDiagram_rowLens_sum]
  omega

theorem extendedTailDiagram_rowLen_zero
    (tail : ℕ) (partition : TailPartition tail)
    (total : ℕ) (hlarge : 2 * tail < total) :
    (extendedTailDiagram tail partition total hlarge).rowLen 0 =
      total - tail := by
  exact FibonacciRibbonKernel.YoungDiagram.rowLen_zero_eq_of_rowLens_eq_cons
    _ _ _ (extendedTailDiagram_rowLens tail partition total hlarge)

theorem extendedTailDiagram_rowLen_succ
    (tail : ℕ) (partition : TailPartition tail)
    (total : ℕ) (hlarge : 2 * tail < total) (row : ℕ) :
    (extendedTailDiagram tail partition total hlarge).rowLen (row + 1) =
      partition.youngDiagram.rowLen row := by
  by_cases hrow : row < partition.youngDiagram.rowLens.length
  · have hext : row + 1 <
        (extendedTailDiagram tail partition total hlarge).rowLens.length := by
      rw [extendedTailDiagram_rowLens]
      simpa using hrow
    have hgetExt := YoungDiagram.get_rowLens
      (μ := extendedTailDiagram tail partition total hlarge)
      (i := row + 1) (h := hext)
    have hgetTail := YoungDiagram.get_rowLens
      (μ := partition.youngDiagram) (i := row) (h := hrow)
    have hentry :
        (extendedTailDiagram tail partition total hlarge).rowLens[row + 1]? =
          partition.youngDiagram.rowLens[row]? := by
      rw [extendedTailDiagram_rowLens]
      simp
    rw [List.getElem?_eq_getElem hext,
      List.getElem?_eq_getElem hrow] at hentry
    injection hentry with hvalues
    exact hgetExt.symm.trans (hvalues.trans hgetTail)
  · have htailZero := YoungDiagram.rowLen'_eq_zero_of_ge_length
      (γ := partition.youngDiagram) row (by omega)
    have hextLength :
        (extendedTailDiagram tail partition total hlarge).rowLens.length =
          partition.youngDiagram.rowLens.length + 1 := by
      rw [extendedTailDiagram_rowLens]
      simp
    have hextZero := YoungDiagram.rowLen'_eq_zero_of_ge_length
      (γ := extendedTailDiagram tail partition total hlarge) (row + 1) (by
        rw [hextLength]
        omega)
    simpa only [YoungDiagram.rowLen'_eq_rowLen] using hextZero.trans htailZero.symm

theorem extendedTailDiagram_rowLen'_succ
    (tail : ℕ) (partition : TailPartition tail)
    (total : ℕ) (hlarge : 2 * tail < total) (row : ℕ) :
    (extendedTailDiagram tail partition total hlarge).rowLen' (row + 1) =
      partition.youngDiagram.rowLen' row := by
  simpa only [YoungDiagram.rowLen'_eq_rowLen] using
    extendedTailDiagram_rowLen_succ tail partition total hlarge row

noncomputable def extendedTailShape
    (tail : ℕ) (partition : TailPartition tail)
    (total : ℕ) (hlarge : 2 * tail < total) :
    BoundedPartition total total :=
  diagramBoundedPartition (extendedTailDiagram tail partition total hlarge)
    total total (extendedTailDiagram_card tail partition total hlarge)
    (by
      have h := FibonacciRibbonKernel.YoungDiagram.colLen_zero_le_card
        (extendedTailDiagram tail partition total hlarge)
      rw [extendedTailDiagram_card] at h
      omega)

@[simp] theorem extendedTailShape_diagram
    (tail : ℕ) (partition : TailPartition tail)
    (total : ℕ) (hlarge : 2 * tail < total) :
    (extendedTailShape tail partition total hlarge).youngDiagram =
      extendedTailDiagram tail partition total hlarge := by
  unfold extendedTailShape
  rw [diagramBoundedPartition_youngDiagram]

@[simp] theorem extendedTailShape_firstRow
    (tail : ℕ) (partition : TailPartition tail)
    (total : ℕ) (hlarge : 2 * tail < total) :
    (extendedTailShape tail partition total hlarge).firstRow =
      total - tail := by
  unfold BoundedPartition.firstRow
  have hrow := (extendedTailShape tail partition total hlarge)
    |>.youngDiagram_rowLen 0
  rw [extendedTailShape_diagram] at hrow
  change (extendedTailDiagram tail partition total hlarge).rowLen 0 =
    ((extendedTailShape tail partition total hlarge).1 0).val at hrow
  exact hrow.symm.trans
    (extendedTailDiagram_rowLen_zero tail partition total hlarge)

theorem extendedTailShape_exact_tail
    (tail : ℕ) (partition : TailPartition tail)
    (total : ℕ) (hlarge : 2 * tail < total) :
    total - (extendedTailShape tail partition total hlarge).firstRow = tail := by
  rw [extendedTailShape_firstRow]
  omega

noncomputable def extendedSubSingleEquiv
    (tail : ℕ) (partition : TailPartition tail)
    (total : ℕ) (hlarge : 2 * tail < total) :
    SubSingle (extendedTailDiagram tail partition total hlarge) ≃
      Option (SubSingle partition.youngDiagram) where
  toFun removal := by
    if hzero : removal.1 = 0 then
      exact none
    else
      let row : ℕ := removal.1 - 1
      refine some ⟨row, ?_⟩
      constructor
      · intro index
        have hcondition := removal.2.1 (index + 1)
        simp only [Finsupp.single_apply] at hcondition ⊢
        rw [extendedTailDiagram_rowLen'_succ,
          extendedTailDiagram_rowLen'_succ] at hcondition
        by_cases heq : row = index
        · rw [if_pos heq]
          have hremoval : removal.1 = index + 1 := by
            dsimp [row] at heq
            omega
          rw [if_pos hremoval] at hcondition
          exact hcondition
        · rw [if_neg heq]
          have hremoval : removal.1 ≠ index + 1 := by
            intro h
            apply heq
            dsimp [row]
            omega
          rw [if_neg hremoval] at hcondition
          exact hcondition
      · intro index
        have hbound := removal.2.2 (index + 1)
        simp only [Finsupp.single_apply] at hbound ⊢
        rw [extendedTailDiagram_rowLen'_succ] at hbound
        by_cases heq : row = index
        · rw [if_pos heq]
          have hremoval : removal.1 = index + 1 := by
            dsimp [row] at heq
            omega
          rw [if_pos hremoval] at hbound
          exact hbound
        · rw [if_neg heq]
          exact zero_le
  invFun
    | none => by
        refine ⟨0, ?_⟩
        constructor
        · intro index
          simp only [Finsupp.single_apply]
          by_cases hindex : index = 0
          · subst index
            rw [if_pos rfl, YoungDiagram.rowLen'_eq_rowLen,
              extendedTailDiagram_rowLen_zero,
              YoungDiagram.rowLen'_eq_rowLen,
              extendedTailDiagram_rowLen_succ]
            have htail := partition.firstRow_le_size
            have hrow : partition.youngDiagram.rowLen 0 =
                partition.firstRow := partition.youngDiagram_rowLen 0
            omega
          · rw [if_neg (Ne.symm hindex)]
            exact (extendedTailDiagram tail partition total hlarge)
              |>.rowLen'_anti index.le_succ
        · intro index
          simp only [Finsupp.single_apply]
          by_cases hindex : index = 0
          · subst index
            rw [if_pos rfl, YoungDiagram.rowLen'_eq_rowLen,
              extendedTailDiagram_rowLen_zero]
            omega
          · rw [if_neg (Ne.symm hindex)]
            exact zero_le
    | some removal => by
        refine ⟨removal.1 + 1, ?_⟩
        constructor
        · intro index
          simp only [Finsupp.single_apply]
          by_cases hzero : index = 0
          · subst index
            rw [if_neg (by omega), YoungDiagram.rowLen'_eq_rowLen,
              extendedTailDiagram_rowLen_zero,
              YoungDiagram.rowLen'_eq_rowLen,
              extendedTailDiagram_rowLen_succ]
            have htail := partition.firstRow_le_size
            have hrow : partition.youngDiagram.rowLen 0 =
                partition.firstRow := partition.youngDiagram_rowLen 0
            omega
          · let row : ℕ := index - 1
            have hindex : index = row + 1 := by
              dsimp [row]
              omega
            rw [hindex, YoungDiagram.rowLen'_eq_rowLen,
              YoungDiagram.rowLen'_eq_rowLen,
              extendedTailDiagram_rowLen_succ,
              extendedTailDiagram_rowLen_succ]
            by_cases heq : removal.1 + 1 = row + 1
            · rw [if_pos heq]
              have hrowEq : removal.1 = row := by omega
              simpa only [YoungDiagram.rowLen'_eq_rowLen, hrowEq,
                Finsupp.single_eq_same, Nat.sub_self] using removal.2.1 row
            · rw [if_neg heq]
              have hrowNe : removal.1 ≠ row := by omega
              have hanti := partition.youngDiagram.rowLen_anti row (row + 1) (by omega)
              exact hanti
        · intro index
          simp only [Finsupp.single_apply]
          by_cases heq : removal.1 + 1 = index
          · rw [if_pos heq, YoungDiagram.rowLen'_eq_rowLen]
            have hindex : index = removal.1 + 1 := heq.symm
            rw [hindex, extendedTailDiagram_rowLen_succ]
            simpa only [YoungDiagram.rowLen'_eq_rowLen,
              Finsupp.single_eq_same] using removal.2.2 removal.1
          · rw [if_neg heq]
            exact zero_le
  left_inv removal := by
    apply Subtype.ext
    by_cases hzero : removal.1 = 0
    · simp only [dif_pos hzero]
      exact hzero.symm
    · simp only [dif_neg hzero]
      omega
  right_inv removal := by
    cases removal with
    | none =>
        rfl
    | some removal =>
        dsimp

noncomputable def tailRemovedDiagram
    {tail : ℕ} (partition : TailPartition tail)
    (removal : SubSingle partition.youngDiagram) : YoungDiagram :=
  partition.youngDiagram.sub (Finsupp.single removal.1 1)

@[simp] theorem tailRemovedDiagram_card
    {tail : ℕ} (partition : TailPartition tail)
    (removal : SubSingle partition.youngDiagram) :
    (tailRemovedDiagram partition removal).card = tail - 1 := by
  unfold tailRemovedDiagram
  rw [YoungDiagram.card_sub (YoungDiagram.sub_cond removal.2.1) removal.2.2,
    partition.youngDiagram_card]
  simp

noncomputable def tailRemovedPartition
    {tail : ℕ} (partition : TailPartition tail)
    (removal : SubSingle partition.youngDiagram) :
    TailPartition (tail - 1) :=
  diagramBoundedPartition (tailRemovedDiagram partition removal)
    (tail - 1) (tail - 1) (tailRemovedDiagram_card partition removal)
    (by
      have h := FibonacciRibbonKernel.YoungDiagram.colLen_zero_le_card
        (tailRemovedDiagram partition removal)
      rw [tailRemovedDiagram_card] at h
      omega)

@[simp] theorem tailRemovedPartition_diagram
    {tail : ℕ} (partition : TailPartition tail)
    (removal : SubSingle partition.youngDiagram) :
    (tailRemovedPartition partition removal).youngDiagram =
      tailRemovedDiagram partition removal := by
  unfold tailRemovedPartition
  rw [diagramBoundedPartition_youngDiagram]

theorem subSingle_diagram_card_pos
    {diagram : YoungDiagram} (removal : SubSingle diagram) :
    0 < diagram.card := by
  have hbound := removal.2.2 removal.1
  rw [Finsupp.single_eq_same, YoungDiagram.rowLen'_eq_rowLen] at hbound
  have hrowCell : diagram.rowLen removal.1 ≤ diagram.card := by
    rw [YoungDiagram.rowLen_eq_card]
    exact Finset.card_le_card (by
      intro cell hcell
      exact (YoungDiagram.mem_row_iff.mp hcell).1)
  omega

theorem tail_pos_of_subSingle
    {tail : ℕ} (partition : TailPartition tail)
    (removal : SubSingle partition.youngDiagram) : 0 < tail := by
  have hpos := subSingle_diagram_card_pos removal
  rw [partition.youngDiagram_card] at hpos
  exact hpos

@[simp] theorem extendedSubSingleEquiv_symm_none_val
    (tail : ℕ) (partition : TailPartition tail)
    (total : ℕ) (hlarge : 2 * tail < total) :
    ((extendedSubSingleEquiv tail partition total hlarge).symm none).1 = 0 := rfl

@[simp] theorem extendedSubSingleEquiv_symm_some_val
    (tail : ℕ) (partition : TailPartition tail)
    (total : ℕ) (hlarge : 2 * tail < total)
    (removal : SubSingle partition.youngDiagram) :
    ((extendedSubSingleEquiv tail partition total hlarge).symm (some removal)).1 =
      removal.1 + 1 := rfl

theorem extendedTailDiagram_sub_none
    (tail : ℕ) (partition : TailPartition tail)
    (total : ℕ) (hlarge : 2 * tail + 1 < total) :
    (extendedTailDiagram tail partition total (by omega)).sub
        (Finsupp.single
          ((extendedSubSingleEquiv tail partition total (by omega)).symm none).1 1) =
      extendedTailDiagram tail partition (total - 1) (by omega) := by
  let extended := extendedTailDiagram tail partition total (by omega)
  let removal := (extendedSubSingleEquiv tail partition total (by omega)).symm none
  have hsubCondition := YoungDiagram.sub_cond removal.2.1
  apply (YoungDiagram.rowLen'_eq_iff).mp
  rw [YoungDiagram.sub_rowLen' hsubCondition]
  apply Finsupp.ext
  intro row
  cases row with
  | zero =>
      have hremoval : removal.1 = 0 := rfl
      rw [hremoval]
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same,
        YoungDiagram.rowLen'_eq_rowLen]
      rw [extendedTailDiagram_rowLen_zero,
        extendedTailDiagram_rowLen_zero]
      omega
  | succ row =>
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
      rw [extendedSubSingleEquiv_symm_none_val,
        if_neg (by omega), tsub_zero,
        extendedTailDiagram_rowLen'_succ,
        extendedTailDiagram_rowLen'_succ]

theorem extendedTailDiagram_sub_some
    (tail : ℕ) (partition : TailPartition tail)
    (total : ℕ) (hlarge : 2 * tail + 1 < total)
    (removal : SubSingle partition.youngDiagram) :
    (extendedTailDiagram tail partition total (by omega)).sub
        (Finsupp.single
          ((extendedSubSingleEquiv tail partition total (by omega)).symm
            (some removal)).1 1) =
      extendedTailDiagram (tail - 1) (tailRemovedPartition partition removal)
        (total - 1) (by
          have htail := tail_pos_of_subSingle partition removal
          omega) := by
  let extended := extendedTailDiagram tail partition total (by omega)
  let extendedRemoval :=
    (extendedSubSingleEquiv tail partition total (by omega)).symm (some removal)
  have hsubCondition := YoungDiagram.sub_cond extendedRemoval.2.1
  apply (YoungDiagram.rowLen'_eq_iff).mp
  rw [YoungDiagram.sub_rowLen' hsubCondition]
  apply Finsupp.ext
  intro row
  cases row with
  | zero =>
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
      rw [extendedSubSingleEquiv_symm_some_val,
        if_neg (by omega), tsub_zero]
      simp only [YoungDiagram.rowLen'_eq_rowLen]
      rw [extendedTailDiagram_rowLen_zero,
        extendedTailDiagram_rowLen_zero]
      have htail := tail_pos_of_subSingle partition removal
      omega
  | succ row =>
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
      rw [extendedSubSingleEquiv_symm_some_val,
        extendedTailDiagram_rowLen'_succ,
        extendedTailDiagram_rowLen'_succ,
        tailRemovedPartition_diagram]
      unfold tailRemovedDiagram
      rw [YoungDiagram.sub_rowLen' (YoungDiagram.sub_cond removal.2.1)]
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
      split_ifs <;> omega

noncomputable def extendedTailTableauNumber
    (tail : ℕ) (partition : TailPartition tail)
    (total : ℕ) (hlarge : 2 * tail < total) : ℕ :=
  standardTableauNumber (extendedTailShape tail partition total hlarge)

theorem extendedTailTableauNumber_eq_kostka
    (tail : ℕ) (partition : TailPartition tail)
    (total : ℕ) (hlarge : 2 * tail < total) :
    extendedTailTableauNumber tail partition total hlarge =
      Kostka.kostkaNumber (extendedTailDiagram tail partition total hlarge)
        (Multiset.replicate total 1) := by
  unfold extendedTailTableauNumber
  rw [standardTableauNumber_eq_kostka_replicate_one,
    extendedTailShape_diagram]

theorem extendedTailTableauNumber_recurrence
    (tail : ℕ) (partition : TailPartition tail)
    (total : ℕ) (hlarge : 2 * tail + 1 < total) :
    extendedTailTableauNumber tail partition total (by omega) =
      extendedTailTableauNumber tail partition (total - 1) (by omega) +
        ∑ removal : SubSingle partition.youngDiagram,
          extendedTailTableauNumber (tail - 1)
            (tailRemovedPartition partition removal) (total - 1)
            (by
              have htail := tail_pos_of_subSingle partition removal
              omega) := by
  rw [extendedTailTableauNumber_eq_kostka]
  have hrec := kostkaStandard_corner_recursion
    (diagram := extendedTailDiagram tail partition total (by omega)) (by
      rw [extendedTailDiagram_card]
      omega)
  rw [extendedTailDiagram_card] at hrec
  rw [hrec]
  let equivalence := extendedSubSingleEquiv tail partition total (by omega)
  let summand : SubSingle (extendedTailDiagram tail partition total (by omega)) → ℕ :=
    fun removal => Kostka.kostkaNumber
      ((extendedTailDiagram tail partition total (by omega)).sub
        (Finsupp.single removal.1 1))
      (Multiset.replicate (total - 1) 1)
  let optionSummand : Option (SubSingle partition.youngDiagram) → ℕ
    | none => extendedTailTableauNumber tail partition (total - 1) (by omega)
    | some removal => extendedTailTableauNumber (tail - 1)
        (tailRemovedPartition partition removal) (total - 1)
        (by
          have htail := tail_pos_of_subSingle partition removal
          omega)
  have hreindex :
      (∑ removal : SubSingle (extendedTailDiagram tail partition total (by omega)),
        summand removal) = ∑ removal : Option (SubSingle partition.youngDiagram),
          optionSummand removal := by
    apply Fintype.sum_equiv equivalence
    intro removal
    cases hoption : equivalence removal with
    | none =>
        have hremoval : removal = equivalence.symm none := by
          apply equivalence.injective
          rw [hoption, equivalence.apply_symm_apply]
        subst removal
        dsimp [summand, optionSummand]
        rw [extendedTailDiagram_sub_none tail partition total hlarge,
          ← extendedTailTableauNumber_eq_kostka]
    | some tailRemoval =>
        have hremoval : removal = equivalence.symm (some tailRemoval) := by
          apply equivalence.injective
          rw [hoption, equivalence.apply_symm_apply]
        subst removal
        dsimp [summand, optionSummand]
        rw [extendedTailDiagram_sub_some tail partition total hlarge tailRemoval,
          ← extendedTailTableauNumber_eq_kostka]
  change (∑ removal, summand removal) = _
  rw [hreindex, Fintype.sum_option]

theorem extendedTailDiagram_zero_eq_horizontal
    (partition : TailPartition 0) (total : ℕ) (hpositive : 0 < total) :
    extendedTailDiagram 0 partition total (by omega) =
      YoungDiagram.horizontalDiagram total := by
  apply (YoungDiagram.eq_iff_rowLens_eq).2
  rw [extendedTailDiagram_rowLens,
    YoungDiagram.horizontalDiagram_rowLens (by omega)]
  have hcard := partition.youngDiagram_card
  have hrowsSum := partition.youngDiagram_rowLens_sum
  have hempty : partition.youngDiagram.rowLens = [] := by
    have hall := (List.sum_eq_zero_iff.mp (by simpa using hrowsSum))
    by_contra hne
    obtain ⟨value, hvalue⟩ :=
      partition.youngDiagram.rowLens.exists_mem_of_ne_nil hne
    have hpos := partition.youngDiagram.pos_of_mem_rowLens value hvalue
    have hzero := hall value hvalue
    omega
  rw [hempty]
  simp

theorem extendedTailTableauNumber_zero
    (partition : TailPartition 0) (total : ℕ) (hpositive : 0 < total) :
    extendedTailTableauNumber 0 partition total (by omega) = 1 := by
  rw [extendedTailTableauNumber_eq_kostka,
    extendedTailDiagram_zero_eq_horizontal]
  apply (kostka_horizontal' total (Multiset.replicate total 1)).2
  simp

noncomputable def tailShapePolynomial :
    (tail : ℕ) → TailPartition tail → Polynomial ℚ
  | 0, _ => 1
  | tail + 1, partition =>
      let lower : Polynomial ℚ :=
        ∑ removal : SubSingle partition.youngDiagram,
          tailShapePolynomial tail (tailRemovedPartition partition removal)
      let primitive := polynomialDiscreteIntegral lower
      let anchor := 2 * (tail + 1) + 2
      primitive + Polynomial.C
        ((extendedTailTableauNumber (tail + 1) partition anchor (by omega) : ℚ) -
          primitive.eval (anchor : ℚ))

theorem tailShapePolynomial_zero
    (partition : TailPartition 0) :
    tailShapePolynomial 0 partition = 1 := rfl

theorem tailShapePolynomial_succ
    (tail : ℕ) (partition : TailPartition (tail + 1)) :
    tailShapePolynomial (tail + 1) partition =
      let lower : Polynomial ℚ :=
        ∑ removal : SubSingle partition.youngDiagram,
          tailShapePolynomial tail (tailRemovedPartition partition removal)
      let primitive := polynomialDiscreteIntegral lower
      let anchor := 2 * (tail + 1) + 2
      primitive + Polynomial.C
        ((extendedTailTableauNumber (tail + 1) partition anchor (by omega) : ℚ) -
          primitive.eval (anchor : ℚ)) := rfl

theorem tailShapePolynomial_eventually_eval :
    ∀ tail : ℕ, ∀ partition : TailPartition tail,
      ∀ total : ℕ, ∀ htotal : 2 * tail + 2 ≤ total,
      (tailShapePolynomial tail partition).eval (total : ℚ) =
        (extendedTailTableauNumber tail partition total (by omega) : ℚ) := by
  intro tail
  induction tail with
  | zero =>
      intro partition total htotal
      rw [tailShapePolynomial_zero, Polynomial.eval_one]
      exact_mod_cast (extendedTailTableauNumber_zero partition total (by omega)).symm
  | succ tail ih =>
      intro partition total htotal
      let lower : Polynomial ℚ :=
        ∑ removal : SubSingle partition.youngDiagram,
          tailShapePolynomial tail (tailRemovedPartition partition removal)
      let primitive := polynomialDiscreteIntegral lower
      let anchor := 2 * (tail + 1) + 2
      have hanchor : anchor ≤ total := by
        dsimp [anchor]
        exact htotal
      induction total, hanchor using Nat.le_induction with
      | base =>
          rw [tailShapePolynomial_succ]
          dsimp [lower, primitive, anchor]
          simp
      | succ total hanchor htotalEval =>
          have hcurrent := htotalEval hanchor
          rw [tailShapePolynomial_succ] at hcurrent ⊢
          dsimp only at hcurrent ⊢
          simp only [Polynomial.eval_add, Polynomial.eval_C] at hcurrent ⊢
          have hcast : ((total + 1 : ℕ) : ℚ) = (total : ℚ) + 1 := by norm_num
          rw [hcast]
          have hdifference := polynomialDiscreteIntegral_eval_succ_sub lower total
          have hlower :
              lower.eval (total : ℚ) =
                ∑ removal : SubSingle partition.youngDiagram,
                  (extendedTailTableauNumber tail
                    (tailRemovedPartition partition removal) total
                    (by
                      have htail := tail_pos_of_subSingle partition removal
                      dsimp [anchor] at hanchor
                      omega) : ℚ) := by
            unfold lower
            rw [Polynomial.eval_finsetSum]
            apply Finset.sum_congr rfl
            intro removal hremoval
            exact ih (tailRemovedPartition partition removal) total (by
              dsimp [anchor] at hanchor
              omega)
          have hrec := extendedTailTableauNumber_recurrence
            (tail + 1) partition (total + 1) (by
              dsimp [anchor] at hanchor
              omega)
          have hrecQ :
              (extendedTailTableauNumber (tail + 1) partition (total + 1)
                  (by omega) : ℚ) =
                extendedTailTableauNumber (tail + 1) partition total (by omega) +
                  ∑ removal : SubSingle partition.youngDiagram,
                    (extendedTailTableauNumber tail
                      (tailRemovedPartition partition removal) total (by
                        have htail := tail_pos_of_subSingle partition removal
                        dsimp [anchor] at hanchor
                        omega) : ℚ) := by
            exact_mod_cast hrec
          rw [hlower] at hdifference
          linarith [hcurrent]

theorem tailShapePolynomial_natDegree_le :
    ∀ tail : ℕ, ∀ partition : TailPartition tail,
      (tailShapePolynomial tail partition).natDegree ≤ tail := by
  intro tail
  induction tail with
  | zero =>
      intro partition
      rw [tailShapePolynomial_zero, Polynomial.natDegree_one]
  | succ tail ih =>
      intro partition
      let lower : Polynomial ℚ :=
        ∑ removal : SubSingle partition.youngDiagram,
          tailShapePolynomial tail (tailRemovedPartition partition removal)
      have hlower : lower.natDegree ≤ tail := by
        apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
        intro exponent hexponent
        unfold lower
        rw [Polynomial.finsetSum_coeff]
        apply Finset.sum_eq_zero
        intro removal hremoval
        exact Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt (ih (tailRemovedPartition partition removal)) hexponent)
      rw [tailShapePolynomial_succ]
      dsimp only
      exact (Polynomial.natDegree_add_le _ _).trans (by
        rw [Polynomial.natDegree_C]
        exact max_le
          (polynomialDiscreteIntegral_natDegree_le lower tail hlower)
          (by omega))

theorem standardTableauNumber_zero_tail
    (partition : TailPartition 0) :
    standardTableauNumber partition = 1 := by
  rw [standardTableauNumber_eq_kostka_replicate_one]
  have hbot : partition.youngDiagram = ⊥ := by
    apply YoungDiagram.eq_bot_iff_card_eq_zero.mpr
    exact partition.youngDiagram_card
  rw [hbot]
  change Kostka.kostkaNumber ⊥ (⊥ : Multiset ℕ) = 1
  exact Kostka.kostka_bot_bot

theorem standardTableauNumber_corner_recurrence
    (tail : ℕ) (partition : TailPartition (tail + 1)) :
    standardTableauNumber partition =
      ∑ removal : SubSingle partition.youngDiagram,
        standardTableauNumber (tailRemovedPartition partition removal) := by
  rw [standardTableauNumber_eq_kostka_replicate_one]
  have hrec := kostkaStandard_corner_recursion
    (diagram := partition.youngDiagram) (by
      rw [partition.youngDiagram_card]
      omega)
  rw [partition.youngDiagram_card] at hrec
  simp only [Nat.add_sub_cancel] at hrec
  rw [hrec]
  apply Finset.sum_congr rfl
  intro removal hremoval
  rw [standardTableauNumber_eq_kostka_replicate_one,
    tailRemovedPartition_diagram]
  rfl

theorem tailShapePolynomial_coeff_top :
    ∀ tail : ℕ, ∀ partition : TailPartition tail,
      (tailShapePolynomial tail partition).coeff tail =
        (standardTableauNumber partition : ℚ) / tail.factorial := by
  intro tail
  induction tail with
  | zero =>
      intro partition
      rw [tailShapePolynomial_zero, Polynomial.coeff_one]
      simp [standardTableauNumber_zero_tail partition]
  | succ tail ih =>
      intro partition
      let lower : Polynomial ℚ :=
        ∑ removal : SubSingle partition.youngDiagram,
          tailShapePolynomial tail (tailRemovedPartition partition removal)
      have hlowerDegree : lower.natDegree ≤ tail := by
        apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
        intro exponent hexponent
        unfold lower
        rw [Polynomial.finsetSum_coeff]
        apply Finset.sum_eq_zero
        intro removal hremoval
        exact Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt
            (tailShapePolynomial_natDegree_le tail
              (tailRemovedPartition partition removal)) hexponent)
      have hlowerCoeff :
          lower.coeff tail =
            (standardTableauNumber partition : ℚ) / tail.factorial := by
        unfold lower
        rw [Polynomial.finsetSum_coeff]
        simp_rw [ih]
        rw [← Finset.sum_div]
        have hrec := standardTableauNumber_corner_recurrence tail partition
        have hrecQ :
            (standardTableauNumber partition : ℚ) =
              ∑ removal : SubSingle partition.youngDiagram,
                (standardTableauNumber
                  (tailRemovedPartition partition removal) : ℚ) := by
          exact_mod_cast hrec
        exact congrArg (fun value : ℚ => value / tail.factorial) hrecQ.symm
      rw [tailShapePolynomial_succ]
      dsimp only
      rw [Polynomial.coeff_add,
        polynomialDiscreteIntegral_coeff_succ lower tail hlowerDegree,
        Polynomial.coeff_C, if_neg (by omega), add_zero]
      rw [hlowerCoeff, Nat.factorial_succ]
      push_cast
      have htailFactorial : (tail.factorial : ℚ) ≠ 0 := by positivity
      have htailSucc : (tail + 1 : ℚ) ≠ 0 := by positivity
      field_simp

theorem rowLens_tail_sorted
    (diagram : YoungDiagram) : diagram.rowLens.tail.SortedGE := by
  have hpair := diagram.rowLens_sorted.pairwise
  cases hrows : diagram.rowLens with
  | nil => exact List.Pairwise.sortedGE (by simp)
  | cons first remaining =>
      rw [hrows] at hpair
      rw [List.pairwise_cons] at hpair
      exact hpair.2.sortedGE

noncomputable def exactShapeTailDiagram
    {total : ℕ} (shape : BoundedPartition total total) : YoungDiagram :=
  YoungDiagram.ofRowLens shape.youngDiagram.rowLens.tail
    (rowLens_tail_sorted shape.youngDiagram)

@[simp] theorem exactShapeTailDiagram_rowLens
    {total : ℕ} (shape : BoundedPartition total total) :
    (exactShapeTailDiagram shape).rowLens = shape.youngDiagram.rowLens.tail := by
  unfold exactShapeTailDiagram
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  intro value hvalue
  exact shape.youngDiagram.pos_of_mem_rowLens value
    (List.mem_of_mem_tail hvalue)

theorem exactShape_rowLens_nonempty
    {total : ℕ} (shape : BoundedPartition total total) (hpositive : 0 < total) :
    shape.youngDiagram.rowLens ≠ [] := by
  intro hempty
  have hsum := shape.youngDiagram_rowLens_sum
  rw [hempty] at hsum
  simp at hsum
  omega

theorem exactShape_rowLens_head
    {total : ℕ} (shape : BoundedPartition total total) (hpositive : 0 < total) :
    shape.youngDiagram.rowLens.head (exactShape_rowLens_nonempty shape hpositive) =
      shape.firstRow := by
  obtain ⟨first, remaining, hremaining⟩ :=
    List.exists_cons_of_ne_nil (exactShape_rowLens_nonempty shape hpositive)
  have hhead : shape.youngDiagram.rowLens.head
      (exactShape_rowLens_nonempty shape hpositive) = first := by
    have hopt := congrArg List.head? hremaining
    have hsome : shape.youngDiagram.rowLens.head? = some first := by
      simpa using hopt
    exact (List.head_eq_iff_head?_eq_some
      (exactShape_rowLens_nonempty shape hpositive)).2 hsome
  have hrow := FibonacciRibbonKernel.YoungDiagram.rowLen_zero_eq_of_rowLens_eq_cons
    shape.youngDiagram first remaining hremaining
  have hshape := shape.youngDiagram_rowLen 0
  exact hhead.trans (hrow.symm.trans hshape)

@[simp] theorem exactShapeTailDiagram_card
    {tail total : ℕ} (shape : BoundedPartition total total)
    (hexact : total - shape.firstRow = tail) (hpositive : 0 < total) :
    (exactShapeTailDiagram shape).card = tail := by
  rw [YoungDiagram.card_eq_sum_rowLens, exactShapeTailDiagram_rowLens]
  have hsum := shape.youngDiagram_rowLens_sum
  have hcons := List.cons_head_tail (exactShape_rowLens_nonempty shape hpositive)
  rw [← hcons, List.sum_cons,
    exactShape_rowLens_head shape hpositive] at hsum
  omega

noncomputable def tailPartitionOfExactShape
    {tail total : ℕ} (shape : BoundedPartition total total)
    (hexact : total - shape.firstRow = tail) (hpositive : 0 < total) :
    TailPartition tail :=
  diagramBoundedPartition (exactShapeTailDiagram shape) tail tail
    (exactShapeTailDiagram_card shape hexact hpositive)
    (by
      have h := FibonacciRibbonKernel.YoungDiagram.colLen_zero_le_card
        (exactShapeTailDiagram shape)
      rw [exactShapeTailDiagram_card shape hexact hpositive] at h
      omega)

@[simp] theorem tailPartitionOfExactShape_diagram
    {tail total : ℕ} (shape : BoundedPartition total total)
    (hexact : total - shape.firstRow = tail) (hpositive : 0 < total) :
    (tailPartitionOfExactShape shape hexact hpositive).youngDiagram =
      exactShapeTailDiagram shape := by
  unfold tailPartitionOfExactShape
  rw [diagramBoundedPartition_youngDiagram]

theorem extendedTailShape_tailPartitionOfExactShape
    {tail total : ℕ} (shape : BoundedPartition total total)
    (hexact : total - shape.firstRow = tail) (hlarge : 2 * tail < total) :
    extendedTailShape tail
      (tailPartitionOfExactShape shape hexact (by omega)) total hlarge = shape := by
  apply BoundedPartition.eq_of_youngDiagram_eq
  rw [extendedTailShape_diagram]
  apply (YoungDiagram.eq_iff_rowLens_eq).2
  rw [extendedTailDiagram_rowLens, tailPartitionOfExactShape_diagram,
    exactShapeTailDiagram_rowLens]
  have hfirst : total - tail = shape.firstRow := by
    have hle := shape.firstRow_le_size
    omega
  rw [hfirst]
  have hhead := exactShape_rowLens_head shape (by omega)
  rw [← hhead]
  exact List.cons_head_tail (exactShape_rowLens_nonempty shape (by omega))

theorem extendedTailShape_injective
    (tail total : ℕ) (hlarge : 2 * tail < total) :
    Function.Injective (fun partition : TailPartition tail =>
      extendedTailShape tail partition total hlarge) := by
  intro left right heq
  apply BoundedPartition.eq_of_youngDiagram_eq
  have hdiagram := congrArg BoundedPartition.youngDiagram heq
  rw [extendedTailShape_diagram, extendedTailShape_diagram,
    YoungDiagram.eq_iff_rowLens_eq,
    extendedTailDiagram_rowLens, extendedTailDiagram_rowLens] at hdiagram
  have htail := congrArg List.tail hdiagram
  simp only [List.tail_cons] at htail
  exact (YoungDiagram.eq_iff_rowLens_eq).2 htail

def ExactTailShape (tail total : ℕ) :=
  {shape : BoundedPartition total total // total - shape.firstRow = tail}

noncomputable instance exactTailShapeFintype (tail total : ℕ) :
    Fintype (ExactTailShape tail total) :=
  classicalSubtypeFintype _

noncomputable def tailPartitionExactShapeEquiv
    (tail total : ℕ) (hlarge : 2 * tail < total) :
    TailPartition tail ≃ ExactTailShape tail total where
  toFun partition :=
    ⟨extendedTailShape tail partition total hlarge,
      extendedTailShape_exact_tail tail partition total hlarge⟩
  invFun shape :=
    tailPartitionOfExactShape shape.1 shape.2 (by omega)
  left_inv partition := by
    apply BoundedPartition.eq_of_youngDiagram_eq
    rw [tailPartitionOfExactShape_diagram]
    apply (YoungDiagram.eq_iff_rowLens_eq).2
    rw [exactShapeTailDiagram_rowLens, extendedTailShape_diagram,
      extendedTailDiagram_rowLens]
    simp
  right_inv shape := by
    apply Subtype.ext
    exact extendedTailShape_tailPartitionOfExactShape shape.1 shape.2 hlarge

theorem exactTailTableauSum_eq_sum_extended
    (tail total : ℕ) (hlarge : 2 * tail < total) :
    exactTailTableauSum tail total =
      ∑ partition : TailPartition tail,
        extendedTailTableauNumber tail partition total hlarge := by
  unfold exactTailTableauSum
  calc
    (∑ shape : BoundedPartition total total,
        if total - shape.firstRow = tail then standardTableauNumber shape else 0) =
        ∑ shape : ExactTailShape tail total,
          standardTableauNumber shape.1 := by
      symm
      let equivalence : ExactTailShape tail total ≃
          {shape : BoundedPartition total total //
            total - shape.firstRow = tail} := Equiv.refl _
      calc
        (∑ shape : ExactTailShape tail total,
            standardTableauNumber shape.1) =
            ∑ shape : {shape : BoundedPartition total total //
              total - shape.firstRow = tail}, standardTableauNumber shape.1 := by
          exact Fintype.sum_equiv equivalence _ _ (by intro; rfl)
        _ = ∑ shape : BoundedPartition total total,
              if total - shape.firstRow = tail then
                standardTableauNumber shape else 0 := by
          rw [← Finset.sum_subtype
            (s := (Finset.univ : Finset (BoundedPartition total total)).filter
              (fun shape => total - shape.firstRow = tail))
            (by intro shape; simp)
            standardTableauNumber]
          rw [Finset.sum_filter]
    _ = ∑ partition : TailPartition tail,
          standardTableauNumber
            (tailPartitionExactShapeEquiv tail total hlarge partition).1 := by
      exact (Equiv.sum_comp (tailPartitionExactShapeEquiv tail total hlarge)
        (fun shape => standardTableauNumber shape.1)).symm
    _ = ∑ partition : TailPartition tail,
          extendedTailTableauNumber tail partition total hlarge := by
      rfl

noncomputable def exactTailPolynomial (tail : ℕ) : Polynomial ℚ :=
  ∑ partition : TailPartition tail, tailShapePolynomial tail partition

theorem exactTailPolynomial_eventually_eval
    (tail total : ℕ) (hlarge : 2 * tail + 2 ≤ total) :
    (exactTailPolynomial tail).eval (total : ℚ) =
      (exactTailTableauSum tail total : ℚ) := by
  unfold exactTailPolynomial
  rw [Polynomial.eval_finsetSum]
  have hsum := exactTailTableauSum_eq_sum_extended tail total (by omega)
  rw [hsum]
  push_cast
  apply Finset.sum_congr rfl
  intro partition hpartition
  exact tailShapePolynomial_eventually_eval tail partition total hlarge

theorem exactTailPolynomial_natDegree_le (tail : ℕ) :
    (exactTailPolynomial tail).natDegree ≤ tail := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro exponent hexponent
  unfold exactTailPolynomial
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro partition hpartition
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (tailShapePolynomial_natDegree_le tail partition) hexponent)

theorem exactTailPolynomial_coeff_top (tail : ℕ) :
    (exactTailPolynomial tail).coeff tail =
      (involutionNumber tail : ℚ) / tail.factorial := by
  unfold exactTailPolynomial
  rw [Polynomial.finsetSum_coeff]
  simp_rw [tailShapePolynomial_coeff_top]
  rw [← Finset.sum_div]
  have hsum :
      (∑ partition : TailPartition tail,
        standardTableauNumber partition) = involutionNumber tail := by
    exact (involutionNumber_eq_sum_standardTableauNumbers tail).symm
  have hsumQ :
      (∑ partition : TailPartition tail,
        (standardTableauNumber partition : ℚ)) = involutionNumber tail := by
    exact_mod_cast hsum
  rw [hsumQ]

noncomputable def tailTableauPolynomial (tail : ℕ) : Polynomial ℚ :=
  ∑ exact ∈ Finset.range (tail + 1), exactTailPolynomial exact

theorem tailTableauPolynomial_eventually_eval
    (tail total : ℕ) (hlarge : 2 * tail + 2 ≤ total) :
    (tailTableauPolynomial tail).eval (total : ℚ) =
      (tailTableauSum tail total : ℚ) := by
  unfold tailTableauPolynomial
  rw [Polynomial.eval_finsetSum]
  have hsplit : tailTableauSum tail total =
      ∑ exact ∈ Finset.range (tail + 1), exactTailTableauSum exact total := by
    unfold tailTableauSum exactTailTableauSum
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro shape hshape
    let defect := total - shape.firstRow
    by_cases hdefect : defect ≤ tail
    · rw [if_pos hdefect]
      have hmem : defect ∈ Finset.range (tail + 1) := by
        simp [defect]
        omega
      rw [Finset.sum_eq_single defect]
      · simp [defect]
      · intro other hother hne
        rw [if_neg (by
          dsimp [defect] at hne ⊢
          exact Ne.symm hne)]
      · simp [hmem]
    · rw [if_neg hdefect]
      symm
      apply Finset.sum_eq_zero
      intro exact hexact
      rw [if_neg]
      simp only [Finset.mem_range] at hexact
      omega
  rw [hsplit]
  push_cast
  apply Finset.sum_congr rfl
  intro exact hexact
  have hexactLe : exact ≤ tail := by
    simp only [Finset.mem_range] at hexact
    omega
  exact exactTailPolynomial_eventually_eval exact total (by omega)

theorem tailTableauPolynomial_natDegree_le (tail : ℕ) :
    (tailTableauPolynomial tail).natDegree ≤ tail := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro exponent hexponent
  unfold tailTableauPolynomial
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro exact hexact
  simp only [Finset.mem_range] at hexact
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt
      (exactTailPolynomial_natDegree_le exact) (by omega))

theorem tailTableauPolynomial_coeff_top (tail : ℕ) :
    (tailTableauPolynomial tail).coeff tail =
      (involutionNumber tail : ℚ) / tail.factorial := by
  unfold tailTableauPolynomial
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single tail]
  · exact exactTailPolynomial_coeff_top tail
  · intro exact hexact hne
    simp only [Finset.mem_range] at hexact
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (exactTailPolynomial_natDegree_le exact) (by omega))
  · simp

end FibonacciRibbonKernel
