import FibonacciRibbonKernel.RSKConsequences
import KostkaNumbers.Kostka.HorizontalAndHook
import FibonacciRibbonKernel.SmallTailKostka

namespace FibonacciRibbonKernel

open scoped Classical

def TailTableauCarrier (tailBound size : ℕ) :=
  {tableau : StandardRowWordTableau size size //
    size - tableau.shape.firstRow ≤ tailBound}

noncomputable instance tailTableauCarrierFintype (tailBound size : ℕ) :
    Fintype (TailTableauCarrier tailBound size) :=
  classicalSubtypeFintype _

noncomputable def tailDefiningTableauEquiv
    (tailBound size : ℕ) :
    {tableau : StandardTableau size size //
      size - tableau.shape.firstRow ≤ tailBound} ≃
      TailTableauCarrier tailBound size where
  toFun tableau :=
    ⟨tableau.1.toBallotRowWord (dominant_zero size), by
      rw [StandardTableau.shape_toBallotRowWord]
      exact tableau.2⟩
  invFun tableau :=
    ⟨tableau.1.toDefiningPath size, by
      have hshape : StandardTableau.shape (tableau.1.toDefiningPath size) =
          tableau.1.shape := by
        apply Subtype.ext
        funext row
        apply Fin.ext
        simpa [StandardTableau.shape, StandardRowWordTableau.shape] using
          congrArg (fun word : List (Fin (size + 1)) => word.count row)
            (BallotRowWordFrom.toDefiningPath_rowWord tableau.1)
      rw [hshape]
      exact tableau.2⟩
  left_inv tableau := by
    apply Subtype.ext
    exact DefiningPathFrom.toBallotRowWord_toDefiningPath
      (dominant_zero size) tableau.1
  right_inv tableau := by
    apply Subtype.ext
    apply BallotRowWordFrom.ext
    exact BallotRowWordFrom.toDefiningPath_rowWord tableau.1

theorem tailTableauSum_eq_card (tailBound size : ℕ) :
    tailTableauSum tailBound size =
      Fintype.card (TailTableauCarrier tailBound size) := by
  classical
  let eligible : Finset (StandardTableau size size) :=
    Finset.univ.filter fun tableau =>
      size - tableau.shape.firstRow ≤ tailBound
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (s := eligible)
    (t := (Finset.univ : Finset (BoundedPartition size size)))
    (f := StandardTableau.shape)
    (by intro tableau htableau; exact Finset.mem_univ _)
  unfold tailTableauSum standardTableauNumber
  calc
    (∑ shape : BoundedPartition size size,
        if size - shape.firstRow ≤ tailBound then
          Fintype.card {tableau : StandardTableau size size // tableau.shape = shape}
        else 0) = eligible.card := by
      rw [hfiber]
      apply Finset.sum_congr rfl
      intro shape hshape
      by_cases heligible : size - shape.firstRow ≤ tailBound
      · rw [if_pos heligible]
        rw [Fintype.card_subtype]
        apply congrArg Finset.card
        ext tableau
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, eligible]
        constructor
        · intro hshapeEq
          exact ⟨by rw [hshapeEq]; exact heligible, hshapeEq⟩
        · rintro ⟨_, hshapeEq⟩
          exact hshapeEq
      · rw [if_neg heligible]
        symm
        rw [Finset.card_eq_zero]
        ext tableau
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, eligible]
        constructor
        · rintro ⟨htableau, hshapeEq⟩
          exfalso
          apply heligible
          rw [← hshapeEq]
          exact htableau
        · intro hmem
          simp at hmem
    _ = Fintype.card
          {tableau : StandardTableau size size //
            size - tableau.shape.firstRow ≤ tailBound} := by
      rw [Fintype.card_subtype]
    _ = Fintype.card (TailTableauCarrier tailBound size) :=
      Fintype.card_congr (tailDefiningTableauEquiv tailBound size)

noncomputable def allZeroTableau (size : ℕ) :
    StandardRowWordTableau size size where
  word := List.replicate size 0
  length_eq := List.length_replicate
  ballot := by
    intro initial hinitial
    rw [runPlusWord_eq_add_wordWeight]
    intro row
    simp only [Pi.add_apply, Pi.zero_apply, zero_add, wordWeight_apply]
    have hall : ∀ letter ∈ initial, letter = (0 : Fin (size + 1)) := by
      intro letter hletter
      have hmem : letter ∈ List.replicate size (0 : Fin (size + 1)) :=
        List.IsPrefix.subset hinitial hletter
      exact (List.mem_replicate.mp hmem).2
    have hsucc : initial.count row.succ = 0 := by
      rw [List.count_eq_zero]
      intro hmem
      have := hall row.succ hmem
      have hvalue := congrArg Fin.val this
      simp at hvalue
    rw [hsucc]
    omega

theorem TailTableauCarrier.zero_unique
    (size : ℕ) (tableau : TailTableauCarrier 0 size) :
    tableau.1 = allZeroTableau size := by
  apply BallotRowWordFrom.ext
  have hcountLe := List.count_le_length
    (a := (0 : Fin (size + 1))) (l := tableau.1.word)
  rw [tableau.1.length_eq] at hcountLe
  have htail := tableau.2
  unfold BoundedPartition.firstRow StandardRowWordTableau.shape at htail
  simp only at htail
  have hcount : tableau.1.word.count (0 : Fin (size + 1)) = size := by omega
  have hall : ∀ letter ∈ tableau.1.word, letter = (0 : Fin (size + 1)) := by
    intro letter hletter
    by_contra hne
    have hlt := (List.count_lt_length_iff
      (l := tableau.1.word) (a := (0 : Fin (size + 1)))).2
      ⟨letter, hletter, hne⟩
    rw [tableau.1.length_eq, hcount] at hlt
    omega
  rw [List.eq_replicate_length.mpr hall, tableau.1.length_eq]
  rfl

noncomputable instance tailTableauCarrierZeroUnique (size : ℕ) :
    Unique (TailTableauCarrier 0 size) where
  default := ⟨allZeroTableau size, by
    unfold BoundedPartition.firstRow StandardRowWordTableau.shape
    simp [allZeroTableau]⟩
  uniq tableau := by
    apply Subtype.ext
    exact TailTableauCarrier.zero_unique size tableau

theorem tailTableauSum_zero (size : ℕ) :
    tailTableauSum 0 size = 1 := by
  rw [tailTableauSum_eq_card]
  exact Fintype.card_unique

theorem first_near_stable_strip
    (size : ℕ) (hsize : 3 ≤ size) :
    (stableActualInvolutionNumber size : ℤ) -
      (ribbonCount (size - 2) size : ℤ) = 1 := by
  have hdefect := stableActualInvolutionNumber_sub_ribbonCount_tail
    1 size (by omega)
  norm_num [Finset.sum_range_succ, tailTableauSum_zero] at hdefect ⊢
  exact hdefect

noncomputable def horizontalBoundedShape (size : ℕ) :
    BoundedPartition size size :=
  diagramBoundedPartition (YoungDiagram.horizontalDiagram size) size size
    YoungDiagram.horizontalDiagram_card
    (by
      have h := FibonacciRibbonKernel.YoungDiagram.colLen_zero_le_card
        (YoungDiagram.horizontalDiagram size)
      rw [YoungDiagram.horizontalDiagram_card] at h
      omega)

noncomputable def hookBoundedShape (size : ℕ) :
    BoundedPartition size size :=
  diagramBoundedPartition (YoungDiagram.hookDiagram size) size size
    (YoungDiagram.hookDiagram_card size)
    (by
      have h := FibonacciRibbonKernel.YoungDiagram.colLen_zero_le_card
        (YoungDiagram.hookDiagram size)
      rw [YoungDiagram.hookDiagram_card] at h
      omega)

@[simp] theorem horizontalBoundedShape_diagram (size : ℕ) :
    (horizontalBoundedShape size).youngDiagram =
      YoungDiagram.horizontalDiagram size := by
  unfold horizontalBoundedShape
  rw [diagramBoundedPartition_youngDiagram]

@[simp] theorem hookBoundedShape_diagram (size : ℕ) :
    (hookBoundedShape size).youngDiagram = YoungDiagram.hookDiagram size := by
  unfold hookBoundedShape
  rw [diagramBoundedPartition_youngDiagram]

theorem horizontalBoundedShape_standardNumber
    (size : ℕ) : standardTableauNumber (horizontalBoundedShape size) = 1 := by
  rw [standardTableauNumber_eq_kostka_replicate_one,
    horizontalBoundedShape_diagram]
  apply (kostka_horizontal' size (Multiset.replicate size 1)).2
  simp

theorem hookBoundedShape_standardNumber
    (size : ℕ) (hsize : 2 ≤ size) :
    standardTableauNumber (hookBoundedShape size) = size - 1 := by
  rw [standardTableauNumber_eq_kostka_replicate_one,
    hookBoundedShape_diagram]
  exact kostka_hook_replicate size hsize

theorem YoungDiagram.rowLen_zero_eq_of_rowLens_eq_cons
    (diagram : YoungDiagram) (first : ℕ) (remaining : List ℕ)
    (hrows : diagram.rowLens = first :: remaining) :
    diagram.rowLen 0 = first := by
  have hlength : 0 < diagram.colLen 0 := by
    rw [← YoungDiagram.length_rowLens, hrows]
    simp
  have hhead := congrArg List.head? hrows
  rw [YoungDiagram.rowLens, List.head?_map, List.head?_range,
    if_neg (by omega)] at hhead
  simpa using hhead

theorem eligible_one_tail_shape_classification
    (size : ℕ) (hsize : 2 ≤ size) (shape : BoundedPartition size size)
    (heligible : size - shape.firstRow ≤ 1) :
    shape = horizontalBoundedShape size ∨ shape = hookBoundedShape size := by
  let rows := shape.youngDiagram.rowLens
  have hsum : rows.sum = size := by
    rw [← YoungDiagram.card_eq_sum_rowLens, shape.youngDiagram_card]
  have hfirstLe : shape.firstRow ≤ size := by
    unfold BoundedPartition.firstRow
    have := (shape.1 0).isLt
    omega
  have hfirstLower : size - 1 ≤ shape.firstRow := by omega
  have hrowZero : shape.youngDiagram.rowLen 0 = shape.firstRow := by
    exact shape.youngDiagram_rowLen 0
  cases hrows : rows with
  | nil =>
      simp [rows, hrows] at hsum
      omega
  | cons first remaining =>
      have hfirst : first = shape.firstRow := by
        have hrows' : shape.youngDiagram.rowLens = first :: remaining := by
          exact hrows
        exact (FibonacciRibbonKernel.YoungDiagram.rowLen_zero_eq_of_rowLens_eq_cons
          shape.youngDiagram first remaining hrows').symm.trans hrowZero
      have hremainingSum : first + remaining.sum = size := by
        simpa [rows, hrows] using hsum
      have hremainingPositive : ∀ value ∈ remaining, 0 < value := by
        intro value hvalue
        exact shape.youngDiagram.pos_of_mem_rowLens value (by
          rw [show shape.youngDiagram.rowLens = rows by rfl, hrows]
          simp [hvalue])
      have remaining_eq_nil_of_sum_zero
          (hsumZero : remaining.sum = 0) : remaining = [] := by
        cases remaining with
        | nil => rfl
        | cons value tail =>
            have hpos := hremainingPositive value (by simp)
            simp at hsumZero
            omega
      rcases (show shape.firstRow = size ∨ shape.firstRow = size - 1 by omega) with
        hhorizontal | hhook
      · left
        apply BoundedPartition.eq_of_youngDiagram_eq
        rw [horizontalBoundedShape_diagram]
        apply (YoungDiagram.eq_iff_rowLens_eq).2
        rw [show shape.youngDiagram.rowLens = rows by rfl, hrows,
          YoungDiagram.horizontalDiagram_rowLens (by omega), hfirst,
          hhorizontal]
        have hzero : remaining.sum = 0 := by omega
        rw [remaining_eq_nil_of_sum_zero hzero]
      · right
        apply BoundedPartition.eq_of_youngDiagram_eq
        rw [hookBoundedShape_diagram]
        apply (YoungDiagram.eq_iff_rowLens_eq).2
        rw [show shape.youngDiagram.rowLens = rows by rfl, hrows,
          YoungDiagram.hookDiagram_rowLens hsize, hfirst, hhook]
        have hone : remaining.sum = 1 := by omega
        cases remaining with
        | nil => simp at hone
        | cons value tail =>
            have hpos := hremainingPositive value (by simp)
            have htailZero : tail.sum = 0 := by simp at hone; omega
            have htail : tail = [] := by
              cases tail with
              | nil => rfl
              | cons next rest =>
                  have hnext := hremainingPositive next (by simp)
                  simp at htailZero
                  omega
            simp [htail] at hone ⊢
            omega

theorem horizontal_ne_hookBoundedShape (size : ℕ) (hsize : 2 ≤ size) :
    horizontalBoundedShape size ≠ hookBoundedShape size := by
  intro heq
  have hdiagram := congrArg BoundedPartition.youngDiagram heq
  rw [horizontalBoundedShape_diagram, hookBoundedShape_diagram,
    YoungDiagram.eq_iff_rowLens_eq,
    YoungDiagram.horizontalDiagram_rowLens (by omega),
    YoungDiagram.hookDiagram_rowLens hsize] at hdiagram
  simp at hdiagram

theorem tailTableauSum_one (size : ℕ) (hsize : 2 ≤ size) :
    tailTableauSum 1 size = size := by
  unfold tailTableauSum
  let contribution : BoundedPartition size size → ℕ := fun shape =>
    if size - shape.firstRow ≤ 1 then standardTableauNumber shape else 0
  have hhorizontalMem : horizontalBoundedShape size ∈
      (Finset.univ : Finset (BoundedPartition size size)) := Finset.mem_univ _
  have hne := horizontal_ne_hookBoundedShape size hsize
  have hhookMem : hookBoundedShape size ∈
      (Finset.univ : Finset (BoundedPartition size size)).erase
        (horizontalBoundedShape size) := by simp [Ne.symm hne]
  have hrest :
      ∑ shape ∈ ((Finset.univ : Finset (BoundedPartition size size)).erase
          (horizontalBoundedShape size)).erase (hookBoundedShape size),
        contribution shape = 0 := by
    apply Finset.sum_eq_zero
    intro shape hshape
    simp only [Finset.mem_erase] at hshape
    unfold contribution
    by_cases heligible : size - shape.firstRow ≤ 1
    · have hclass := eligible_one_tail_shape_classification size hsize shape heligible
      rcases hclass with hhorizontal | hhook
      · exact (hshape.2.1 hhorizontal).elim
      · exact (hshape.1 hhook).elim
    · rw [if_neg heligible]
  rw [← Finset.sum_erase_add _ contribution hhorizontalMem,
    ← Finset.sum_erase_add _ contribution hhookMem, hrest]
  unfold contribution
  have hhorizontalFirst : (horizontalBoundedShape size).firstRow = size := by
    unfold BoundedPartition.firstRow
    have hshape := (horizontalBoundedShape size).youngDiagram_rowLen 0
    rw [horizontalBoundedShape_diagram] at hshape
    change (YoungDiagram.horizontalDiagram size).rowLen 0 =
      ((horizontalBoundedShape size).1 0).val at hshape
    have hr0 := FibonacciRibbonKernel.YoungDiagram.rowLen_zero_eq_of_rowLens_eq_cons
      (YoungDiagram.horizontalDiagram size) size []
      (YoungDiagram.horizontalDiagram_rowLens (by omega))
    exact hshape.symm.trans hr0
  have hhookFirst : (hookBoundedShape size).firstRow = size - 1 := by
    unfold BoundedPartition.firstRow
    have hshape := (hookBoundedShape size).youngDiagram_rowLen 0
    rw [hookBoundedShape_diagram] at hshape
    change (YoungDiagram.hookDiagram size).rowLen 0 =
      ((hookBoundedShape size).1 0).val at hshape
    have hr0 := FibonacciRibbonKernel.YoungDiagram.rowLen_zero_eq_of_rowLens_eq_cons
      (YoungDiagram.hookDiagram size) (size - 1) [1]
      (YoungDiagram.hookDiagram_rowLens hsize)
    exact hshape.symm.trans hr0
  have hhorizontalEligible : size - (horizontalBoundedShape size).firstRow ≤ 1 := by
    rw [hhorizontalFirst]
    omega
  have hhookEligible : size - (hookBoundedShape size).firstRow ≤ 1 := by
    rw [hhookFirst]
    omega
  rw [if_pos hhorizontalEligible, if_pos hhookEligible,
    horizontalBoundedShape_standardNumber,
    hookBoundedShape_standardNumber size hsize]
  omega

theorem second_near_stable_strip
    (size : ℕ) (hsize : 4 ≤ size) :
    (stableActualInvolutionNumber size : ℤ) -
      (ribbonCount (size - 3) size : ℤ) = size := by
  have hdefect := stableActualInvolutionNumber_sub_ribbonCount_tail
    2 size (by omega)
  norm_num [Finset.sum_range_succ, tailTableauSum_one size (by omega)] at hdefect ⊢
  exact hdefect

noncomputable def twoTailRowBoundedShape (size : ℕ) (hsize : 4 ≤ size) :
    BoundedPartition size size :=
  diagramBoundedPartition (twoTailRowDiagram size hsize) size size
    (twoTailRowDiagram_card size hsize)
    (by
      have h := FibonacciRibbonKernel.YoungDiagram.colLen_zero_le_card
        (twoTailRowDiagram size hsize)
      rw [twoTailRowDiagram_card] at h
      omega)

noncomputable def twoTailColumnBoundedShape (size : ℕ) (hsize : 4 ≤ size) :
    BoundedPartition size size :=
  diagramBoundedPartition (twoTailColumnDiagram size hsize) size size
    (twoTailColumnDiagram_card size hsize)
    (by
      have h := FibonacciRibbonKernel.YoungDiagram.colLen_zero_le_card
        (twoTailColumnDiagram size hsize)
      rw [twoTailColumnDiagram_card] at h
      omega)

@[simp] theorem twoTailRowBoundedShape_diagram
    (size : ℕ) (hsize : 4 ≤ size) :
    (twoTailRowBoundedShape size hsize).youngDiagram =
      twoTailRowDiagram size hsize := by
  unfold twoTailRowBoundedShape
  rw [diagramBoundedPartition_youngDiagram]

@[simp] theorem twoTailColumnBoundedShape_diagram
    (size : ℕ) (hsize : 4 ≤ size) :
    (twoTailColumnBoundedShape size hsize).youngDiagram =
      twoTailColumnDiagram size hsize := by
  unfold twoTailColumnBoundedShape
  rw [diagramBoundedPartition_youngDiagram]

theorem twoTailRowBoundedShape_standardNumber_double
    (size : ℕ) (hsize : 4 ≤ size) :
    2 * standardTableauNumber (twoTailRowBoundedShape size hsize) =
      size * (size - 3) := by
  rw [standardTableauNumber_eq_kostka_replicate_one,
    twoTailRowBoundedShape_diagram]
  exact twoTailRowDiagram_kostka_double size hsize

theorem twoTailColumnBoundedShape_standardNumber_double
    (size : ℕ) (hsize : 4 ≤ size) :
    2 * standardTableauNumber (twoTailColumnBoundedShape size hsize) =
      (size - 1) * (size - 2) := by
  rw [standardTableauNumber_eq_kostka_replicate_one,
    twoTailColumnBoundedShape_diagram]
  exact twoTailColumnDiagram_kostka_double size hsize

theorem positiveList_sum_two_classification
    (values : List ℕ) (hpositive : ∀ value ∈ values, 0 < value)
    (hsum : values.sum = 2) :
    values = [2] ∨ values = [1, 1] := by
  cases values with
  | nil => simp at hsum
  | cons first remaining =>
      have hfirst := hpositive first (by simp)
      have hremaining : first + remaining.sum = 2 := by simpa using hsum
      by_cases hfirstTwo : first = 2
      · left
        subst first
        have hzero : remaining.sum = 0 := by omega
        have hempty : remaining = [] := by
          cases remaining with
          | nil => rfl
          | cons next tail =>
              have hnext := hpositive next (by simp)
              simp at hzero
              omega
        rw [hempty]
      · have hfirstOne : first = 1 := by omega
        right
        subst first
        have hone : remaining.sum = 1 := by omega
        cases remaining with
        | nil => simp at hone
        | cons second tail =>
            have hsecond := hpositive second (by simp)
            have htailZero : tail.sum = 0 := by simp at hone; omega
            have htail : tail = [] := by
              cases tail with
              | nil => rfl
              | cons next rest =>
                  have hnext := hpositive next (by simp)
                  simp at htailZero
                  omega
            simp [htail] at hone ⊢
            omega

theorem eligible_two_tail_shape_classification
    (size : ℕ) (hsize : 4 ≤ size) (shape : BoundedPartition size size)
    (heligible : size - shape.firstRow ≤ 2) :
    shape = horizontalBoundedShape size ∨
      shape = hookBoundedShape size ∨
      shape = twoTailRowBoundedShape size hsize ∨
      shape = twoTailColumnBoundedShape size hsize := by
  by_cases hone : size - shape.firstRow ≤ 1
  · rcases eligible_one_tail_shape_classification size (by omega) shape hone with
      hhorizontal | hhook
    · exact Or.inl hhorizontal
    · exact Or.inr (Or.inl hhook)
  · have hfirstLe : shape.firstRow ≤ size := by
      unfold BoundedPartition.firstRow
      have := (shape.1 0).isLt
      omega
    have hfirst : shape.firstRow = size - 2 := by omega
    let rows := shape.youngDiagram.rowLens
    have hsum : rows.sum = size := by
      rw [← YoungDiagram.card_eq_sum_rowLens, shape.youngDiagram_card]
    cases hrows : rows with
    | nil => simp [rows, hrows] at hsum; omega
    | cons first remaining =>
        have hrows' : shape.youngDiagram.rowLens = first :: remaining := hrows
        have hfirstEq : first = shape.firstRow :=
          (FibonacciRibbonKernel.YoungDiagram.rowLen_zero_eq_of_rowLens_eq_cons
            shape.youngDiagram first remaining hrows').symm.trans
              (shape.youngDiagram_rowLen 0)
        have hremainingSum : remaining.sum = 2 := by
          have : first + remaining.sum = size := by simpa [rows, hrows] using hsum
          omega
        have hremainingPositive : ∀ value ∈ remaining, 0 < value := by
          intro value hvalue
          exact shape.youngDiagram.pos_of_mem_rowLens value (by
            rw [hrows']
            simp [hvalue])
        rcases positiveList_sum_two_classification remaining
          hremainingPositive hremainingSum with htwo | hones
        · exact Or.inr (Or.inr (Or.inl (by
            apply BoundedPartition.eq_of_youngDiagram_eq
            rw [twoTailRowBoundedShape_diagram]
            apply (YoungDiagram.eq_iff_rowLens_eq).2
            rw [hrows', htwo, hfirstEq, hfirst,
              twoTailRowDiagram_rowLens])))
        · exact Or.inr (Or.inr (Or.inr (by
            apply BoundedPartition.eq_of_youngDiagram_eq
            rw [twoTailColumnBoundedShape_diagram]
            apply (YoungDiagram.eq_iff_rowLens_eq).2
            rw [hrows', hones, hfirstEq, hfirst,
              twoTailColumnDiagram_rowLens])))

theorem horizontalBoundedShape_firstRow
    (size : ℕ) (hsize : 1 ≤ size) :
    (horizontalBoundedShape size).firstRow = size := by
  unfold BoundedPartition.firstRow
  have hshape := (horizontalBoundedShape size).youngDiagram_rowLen 0
  rw [horizontalBoundedShape_diagram] at hshape
  change (YoungDiagram.horizontalDiagram size).rowLen 0 =
    ((horizontalBoundedShape size).1 0).val at hshape
  have hr0 := FibonacciRibbonKernel.YoungDiagram.rowLen_zero_eq_of_rowLens_eq_cons
    (YoungDiagram.horizontalDiagram size) size []
    (YoungDiagram.horizontalDiagram_rowLens (by omega))
  exact hshape.symm.trans hr0

theorem hookBoundedShape_firstRow
    (size : ℕ) (hsize : 2 ≤ size) :
    (hookBoundedShape size).firstRow = size - 1 := by
  unfold BoundedPartition.firstRow
  have hshape := (hookBoundedShape size).youngDiagram_rowLen 0
  rw [hookBoundedShape_diagram] at hshape
  change (YoungDiagram.hookDiagram size).rowLen 0 =
    ((hookBoundedShape size).1 0).val at hshape
  have hr0 := FibonacciRibbonKernel.YoungDiagram.rowLen_zero_eq_of_rowLens_eq_cons
    (YoungDiagram.hookDiagram size) (size - 1) [1]
    (YoungDiagram.hookDiagram_rowLens hsize)
  exact hshape.symm.trans hr0

theorem twoTailRowBoundedShape_firstRow
    (size : ℕ) (hsize : 4 ≤ size) :
    (twoTailRowBoundedShape size hsize).firstRow = size - 2 := by
  unfold BoundedPartition.firstRow
  have hshape := (twoTailRowBoundedShape size hsize).youngDiagram_rowLen 0
  rw [twoTailRowBoundedShape_diagram,
    twoTailRowDiagram_rowLen] at hshape
  simpa using hshape.symm

theorem twoTailColumnBoundedShape_firstRow
    (size : ℕ) (hsize : 4 ≤ size) :
    (twoTailColumnBoundedShape size hsize).firstRow = size - 2 := by
  unfold BoundedPartition.firstRow
  have hshape := (twoTailColumnBoundedShape size hsize).youngDiagram_rowLen 0
  rw [twoTailColumnBoundedShape_diagram,
    twoTailColumnDiagram_rowLen] at hshape
  simpa using hshape.symm

theorem twoTailRow_ne_twoTailColumnBoundedShape
    (size : ℕ) (hsize : 4 ≤ size) :
    twoTailRowBoundedShape size hsize ≠ twoTailColumnBoundedShape size hsize := by
  intro heq
  have hdiagram := congrArg BoundedPartition.youngDiagram heq
  rw [twoTailRowBoundedShape_diagram,
    twoTailColumnBoundedShape_diagram,
    YoungDiagram.eq_iff_rowLens_eq,
    twoTailRowDiagram_rowLens,
    twoTailColumnDiagram_rowLens] at hdiagram
  simp at hdiagram

theorem tailTableauSum_two (size : ℕ) (hsize : 4 ≤ size) :
    tailTableauSum 2 size = (size - 1) ^ 2 := by
  let horizontal := horizontalBoundedShape size
  let hook := hookBoundedShape size
  let twoRow := twoTailRowBoundedShape size hsize
  let twoColumn := twoTailColumnBoundedShape size hsize
  let contribution : BoundedPartition size size → ℕ := fun shape =>
    if size - shape.firstRow ≤ 2 then standardTableauNumber shape else 0
  let selected : Finset (BoundedPartition size size) :=
    {horizontal, hook, twoRow, twoColumn}
  have hhorizontalHook : horizontal ≠ hook :=
    horizontal_ne_hookBoundedShape size (by omega)
  have hhorizontalRow : horizontal ≠ twoRow := by
    intro heq
    have hfirst := congrArg BoundedPartition.firstRow heq
    dsimp [horizontal, twoRow] at hfirst
    rw [horizontalBoundedShape_firstRow size (by omega),
      twoTailRowBoundedShape_firstRow] at hfirst
    omega
  have hhorizontalColumn : horizontal ≠ twoColumn := by
    intro heq
    have hfirst := congrArg BoundedPartition.firstRow heq
    dsimp [horizontal, twoColumn] at hfirst
    rw [horizontalBoundedShape_firstRow size (by omega),
      twoTailColumnBoundedShape_firstRow] at hfirst
    omega
  have hhookRow : hook ≠ twoRow := by
    intro heq
    have hfirst := congrArg BoundedPartition.firstRow heq
    dsimp [hook, twoRow] at hfirst
    rw [hookBoundedShape_firstRow size (by omega),
      twoTailRowBoundedShape_firstRow] at hfirst
    omega
  have hhookColumn : hook ≠ twoColumn := by
    intro heq
    have hfirst := congrArg BoundedPartition.firstRow heq
    dsimp [hook, twoColumn] at hfirst
    rw [hookBoundedShape_firstRow size (by omega),
      twoTailColumnBoundedShape_firstRow] at hfirst
    omega
  have hrowColumn : twoRow ≠ twoColumn :=
    twoTailRow_ne_twoTailColumnBoundedShape size hsize
  have hsum :
      ∑ shape ∈ selected, contribution shape =
        ∑ shape ∈ (Finset.univ : Finset (BoundedPartition size size)),
          contribution shape := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro shape hshape hnotSelected
    unfold contribution
    by_cases heligible : size - shape.firstRow ≤ 2
    · have hclass := eligible_two_tail_shape_classification
        size hsize shape heligible
      unfold selected horizontal hook twoRow twoColumn at hnotSelected
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnotSelected
      rcases hclass with hhorizontal | hhook | hrow | hcolumn
      · exact (hnotSelected.1 hhorizontal).elim
      · exact (hnotSelected.2.1 hhook).elim
      · exact (hnotSelected.2.2.1 hrow).elim
      · exact (hnotSelected.2.2.2 hcolumn).elim
    · rw [if_neg heligible]
  unfold tailTableauSum
  change (∑ shape ∈ (Finset.univ : Finset (BoundedPartition size size)),
    contribution shape) = (size - 1) ^ 2
  rw [← hsum]
  unfold selected
  rw [Finset.sum_insert (by simp [hhorizontalHook, hhorizontalRow,
      hhorizontalColumn]),
    Finset.sum_insert (by simp [hhookRow, hhookColumn]),
    Finset.sum_insert (by simp [hrowColumn]), Finset.sum_singleton]
  unfold contribution horizontal hook twoRow twoColumn
  rw [if_pos (by rw [horizontalBoundedShape_firstRow size (by omega)]; omega),
    if_pos (by rw [hookBoundedShape_firstRow size (by omega)]; omega),
    if_pos (by rw [twoTailRowBoundedShape_firstRow]; omega),
    if_pos (by rw [twoTailColumnBoundedShape_firstRow]; omega),
    horizontalBoundedShape_standardNumber,
    hookBoundedShape_standardNumber size (by omega)]
  let rowNumber := standardTableauNumber (twoTailRowBoundedShape size hsize)
  let columnNumber := standardTableauNumber (twoTailColumnBoundedShape size hsize)
  have hrowNumber : 2 * rowNumber = size * (size - 3) :=
    twoTailRowBoundedShape_standardNumber_double size hsize
  have hcolumnNumber : 2 * columnNumber = (size - 1) * (size - 2) :=
    twoTailColumnBoundedShape_standardNumber_double size hsize
  have hpure : 2 + 2 * (size - 1) + size * (size - 3) +
      (size - 1) * (size - 2) = 2 * ((size - 1) ^ 2) := by
    let offset := size - 4
    have hsizeEq : size = offset + 4 := by
      dsimp [offset]
      omega
    rw [hsizeEq]
    simp
    ring
  change 1 + ((size - 1) + (rowNumber + columnNumber)) = (size - 1) ^ 2
  apply Nat.mul_left_cancel (n := 2) (by omega)
  calc
    2 * (1 + ((size - 1) + (rowNumber + columnNumber))) =
        2 + 2 * (size - 1) + 2 * rowNumber + 2 * columnNumber := by ring
    _ = 2 + 2 * (size - 1) + size * (size - 3) +
        (size - 1) * (size - 2) := by rw [hrowNumber, hcolumnNumber]
    _ = 2 * ((size - 1) ^ 2) := hpure

theorem third_near_stable_strip
    (size : ℕ) (hsize : 5 ≤ size) :
    (stableActualInvolutionNumber size : ℤ) -
      (ribbonCount (size - 4) size : ℤ) = (size - 1) * (size - 2) := by
  have hdefect := stableActualInvolutionNumber_sub_ribbonCount_tail
    3 size (by omega)
  norm_num [Finset.sum_range_succ, tailTableauSum_two size (by omega),
    tailTableauSum_zero] at hdefect
  have hindex : size - 3 - 1 = size - 4 := by omega
  rw [hindex] at hdefect
  have hcast : ((size - 1 : ℕ) : ℤ) = (size : ℤ) - 1 := by
    rw [Nat.cast_sub (R := ℤ) (by omega : 1 ≤ size)]
    norm_num
  rw [hcast] at hdefect
  calc
    (stableActualInvolutionNumber size : ℤ) -
        (ribbonCount (size - 4) size : ℤ) =
      ((size : ℤ) - 1) ^ 2 - ((size : ℤ) - 1) := by
        simpa [sub_eq_add_neg] using hdefect
    _ = ((size : ℤ) - 1) * ((size : ℤ) - 2) := by ring

noncomputable def exactTailTableauSum (tail size : ℕ) : ℕ :=
  ∑ shape : BoundedPartition size size,
    if size - shape.firstRow = tail then standardTableauNumber shape else 0

theorem tailTableauSum_succ_split (tail size : ℕ) :
    tailTableauSum (tail + 1) size =
      tailTableauSum tail size + exactTailTableauSum (tail + 1) size := by
  unfold tailTableauSum exactTailTableauSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro shape hshape
  by_cases hle : size - shape.firstRow ≤ tail
  · have hleSucc : size - shape.firstRow ≤ tail + 1 := by omega
    have hne : size - shape.firstRow ≠ tail + 1 := by omega
    rw [if_pos hleSucc, if_pos hle, if_neg hne]
    omega
  · by_cases heq : size - shape.firstRow = tail + 1
    · have hleSucc : size - shape.firstRow ≤ tail + 1 := heq.le
      rw [if_pos hleSucc, if_neg hle, if_pos heq]
      omega
    · have hnotSucc : ¬size - shape.firstRow ≤ tail + 1 := by omega
      rw [if_neg hnotSucc, if_neg hle, if_neg heq]

noncomputable def threeTailRowBoundedShape (size : ℕ) (hsize : 6 ≤ size) :
    BoundedPartition size size :=
  diagramBoundedPartition (threeTailRowDiagram size hsize) size size
    (threeTailRowDiagram_card size hsize)
    (by
      have h := FibonacciRibbonKernel.YoungDiagram.colLen_zero_le_card
        (threeTailRowDiagram size hsize)
      rw [threeTailRowDiagram_card] at h
      omega)

noncomputable def threeTailMixedBoundedShape (size : ℕ) (hsize : 6 ≤ size) :
    BoundedPartition size size :=
  diagramBoundedPartition (threeTailMixedDiagram size hsize) size size
    (threeTailMixedDiagram_card size hsize)
    (by
      have h := FibonacciRibbonKernel.YoungDiagram.colLen_zero_le_card
        (threeTailMixedDiagram size hsize)
      rw [threeTailMixedDiagram_card] at h
      omega)

noncomputable def threeTailColumnBoundedShape (size : ℕ) (hsize : 6 ≤ size) :
    BoundedPartition size size :=
  diagramBoundedPartition (threeTailColumnDiagram size hsize) size size
    (threeTailColumnDiagram_card size hsize)
    (by
      have h := FibonacciRibbonKernel.YoungDiagram.colLen_zero_le_card
        (threeTailColumnDiagram size hsize)
      rw [threeTailColumnDiagram_card] at h
      omega)

@[simp] theorem threeTailRowBoundedShape_diagram
    (size : ℕ) (hsize : 6 ≤ size) :
    (threeTailRowBoundedShape size hsize).youngDiagram =
      threeTailRowDiagram size hsize := by
  unfold threeTailRowBoundedShape
  rw [diagramBoundedPartition_youngDiagram]

@[simp] theorem threeTailMixedBoundedShape_diagram
    (size : ℕ) (hsize : 6 ≤ size) :
    (threeTailMixedBoundedShape size hsize).youngDiagram =
      threeTailMixedDiagram size hsize := by
  unfold threeTailMixedBoundedShape
  rw [diagramBoundedPartition_youngDiagram]

@[simp] theorem threeTailColumnBoundedShape_diagram
    (size : ℕ) (hsize : 6 ≤ size) :
    (threeTailColumnBoundedShape size hsize).youngDiagram =
      threeTailColumnDiagram size hsize := by
  unfold threeTailColumnBoundedShape
  rw [diagramBoundedPartition_youngDiagram]

theorem threeTailRowBoundedShape_firstRow
    (size : ℕ) (hsize : 6 ≤ size) :
    (threeTailRowBoundedShape size hsize).firstRow = size - 3 := by
  unfold BoundedPartition.firstRow
  have hshape := (threeTailRowBoundedShape size hsize).youngDiagram_rowLen 0
  rw [threeTailRowBoundedShape_diagram, threeTailRowDiagram_rowLen] at hshape
  simpa using hshape.symm

theorem threeTailMixedBoundedShape_firstRow
    (size : ℕ) (hsize : 6 ≤ size) :
    (threeTailMixedBoundedShape size hsize).firstRow = size - 3 := by
  unfold BoundedPartition.firstRow
  have hshape := (threeTailMixedBoundedShape size hsize).youngDiagram_rowLen 0
  rw [threeTailMixedBoundedShape_diagram, threeTailMixedDiagram_rowLen] at hshape
  simpa using hshape.symm

theorem threeTailColumnBoundedShape_firstRow
    (size : ℕ) (hsize : 6 ≤ size) :
    (threeTailColumnBoundedShape size hsize).firstRow = size - 3 := by
  unfold BoundedPartition.firstRow
  have hshape := (threeTailColumnBoundedShape size hsize).youngDiagram_rowLen 0
  rw [threeTailColumnBoundedShape_diagram, threeTailColumnDiagram_rowLen] at hshape
  simpa using hshape.symm

theorem threeTailBoundedShape_standard_sum_triple
    (size : ℕ) (hsize : 6 ≤ size) :
    3 * (standardTableauNumber (threeTailRowBoundedShape size hsize) +
      standardTableauNumber (threeTailMixedBoundedShape size hsize) +
      standardTableauNumber (threeTailColumnBoundedShape size hsize)) =
      size * (size - 2) * (2 * size - 5) - 3 * (size - 1) ^ 2 := by
  rw [standardTableauNumber_eq_kostka_replicate_one,
    standardTableauNumber_eq_kostka_replicate_one,
    standardTableauNumber_eq_kostka_replicate_one,
    threeTailRowBoundedShape_diagram,
    threeTailMixedBoundedShape_diagram,
    threeTailColumnBoundedShape_diagram]
  exact threeTailNewKostkaSum_triple size hsize

theorem positiveSortedList_sum_three_classification
    (values : List ℕ) (hpositive : ∀ value ∈ values, 0 < value)
    (hsorted : values.SortedGE) (hsum : values.sum = 3) :
    values = [3] ∨ values = [2, 1] ∨ values = [1, 1, 1] := by
  cases values with
  | nil => simp at hsum
  | cons first remaining =>
      have hfirst := hpositive first (by simp)
      have hsum' : first + remaining.sum = 3 := by simpa using hsum
      have hpair := hsorted.pairwise
      simp only [List.pairwise_cons] at hpair
      by_cases hthree : first = 3
      · left
        subst first
        have hzero : remaining.sum = 0 := by omega
        have hempty : remaining = [] := by
          cases remaining with
          | nil => rfl
          | cons next tail =>
              have hnext := hpositive next (by simp)
              simp at hzero
              omega
        rw [hempty]
      · by_cases htwo : first = 2
        · right; left
          subst first
          have hone : remaining.sum = 1 := by omega
          cases remaining with
          | nil => simp at hone
          | cons second tail =>
              have hsecond := hpositive second (by simp)
              have htailZero : tail.sum = 0 := by simp at hone; omega
              have htail : tail = [] := by
                cases tail with
                | nil => rfl
                | cons next rest =>
                    have hnext := hpositive next (by simp)
                    simp at htailZero
                    omega
              simp [htail] at hone ⊢
              omega
        · have honeFirst : first = 1 := by omega
          right; right
          subst first
          have hremainingSum : remaining.sum = 2 := by omega
          cases remaining with
          | nil => simp at hremainingSum
          | cons second tail =>
              have hsecondPos := hpositive second (by simp)
              have hsecondLe : second ≤ 1 := hpair.1 second (by simp)
              have hsecond : second = 1 := by omega
              subst second
              have htailSum : tail.sum = 1 := by simp at hremainingSum; omega
              cases tail with
              | nil => simp at htailSum
              | cons third rest =>
                  have hthirdPos := hpositive third (by simp)
                  have hthirdLe : third ≤ 1 := hpair.1 third (by simp)
                  have hthird : third = 1 := by omega
                  subst third
                  have hrestZero : rest.sum = 0 := by simp at htailSum; omega
                  have hrest : rest = [] := by
                    cases rest with
                    | nil => rfl
                    | cons next more =>
                        have hnext := hpositive next (by simp)
                        simp at hrestZero
                        omega
                  rw [hrest]

theorem exact_three_tail_shape_classification
    (size : ℕ) (hsize : 6 ≤ size) (shape : BoundedPartition size size)
    (hexact : size - shape.firstRow = 3) :
    shape = threeTailRowBoundedShape size hsize ∨
      shape = threeTailMixedBoundedShape size hsize ∨
      shape = threeTailColumnBoundedShape size hsize := by
  have hfirstLe : shape.firstRow ≤ size := by
    unfold BoundedPartition.firstRow
    have := (shape.1 0).isLt
    omega
  have hfirst : shape.firstRow = size - 3 := by omega
  let rows := shape.youngDiagram.rowLens
  have hsum : rows.sum = size := by
    rw [← YoungDiagram.card_eq_sum_rowLens, shape.youngDiagram_card]
  cases hrows : rows with
  | nil => simp [rows, hrows] at hsum; omega
  | cons first remaining =>
      have hrows' : shape.youngDiagram.rowLens = first :: remaining := hrows
      have hfirstEq : first = shape.firstRow :=
        (FibonacciRibbonKernel.YoungDiagram.rowLen_zero_eq_of_rowLens_eq_cons
          shape.youngDiagram first remaining hrows').symm.trans
            (shape.youngDiagram_rowLen 0)
      have hremainingSum : remaining.sum = 3 := by
        have : first + remaining.sum = size := by simpa [rows, hrows] using hsum
        omega
      have hremainingPositive : ∀ value ∈ remaining, 0 < value := by
        intro value hvalue
        exact shape.youngDiagram.pos_of_mem_rowLens value (by
          rw [hrows']
          simp [hvalue])
      have hremainingSorted : remaining.SortedGE := by
        have hsorted := shape.youngDiagram.rowLens_sorted
        rw [hrows'] at hsorted
        have hpair := hsorted.pairwise
        rw [List.pairwise_cons] at hpair
        exact hpair.2.sortedGE
      rcases positiveSortedList_sum_three_classification remaining
        hremainingPositive hremainingSorted hremainingSum with
        hthree | hmixed | hcolumn
      · left
        apply BoundedPartition.eq_of_youngDiagram_eq
        rw [threeTailRowBoundedShape_diagram]
        apply (YoungDiagram.eq_iff_rowLens_eq).2
        rw [hrows', hthree, hfirstEq, hfirst, threeTailRowDiagram_rowLens]
      · right; left
        apply BoundedPartition.eq_of_youngDiagram_eq
        rw [threeTailMixedBoundedShape_diagram]
        apply (YoungDiagram.eq_iff_rowLens_eq).2
        rw [hrows', hmixed, hfirstEq, hfirst, threeTailMixedDiagram_rowLens]
      · right; right
        apply BoundedPartition.eq_of_youngDiagram_eq
        rw [threeTailColumnBoundedShape_diagram]
        apply (YoungDiagram.eq_iff_rowLens_eq).2
        rw [hrows', hcolumn, hfirstEq, hfirst, threeTailColumnDiagram_rowLens]

theorem threeTailRow_ne_threeTailMixedBoundedShape
    (size : ℕ) (hsize : 6 ≤ size) :
    threeTailRowBoundedShape size hsize ≠
      threeTailMixedBoundedShape size hsize := by
  intro heq
  have hdiagram := congrArg BoundedPartition.youngDiagram heq
  rw [threeTailRowBoundedShape_diagram, threeTailMixedBoundedShape_diagram,
    YoungDiagram.eq_iff_rowLens_eq, threeTailRowDiagram_rowLens,
    threeTailMixedDiagram_rowLens] at hdiagram
  simp at hdiagram

theorem threeTailRow_ne_threeTailColumnBoundedShape
    (size : ℕ) (hsize : 6 ≤ size) :
    threeTailRowBoundedShape size hsize ≠
      threeTailColumnBoundedShape size hsize := by
  intro heq
  have hdiagram := congrArg BoundedPartition.youngDiagram heq
  rw [threeTailRowBoundedShape_diagram, threeTailColumnBoundedShape_diagram,
    YoungDiagram.eq_iff_rowLens_eq, threeTailRowDiagram_rowLens,
    threeTailColumnDiagram_rowLens] at hdiagram
  simp at hdiagram

theorem threeTailMixed_ne_threeTailColumnBoundedShape
    (size : ℕ) (hsize : 6 ≤ size) :
    threeTailMixedBoundedShape size hsize ≠
      threeTailColumnBoundedShape size hsize := by
  intro heq
  have hdiagram := congrArg BoundedPartition.youngDiagram heq
  rw [threeTailMixedBoundedShape_diagram, threeTailColumnBoundedShape_diagram,
    YoungDiagram.eq_iff_rowLens_eq, threeTailMixedDiagram_rowLens,
    threeTailColumnDiagram_rowLens] at hdiagram
  simp at hdiagram

theorem exactTailTableauSum_three_triple
    (size : ℕ) (hsize : 6 ≤ size) :
    3 * exactTailTableauSum 3 size =
      size * (size - 2) * (2 * size - 5) - 3 * (size - 1) ^ 2 := by
  let rowShape := threeTailRowBoundedShape size hsize
  let mixedShape := threeTailMixedBoundedShape size hsize
  let columnShape := threeTailColumnBoundedShape size hsize
  let contribution : BoundedPartition size size → ℕ := fun shape =>
    if size - shape.firstRow = 3 then standardTableauNumber shape else 0
  let selected : Finset (BoundedPartition size size) :=
    {rowShape, mixedShape, columnShape}
  have hrowMixed : rowShape ≠ mixedShape :=
    threeTailRow_ne_threeTailMixedBoundedShape size hsize
  have hrowColumn : rowShape ≠ columnShape :=
    threeTailRow_ne_threeTailColumnBoundedShape size hsize
  have hmixedColumn : mixedShape ≠ columnShape :=
    threeTailMixed_ne_threeTailColumnBoundedShape size hsize
  have hsum :
      ∑ shape ∈ selected, contribution shape =
        ∑ shape ∈ (Finset.univ : Finset (BoundedPartition size size)),
          contribution shape := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro shape hshape hnotSelected
    unfold contribution
    by_cases hexact : size - shape.firstRow = 3
    · have hclass := exact_three_tail_shape_classification
        size hsize shape hexact
      unfold selected rowShape mixedShape columnShape at hnotSelected
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnotSelected
      rcases hclass with hrow | hmixed | hcolumn
      · exact (hnotSelected.1 hrow).elim
      · exact (hnotSelected.2.1 hmixed).elim
      · exact (hnotSelected.2.2 hcolumn).elim
    · rw [if_neg hexact]
  unfold exactTailTableauSum
  change 3 * (∑ shape ∈ (Finset.univ : Finset (BoundedPartition size size)),
    contribution shape) = _
  rw [← hsum]
  unfold selected
  rw [Finset.sum_insert (by simp [hrowMixed, hrowColumn]),
    Finset.sum_insert (by simp [hmixedColumn]), Finset.sum_singleton]
  unfold contribution rowShape mixedShape columnShape
  rw [if_pos (by rw [threeTailRowBoundedShape_firstRow]; omega),
    if_pos (by rw [threeTailMixedBoundedShape_firstRow]; omega),
    if_pos (by rw [threeTailColumnBoundedShape_firstRow]; omega)]
  simpa [add_assoc] using threeTailBoundedShape_standard_sum_triple size hsize

theorem tailTableauSum_three_triple
    (size : ℕ) (hsize : 6 ≤ size) :
    3 * tailTableauSum 3 size = size * (size - 2) * (2 * size - 5) := by
  have hsplit := tailTableauSum_succ_split 2 size
  have htwo := tailTableauSum_two size (by omega)
  have hthree := exactTailTableauSum_three_triple size hsize
  rw [show 2 + 1 = 3 by omega, htwo] at hsplit
  rw [hsplit]
  have hbound : 3 * (size - 1) ^ 2 ≤
      size * (size - 2) * (2 * size - 5) := by
    let offset := size - 6
    have hsizeEq : size = offset + 6 := by
      dsimp [offset]
      omega
    rw [hsizeEq]
    have hm1 : offset + 6 - 1 = offset + 5 := by omega
    have hm2 : offset + 6 - 2 = offset + 4 := by omega
    have hscale : 2 * (offset + 6) - 5 = 2 * offset + 7 := by omega
    rw [hm1, hm2, hscale]
    have heq :
        (offset + 6) * (offset + 4) * (2 * offset + 7) =
          3 * (offset + 5) ^ 2 +
            (2 * offset ^ 3 + 24 * offset ^ 2 + 88 * offset + 93) := by
      ring
    rw [heq]
    omega
  have hcancel := Nat.sub_add_cancel hbound
  calc
    3 * ((size - 1) ^ 2 + exactTailTableauSum 3 size) =
        3 * (size - 1) ^ 2 + 3 * exactTailTableauSum 3 size := by ring
    _ = 3 * (size - 1) ^ 2 +
        (size * (size - 2) * (2 * size - 5) - 3 * (size - 1) ^ 2) := by
      rw [hthree]
    _ = size * (size - 2) * (2 * size - 5) := by omega

theorem fourth_near_stable_strip_triple
    (size : ℕ) (hsize : 6 ≤ size) :
    3 * ((stableActualInvolutionNumber size : ℤ) -
      (ribbonCount (size - 5) size : ℤ)) =
        ((size : ℤ) - 2) *
          (2 * (size : ℤ) ^ 2 - 8 * (size : ℤ) + 3) := by
  have hdefect := stableActualInvolutionNumber_sub_ribbonCount_tail
    4 size (by omega)
  have hone := tailTableauSum_one (size - 2) (by omega)
  norm_num [Finset.sum_range_succ, hone] at hdefect
  have hindex : size - 4 - 1 = size - 5 := by omega
  rw [hindex] at hdefect
  have hthreeNat := tailTableauSum_three_triple size hsize
  have hthree :
      (3 : ℤ) * tailTableauSum 3 size =
        (size : ℤ) * (size - 2 : ℕ) * (2 * size - 5 : ℕ) := by
    exact_mod_cast hthreeNat
  have hsize1 : ((size - 1 : ℕ) : ℤ) = (size : ℤ) - 1 := by
    rw [Nat.cast_sub (R := ℤ) (by omega : 1 ≤ size)]
    norm_num
  have hsize2 : ((size - 2 : ℕ) : ℤ) = (size : ℤ) - 2 := by
    rw [Nat.cast_sub (R := ℤ) (by omega : 2 ≤ size)]
    norm_num
  have hscale : ((2 * size - 5 : ℕ) : ℤ) = 2 * (size : ℤ) - 5 := by
    rw [Nat.cast_sub (R := ℤ) (by omega : 5 ≤ 2 * size)]
    push_cast
    ring
  rw [hsize1, hsize2] at hdefect
  rw [hsize2, hscale] at hthree
  linear_combination 3 * hdefect + hthree

theorem fourth_near_stable_strip
    (size : ℕ) (hsize : 6 ≤ size) :
    ((stableActualInvolutionNumber size : ℚ) -
      (ribbonCount (size - 5) size : ℚ)) =
        (((size : ℚ) - 2) *
          (2 * (size : ℚ) ^ 2 - 8 * (size : ℚ) + 3)) / 3 := by
  have htriple := fourth_near_stable_strip_triple size hsize
  have htripleQ :
      (3 : ℚ) * ((stableActualInvolutionNumber size : ℚ) -
        (ribbonCount (size - 5) size : ℚ)) =
          ((size : ℚ) - 2) *
            (2 * (size : ℚ) ^ 2 - 8 * (size : ℚ) + 3) := by
    exact_mod_cast htriple
  linarith

end FibonacciRibbonKernel
