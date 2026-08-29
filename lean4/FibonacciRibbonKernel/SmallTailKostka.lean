import FibonacciRibbonKernel.KostkaCornerRecursion
import KostkaNumbers.Computation.HookLengthComputation
import KostkaNumbers.Kostka.HorizontalAndHook

namespace FibonacciRibbonKernel

open scoped Classical
open YoungDiagram Kostka

noncomputable def twoTailRowDiagram (size : ℕ) (hsize : 4 ≤ size) :
    YoungDiagram :=
  YoungDiagram.ofRowLens [size - 2, 2]
    (sorted_pair (by omega))

@[simp] theorem twoTailRowDiagram_rowLens
    (size : ℕ) (hsize : 4 ≤ size) :
    (twoTailRowDiagram size hsize).rowLens = [size - 2, 2] := by
  unfold twoTailRowDiagram
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  simp
  omega

@[simp] theorem twoTailRowDiagram_card
    (size : ℕ) (hsize : 4 ≤ size) :
    (twoTailRowDiagram size hsize).card = size := by
  calc
    (twoTailRowDiagram size hsize).card =
        (twoTailRowDiagram size hsize).rowLens.sum :=
      YoungDiagram.card_eq_sum_rowLens
    _ = [size - 2, 2].sum := by rw [twoTailRowDiagram_rowLens]
    _ = size := by simp; omega

theorem twoTailRowDiagram_rowLen
    (size : ℕ) (hsize : 4 ≤ size) (row : ℕ) :
    (twoTailRowDiagram size hsize).rowLen row =
      if row = 0 then size - 2 else if row = 1 then 2 else 0 := by
  by_cases hrow : row < 2
  · interval_cases row <;>
      simp [twoTailRowDiagram, YoungDiagram.rowLen_ofRowLens']
  · have hempty : (twoTailRowDiagram size hsize).row row = ∅ := by
      ext cell
      simp only [YoungDiagram.mem_row_iff]
      unfold twoTailRowDiagram
      rw [YoungDiagram.mem_ofRowLens]
      simp
      omega
    rw [YoungDiagram.rowLen_eq_card, hempty]
    rw [if_neg (by omega), if_neg (by omega)]
    simp

theorem hookDiagram_rowLen_kernel
    (size : ℕ) (hsize : 2 ≤ size) (row : ℕ) :
    (YoungDiagram.hookDiagram size).rowLen row =
      if row = 0 then size - 1 else if row = 1 then 1 else 0 := by
  have hdiagram : YoungDiagram.hookDiagram size =
      YoungDiagram.ofRowLens [size - 1, 1] (sorted_pair (by omega)) := by
    apply (YoungDiagram.eq_iff_rowLens_eq).2
    rw [YoungDiagram.hookDiagram_rowLens hsize]
    exact (YoungDiagram.rowLens_ofRowLens_eq_self (by simp; omega)).symm
  by_cases hrow : row < 2
  · rw [hdiagram]
    interval_cases row <;>
      simp [YoungDiagram.rowLen_ofRowLens']
  · rw [hdiagram]
    have hempty : (YoungDiagram.ofRowLens [size - 1, 1]
      (sorted_pair (by omega))).row row = ∅ := by
      ext cell
      simp only [YoungDiagram.mem_row_iff]
      rw [YoungDiagram.mem_ofRowLens]
      simp
      omega
    rw [YoungDiagram.rowLen_eq_card, hempty]
    rw [if_neg (by omega), if_neg (by omega)]
    simp

theorem twoTailRowDiagram_corners
    (size : ℕ) (hsize : 5 ≤ size) :
    (twoTailRowDiagram size (by omega)).corners =
      {(0, size - 3), (1, 1)} := by
  ext cell
  rcases cell with ⟨row, column⟩
  simp only [YoungDiagram.corners, Finset.mem_filter,
    YoungDiagram.mem_cells, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq]
  constructor
  · rintro ⟨hmem, hright, hbelow⟩
    have hmem' := hmem
    unfold twoTailRowDiagram at hmem'
    rw [YoungDiagram.mem_ofRowLens] at hmem'
    rcases hmem' with ⟨hrow, hcolumn⟩
    simp at hrow
    interval_cases row <;>
      simp [twoTailRowDiagram, YoungDiagram.rowLen_ofRowLens'] at hright <;>
      omega
  · intro hcorner
    rcases hcorner with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · constructor
      · unfold twoTailRowDiagram
        rw [YoungDiagram.mem_ofRowLens]
        simp
        omega
      constructor
      · simp [twoTailRowDiagram, YoungDiagram.rowLen_ofRowLens']
        omega
      · have hmem0 : (0, size - 3) ∈ twoTailRowDiagram size (by omega) := by
          unfold twoTailRowDiagram
          rw [YoungDiagram.mem_ofRowLens]
          simp
          omega
        have hnot1 : (1, size - 3) ∉ twoTailRowDiagram size (by omega) := by
          unfold twoTailRowDiagram
          rw [YoungDiagram.mem_ofRowLens]
          simp
          omega
        rw [YoungDiagram.mem_iff_lt_colLen] at hmem0 hnot1
        omega
    · constructor
      · unfold twoTailRowDiagram
        rw [YoungDiagram.mem_ofRowLens]
        simp
      constructor
      · simp [twoTailRowDiagram, YoungDiagram.rowLen_ofRowLens']
      · have hmem1 : (1, 1) ∈ twoTailRowDiagram size (by omega) := by
          unfold twoTailRowDiagram
          rw [YoungDiagram.mem_ofRowLens]
          simp
        have hnot2 : (2, 1) ∉ twoTailRowDiagram size (by omega) := by
          unfold twoTailRowDiagram
          rw [YoungDiagram.mem_ofRowLens]
          simp
        rw [YoungDiagram.mem_iff_lt_colLen] at hmem1 hnot2
        omega

theorem twoTailRowDiagram_sub_zero
    (size : ℕ) (hsize : 5 ≤ size) :
    (twoTailRowDiagram size (by omega)).sub (Finsupp.single 0 1) =
      twoTailRowDiagram (size - 1) (by omega) := by
  let diagram := twoTailRowDiagram size (by omega)
  have hcorner : (0, size - 3) ∈ diagram.corners := by
    rw [twoTailRowDiagram_corners size hsize]
    simp
  have hcondition := subSingle_sub_cond_kernel hcorner
  have hsubCondition := YoungDiagram.sub_cond hcondition
  apply (YoungDiagram.rowLen'_eq_iff).mp
  rw [YoungDiagram.sub_rowLen' hsubCondition]
  apply Finsupp.ext
  intro row
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply,
    YoungDiagram.rowLen'_eq_rowLen]
  rw [twoTailRowDiagram_rowLen, twoTailRowDiagram_rowLen]
  split_ifs <;> omega

theorem twoTailRowDiagram_sub_one
    (size : ℕ) (hsize : 5 ≤ size) :
    (twoTailRowDiagram size (by omega)).sub (Finsupp.single 1 1) =
      YoungDiagram.hookDiagram (size - 1) := by
  let diagram := twoTailRowDiagram size (by omega)
  have hcorner : (1, 1) ∈ diagram.corners := by
    rw [twoTailRowDiagram_corners size hsize]
    simp
  have hcondition := subSingle_sub_cond_kernel hcorner
  have hsubCondition := YoungDiagram.sub_cond hcondition
  apply (YoungDiagram.rowLen'_eq_iff).mp
  rw [YoungDiagram.sub_rowLen' hsubCondition]
  apply Finsupp.ext
  intro row
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply,
    YoungDiagram.rowLen'_eq_rowLen]
  rw [twoTailRowDiagram_rowLen,
    hookDiagram_rowLen_kernel (size - 1) (by omega)]
  split_ifs <;> omega

theorem twoTailRowDiagram_kostka_double
    (size : ℕ) (hsize : 4 ≤ size) :
    2 * kostkaNumber (twoTailRowDiagram size hsize)
        (Multiset.replicate size 1) = size * (size - 3) := by
  induction size using Nat.strong_induction_on with
  | h size ih =>
      by_cases hbase : size = 4
      · subst size
        change 2 * kostkaNumber
          (YoungDiagram.ofRowLens [2, 2] (sorted_pair (by rfl)))
          (Multiset.replicate 4 1) = 4 * (4 - 3)
        rw [kostka_22]
      · have hfive : 5 ≤ size := by omega
        have hrec := kostkaStandard_corner_recursion_cells
          (diagram := twoTailRowDiagram size (by omega)) (by
            rw [twoTailRowDiagram_card]
            omega)
        rw [twoTailRowDiagram_card] at hrec
        have hsum :
            (∑ cell : (twoTailRowDiagram size (by omega)).corners,
              kostkaNumber ((twoTailRowDiagram size (by omega)).sub
                (Finsupp.single cell.1.1 1))
                (Multiset.replicate (size - 1) 1)) =
              ∑ cell ∈ (twoTailRowDiagram size (by omega)).corners,
                kostkaNumber ((twoTailRowDiagram size (by omega)).sub
                  (Finsupp.single cell.1 1))
                  (Multiset.replicate (size - 1) 1) :=
          by
            simpa only using Finset.sum_coe_sort
              (twoTailRowDiagram size (by omega)).corners
              (fun cell => kostkaNumber
                ((twoTailRowDiagram size (by omega)).sub
                  (Finsupp.single cell.1 1))
                (Multiset.replicate (size - 1) 1))
        rw [hsum, twoTailRowDiagram_corners size hfive] at hrec
        rw [Finset.sum_insert (by simp), Finset.sum_singleton] at hrec
        rw [twoTailRowDiagram_sub_zero size hfive,
          twoTailRowDiagram_sub_one size hfive] at hrec
        have hinduction := ih (size - 1) (by omega) (by omega)
        have hhook := kostka_hook_replicate (size - 1) (by omega)
        have hprevSub : size - 1 - 3 = size - 4 := by omega
        have hhookSub : size - 1 - 1 = size - 2 := by omega
        rw [hprevSub] at hinduction
        rw [hrec, hhook, hhookSub]
        have hpure : (size - 1) * (size - 4) + 2 * (size - 2) =
            size * (size - 3) := by
          let offset := size - 5
          have hsizeEq : size = offset + 5 := by
            dsimp [offset]
            omega
          rw [hsizeEq]
          simp
          ring
        calc
          2 * (kostkaNumber (twoTailRowDiagram (size - 1) (by omega))
                (Multiset.replicate (size - 1) 1) + (size - 2)) =
              2 * kostkaNumber (twoTailRowDiagram (size - 1) (by omega))
                (Multiset.replicate (size - 1) 1) + 2 * (size - 2) := by ring
          _ = (size - 1) * (size - 4) + 2 * (size - 2) := by
            rw [hinduction]
          _ = size * (size - 3) := hpure

noncomputable def twoTailColumnDiagram (size : ℕ) (hsize : 4 ≤ size) :
    YoungDiagram :=
  YoungDiagram.ofRowLens [size - 2, 1, 1]
    (sorted_triple (by omega) (by rfl))

@[simp] theorem twoTailColumnDiagram_rowLens
    (size : ℕ) (hsize : 4 ≤ size) :
    (twoTailColumnDiagram size hsize).rowLens = [size - 2, 1, 1] := by
  unfold twoTailColumnDiagram
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  simp
  omega

@[simp] theorem twoTailColumnDiagram_card
    (size : ℕ) (hsize : 4 ≤ size) :
    (twoTailColumnDiagram size hsize).card = size := by
  calc
    (twoTailColumnDiagram size hsize).card =
        (twoTailColumnDiagram size hsize).rowLens.sum :=
      YoungDiagram.card_eq_sum_rowLens
    _ = [size - 2, 1, 1].sum := by rw [twoTailColumnDiagram_rowLens]
    _ = size := by simp; omega

theorem twoTailColumnDiagram_rowLen
    (size : ℕ) (hsize : 4 ≤ size) (row : ℕ) :
    (twoTailColumnDiagram size hsize).rowLen row =
      if row = 0 then size - 2 else if row = 1 then 1
      else if row = 2 then 1 else 0 := by
  by_cases hrow : row < 3
  · interval_cases row <;>
      simp [twoTailColumnDiagram, YoungDiagram.rowLen_ofRowLens']
  · have hempty : (twoTailColumnDiagram size hsize).row row = ∅ := by
      ext cell
      simp only [YoungDiagram.mem_row_iff]
      unfold twoTailColumnDiagram
      rw [YoungDiagram.mem_ofRowLens]
      simp
      omega
    rw [YoungDiagram.rowLen_eq_card, hempty]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp

theorem twoTailColumnDiagram_corners
    (size : ℕ) (hsize : 5 ≤ size) :
    (twoTailColumnDiagram size (by omega)).corners =
      {(0, size - 3), (2, 0)} := by
  ext cell
  rcases cell with ⟨row, column⟩
  simp only [YoungDiagram.corners, Finset.mem_filter,
    YoungDiagram.mem_cells, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq]
  constructor
  · rintro ⟨hmem, hright, hbelow⟩
    have hmem' := hmem
    unfold twoTailColumnDiagram at hmem'
    rw [YoungDiagram.mem_ofRowLens] at hmem'
    rcases hmem' with ⟨hrow, hcolumn⟩
    simp at hrow
    interval_cases row
    · left
      constructor
      · rfl
      · simp [twoTailColumnDiagram,
          YoungDiagram.rowLen_ofRowLens'] at hright
        omega
    · simp [twoTailColumnDiagram, YoungDiagram.rowLen_ofRowLens'] at hright
      have hcolumnZero : column = 0 := by omega
      subst column
      have hmem2 : (2, 0) ∈ twoTailColumnDiagram size (by omega) := by
        unfold twoTailColumnDiagram
        rw [YoungDiagram.mem_ofRowLens]
        simp
      rw [YoungDiagram.mem_iff_lt_colLen] at hmem2
      omega
    · right
      constructor
      · rfl
      · simp [twoTailColumnDiagram,
          YoungDiagram.rowLen_ofRowLens'] at hright
        omega
  · intro hcorner
    rcases hcorner with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · constructor
      · unfold twoTailColumnDiagram
        rw [YoungDiagram.mem_ofRowLens]
        simp
        omega
      constructor
      · simp [twoTailColumnDiagram, YoungDiagram.rowLen_ofRowLens']
        omega
      · have hmem0 : (0, size - 3) ∈ twoTailColumnDiagram size (by omega) := by
          unfold twoTailColumnDiagram
          rw [YoungDiagram.mem_ofRowLens]
          simp
          omega
        have hnot1 : (1, size - 3) ∉ twoTailColumnDiagram size (by omega) := by
          unfold twoTailColumnDiagram
          rw [YoungDiagram.mem_ofRowLens]
          simp
          omega
        rw [YoungDiagram.mem_iff_lt_colLen] at hmem0 hnot1
        omega
    · constructor
      · unfold twoTailColumnDiagram
        rw [YoungDiagram.mem_ofRowLens]
        simp
      constructor
      · simp [twoTailColumnDiagram, YoungDiagram.rowLen_ofRowLens']
      · have hmem2 : (2, 0) ∈ twoTailColumnDiagram size (by omega) := by
          unfold twoTailColumnDiagram
          rw [YoungDiagram.mem_ofRowLens]
          simp
        have hnot3 : (3, 0) ∉ twoTailColumnDiagram size (by omega) := by
          unfold twoTailColumnDiagram
          rw [YoungDiagram.mem_ofRowLens]
          simp
        rw [YoungDiagram.mem_iff_lt_colLen] at hmem2 hnot3
        omega

theorem twoTailColumnDiagram_sub_zero
    (size : ℕ) (hsize : 5 ≤ size) :
    (twoTailColumnDiagram size (by omega)).sub (Finsupp.single 0 1) =
      twoTailColumnDiagram (size - 1) (by omega) := by
  let diagram := twoTailColumnDiagram size (by omega)
  have hcorner : (0, size - 3) ∈ diagram.corners := by
    rw [twoTailColumnDiagram_corners size hsize]
    simp
  have hcondition := subSingle_sub_cond_kernel hcorner
  have hsubCondition := YoungDiagram.sub_cond hcondition
  apply (YoungDiagram.rowLen'_eq_iff).mp
  rw [YoungDiagram.sub_rowLen' hsubCondition]
  apply Finsupp.ext
  intro row
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply,
    YoungDiagram.rowLen'_eq_rowLen]
  rw [twoTailColumnDiagram_rowLen, twoTailColumnDiagram_rowLen]
  split_ifs <;> omega

theorem twoTailColumnDiagram_sub_two
    (size : ℕ) (hsize : 5 ≤ size) :
    (twoTailColumnDiagram size (by omega)).sub (Finsupp.single 2 1) =
      YoungDiagram.hookDiagram (size - 1) := by
  let diagram := twoTailColumnDiagram size (by omega)
  have hcorner : (2, 0) ∈ diagram.corners := by
    rw [twoTailColumnDiagram_corners size hsize]
    simp
  have hcondition := subSingle_sub_cond_kernel hcorner
  have hsubCondition := YoungDiagram.sub_cond hcondition
  apply (YoungDiagram.rowLen'_eq_iff).mp
  rw [YoungDiagram.sub_rowLen' hsubCondition]
  apply Finsupp.ext
  intro row
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply,
    YoungDiagram.rowLen'_eq_rowLen]
  rw [twoTailColumnDiagram_rowLen,
    hookDiagram_rowLen_kernel (size - 1) (by omega)]
  split_ifs <;> omega

theorem twoTailColumnDiagram_kostka_double
    (size : ℕ) (hsize : 4 ≤ size) :
    2 * kostkaNumber (twoTailColumnDiagram size hsize)
        (Multiset.replicate size 1) = (size - 1) * (size - 2) := by
  induction size using Nat.strong_induction_on with
  | h size ih =>
      by_cases hbase : size = 4
      · subst size
        change 2 * kostkaNumber
          (YoungDiagram.ofRowLens [2, 1, 1]
            (sorted_triple (by norm_num) (by rfl)))
          (Multiset.replicate 4 1) = (4 - 1) * (4 - 2)
        rw [kostka_211]
      · have hfive : 5 ≤ size := by omega
        have hrec := kostkaStandard_corner_recursion_cells
          (diagram := twoTailColumnDiagram size (by omega)) (by
            rw [twoTailColumnDiagram_card]
            omega)
        rw [twoTailColumnDiagram_card] at hrec
        have hsum :
            (∑ cell : (twoTailColumnDiagram size (by omega)).corners,
              kostkaNumber ((twoTailColumnDiagram size (by omega)).sub
                (Finsupp.single cell.1.1 1))
                (Multiset.replicate (size - 1) 1)) =
              ∑ cell ∈ (twoTailColumnDiagram size (by omega)).corners,
                kostkaNumber ((twoTailColumnDiagram size (by omega)).sub
                  (Finsupp.single cell.1 1))
                  (Multiset.replicate (size - 1) 1) := by
          simpa only using Finset.sum_coe_sort
            (twoTailColumnDiagram size (by omega)).corners
            (fun cell => kostkaNumber
              ((twoTailColumnDiagram size (by omega)).sub
                (Finsupp.single cell.1 1))
              (Multiset.replicate (size - 1) 1))
        rw [hsum, twoTailColumnDiagram_corners size hfive] at hrec
        rw [Finset.sum_insert (by simp), Finset.sum_singleton] at hrec
        rw [twoTailColumnDiagram_sub_zero size hfive,
          twoTailColumnDiagram_sub_two size hfive] at hrec
        have hinduction := ih (size - 1) (by omega) (by omega)
        have hhook := kostka_hook_replicate (size - 1) (by omega)
        have hprev1 : size - 1 - 1 = size - 2 := by omega
        have hprev2 : size - 1 - 2 = size - 3 := by omega
        have hhookSub : size - 1 - 1 = size - 2 := by omega
        rw [hprev1, hprev2] at hinduction
        rw [hrec, hhook, hhookSub]
        have hpure : (size - 2) * (size - 3) + 2 * (size - 2) =
            (size - 1) * (size - 2) := by
          let offset := size - 5
          have hsizeEq : size = offset + 5 := by
            dsimp [offset]
            omega
          rw [hsizeEq]
          simp
          ring
        calc
          2 * (kostkaNumber (twoTailColumnDiagram (size - 1) (by omega))
                (Multiset.replicate (size - 1) 1) + (size - 2)) =
              2 * kostkaNumber (twoTailColumnDiagram (size - 1) (by omega))
                (Multiset.replicate (size - 1) 1) + 2 * (size - 2) := by ring
          _ = (size - 2) * (size - 3) + 2 * (size - 2) := by
            rw [hinduction]
          _ = (size - 1) * (size - 2) := hpure

noncomputable def threeTailRowDiagram (size : ℕ) (hsize : 6 ≤ size) :
    YoungDiagram :=
  YoungDiagram.ofRowLens [size - 3, 3] (sorted_pair (by omega))

noncomputable def threeTailMixedDiagram (size : ℕ) (hsize : 6 ≤ size) :
    YoungDiagram :=
  YoungDiagram.ofRowLens [size - 3, 2, 1]
    (sorted_triple (by omega) (by omega))

noncomputable def threeTailColumnDiagram (size : ℕ) (hsize : 6 ≤ size) :
    YoungDiagram :=
  YoungDiagram.ofRowLens [size - 3, 1, 1, 1]
    (by
      apply List.Pairwise.sortedGE
      simp
      omega)

@[simp] theorem threeTailRowDiagram_rowLens
    (size : ℕ) (hsize : 6 ≤ size) :
    (threeTailRowDiagram size hsize).rowLens = [size - 3, 3] := by
  unfold threeTailRowDiagram
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  simp
  omega

@[simp] theorem threeTailMixedDiagram_rowLens
    (size : ℕ) (hsize : 6 ≤ size) :
    (threeTailMixedDiagram size hsize).rowLens = [size - 3, 2, 1] := by
  unfold threeTailMixedDiagram
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  simp
  omega

@[simp] theorem threeTailColumnDiagram_rowLens
    (size : ℕ) (hsize : 6 ≤ size) :
    (threeTailColumnDiagram size hsize).rowLens = [size - 3, 1, 1, 1] := by
  unfold threeTailColumnDiagram
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  simp
  omega

@[simp] theorem threeTailRowDiagram_card
    (size : ℕ) (hsize : 6 ≤ size) :
    (threeTailRowDiagram size hsize).card = size := by
  rw [YoungDiagram.card_eq_sum_rowLens, threeTailRowDiagram_rowLens]
  simp
  omega

@[simp] theorem threeTailMixedDiagram_card
    (size : ℕ) (hsize : 6 ≤ size) :
    (threeTailMixedDiagram size hsize).card = size := by
  rw [YoungDiagram.card_eq_sum_rowLens, threeTailMixedDiagram_rowLens]
  simp
  omega

@[simp] theorem threeTailColumnDiagram_card
    (size : ℕ) (hsize : 6 ≤ size) :
    (threeTailColumnDiagram size hsize).card = size := by
  rw [YoungDiagram.card_eq_sum_rowLens, threeTailColumnDiagram_rowLens]
  simp
  omega

theorem threeTailRowDiagram_rowLen
    (size : ℕ) (hsize : 6 ≤ size) (row : ℕ) :
    (threeTailRowDiagram size hsize).rowLen row =
      if row = 0 then size - 3 else if row = 1 then 3 else 0 := by
  by_cases hrow : row < 2
  · interval_cases row <;>
      simp [threeTailRowDiagram, YoungDiagram.rowLen_ofRowLens']
  · have hempty : (threeTailRowDiagram size hsize).row row = ∅ := by
      ext cell
      simp only [YoungDiagram.mem_row_iff]
      unfold threeTailRowDiagram
      rw [YoungDiagram.mem_ofRowLens]
      simp
      omega
    rw [YoungDiagram.rowLen_eq_card, hempty]
    rw [if_neg (by omega), if_neg (by omega)]
    simp

theorem threeTailRowDiagram_corners
    (size : ℕ) (hsize : 7 ≤ size) :
    (threeTailRowDiagram size (by omega)).corners =
      {(0, size - 4), (1, 2)} := by
  ext cell
  rcases cell with ⟨row, column⟩
  simp only [YoungDiagram.corners, Finset.mem_filter,
    YoungDiagram.mem_cells, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq]
  constructor
  · rintro ⟨hmem, hright, hbelow⟩
    have hmem' := hmem
    unfold threeTailRowDiagram at hmem'
    rw [YoungDiagram.mem_ofRowLens] at hmem'
    rcases hmem' with ⟨hrow, hcolumn⟩
    simp at hrow
    interval_cases row <;>
      simp [threeTailRowDiagram, YoungDiagram.rowLen_ofRowLens'] at hright <;>
      omega
  · intro hcorner
    rcases hcorner with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · constructor
      · unfold threeTailRowDiagram
        rw [YoungDiagram.mem_ofRowLens]
        simp
        omega
      constructor
      · simp [threeTailRowDiagram, YoungDiagram.rowLen_ofRowLens']
        omega
      · have hmem0 : (0, size - 4) ∈ threeTailRowDiagram size (by omega) := by
          unfold threeTailRowDiagram
          rw [YoungDiagram.mem_ofRowLens]
          simp
          omega
        have hnot1 : (1, size - 4) ∉ threeTailRowDiagram size (by omega) := by
          unfold threeTailRowDiagram
          rw [YoungDiagram.mem_ofRowLens]
          simp
          omega
        rw [YoungDiagram.mem_iff_lt_colLen] at hmem0 hnot1
        omega
    · constructor
      · unfold threeTailRowDiagram
        rw [YoungDiagram.mem_ofRowLens]
        simp
      constructor
      · simp [threeTailRowDiagram, YoungDiagram.rowLen_ofRowLens']
      · have hmem1 : (1, 2) ∈ threeTailRowDiagram size (by omega) := by
          unfold threeTailRowDiagram
          rw [YoungDiagram.mem_ofRowLens]
          simp
        have hnot2 : (2, 2) ∉ threeTailRowDiagram size (by omega) := by
          unfold threeTailRowDiagram
          rw [YoungDiagram.mem_ofRowLens]
          simp
        rw [YoungDiagram.mem_iff_lt_colLen] at hmem1 hnot2
        omega

theorem threeTailRowDiagram_sub_zero
    (size : ℕ) (hsize : 7 ≤ size) :
    (threeTailRowDiagram size (by omega)).sub (Finsupp.single 0 1) =
      threeTailRowDiagram (size - 1) (by omega) := by
  let diagram := threeTailRowDiagram size (by omega)
  have hcorner : (0, size - 4) ∈ diagram.corners := by
    rw [threeTailRowDiagram_corners size hsize]
    simp
  have hcondition := subSingle_sub_cond_kernel hcorner
  have hsubCondition := YoungDiagram.sub_cond hcondition
  apply (YoungDiagram.rowLen'_eq_iff).mp
  rw [YoungDiagram.sub_rowLen' hsubCondition]
  apply Finsupp.ext
  intro row
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply,
    YoungDiagram.rowLen'_eq_rowLen]
  rw [threeTailRowDiagram_rowLen, threeTailRowDiagram_rowLen]
  split_ifs <;> omega

theorem threeTailRowDiagram_sub_one
    (size : ℕ) (hsize : 7 ≤ size) :
    (threeTailRowDiagram size (by omega)).sub (Finsupp.single 1 1) =
      twoTailRowDiagram (size - 1) (by omega) := by
  let diagram := threeTailRowDiagram size (by omega)
  have hcorner : (1, 2) ∈ diagram.corners := by
    rw [threeTailRowDiagram_corners size hsize]
    simp
  have hcondition := subSingle_sub_cond_kernel hcorner
  have hsubCondition := YoungDiagram.sub_cond hcondition
  apply (YoungDiagram.rowLen'_eq_iff).mp
  rw [YoungDiagram.sub_rowLen' hsubCondition]
  apply Finsupp.ext
  intro row
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply,
    YoungDiagram.rowLen'_eq_rowLen]
  rw [threeTailRowDiagram_rowLen, twoTailRowDiagram_rowLen]
  split_ifs <;> omega

theorem threeTailMixedDiagram_rowLen
    (size : ℕ) (hsize : 6 ≤ size) (row : ℕ) :
    (threeTailMixedDiagram size hsize).rowLen row =
      if row = 0 then size - 3 else if row = 1 then 2
      else if row = 2 then 1 else 0 := by
  by_cases hrow : row < 3
  · interval_cases row <;>
      simp [threeTailMixedDiagram, YoungDiagram.rowLen_ofRowLens']
  · have hempty : (threeTailMixedDiagram size hsize).row row = ∅ := by
      ext cell
      simp only [YoungDiagram.mem_row_iff]
      unfold threeTailMixedDiagram
      rw [YoungDiagram.mem_ofRowLens]
      simp
      omega
    rw [YoungDiagram.rowLen_eq_card, hempty]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp

theorem threeTailMixedDiagram_corners
    (size : ℕ) (hsize : 7 ≤ size) :
    (threeTailMixedDiagram size (by omega)).corners =
      {(0, size - 4), (1, 1), (2, 0)} := by
  ext cell
  rcases cell with ⟨row, column⟩
  simp only [YoungDiagram.corners, Finset.mem_filter, YoungDiagram.mem_cells,
    Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨hmem, hright, hbelow⟩
    have hmem' := hmem
    unfold threeTailMixedDiagram at hmem'
    rw [YoungDiagram.mem_ofRowLens] at hmem'
    rcases hmem' with ⟨hrow, hcolumn⟩
    simp at hrow
    interval_cases row
    · left
      constructor
      · rfl
      · simp [threeTailMixedDiagram, YoungDiagram.rowLen_ofRowLens'] at hright
        omega
    · right; left
      constructor
      · rfl
      · simp [threeTailMixedDiagram, YoungDiagram.rowLen_ofRowLens'] at hright
        omega
    · right; right
      constructor
      · rfl
      · simp [threeTailMixedDiagram, YoungDiagram.rowLen_ofRowLens'] at hright
        omega
  · intro hcorner
    rcases hcorner with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · constructor
      · unfold threeTailMixedDiagram
        rw [YoungDiagram.mem_ofRowLens]
        simp
        omega
      constructor
      · simp [threeTailMixedDiagram, YoungDiagram.rowLen_ofRowLens']
        omega
      · have hmem0 : (0, size - 4) ∈ threeTailMixedDiagram size (by omega) := by
          unfold threeTailMixedDiagram
          rw [YoungDiagram.mem_ofRowLens]
          simp
          omega
        have hnot1 : (1, size - 4) ∉ threeTailMixedDiagram size (by omega) := by
          unfold threeTailMixedDiagram
          rw [YoungDiagram.mem_ofRowLens]
          simp
          omega
        rw [YoungDiagram.mem_iff_lt_colLen] at hmem0 hnot1
        omega
    · constructor
      · unfold threeTailMixedDiagram
        rw [YoungDiagram.mem_ofRowLens]
        simp
      constructor
      · simp [threeTailMixedDiagram, YoungDiagram.rowLen_ofRowLens']
      · have hmem1 : (1, 1) ∈ threeTailMixedDiagram size (by omega) := by
          unfold threeTailMixedDiagram
          rw [YoungDiagram.mem_ofRowLens]
          simp
        have hnot2 : (2, 1) ∉ threeTailMixedDiagram size (by omega) := by
          unfold threeTailMixedDiagram
          rw [YoungDiagram.mem_ofRowLens]
          simp
        rw [YoungDiagram.mem_iff_lt_colLen] at hmem1 hnot2
        omega
    · constructor
      · unfold threeTailMixedDiagram
        rw [YoungDiagram.mem_ofRowLens]
        simp
      constructor
      · simp [threeTailMixedDiagram, YoungDiagram.rowLen_ofRowLens']
      · have hmem2 : (2, 0) ∈ threeTailMixedDiagram size (by omega) := by
          unfold threeTailMixedDiagram
          rw [YoungDiagram.mem_ofRowLens]
          simp
        have hnot3 : (3, 0) ∉ threeTailMixedDiagram size (by omega) := by
          unfold threeTailMixedDiagram
          rw [YoungDiagram.mem_ofRowLens]
          simp
        rw [YoungDiagram.mem_iff_lt_colLen] at hmem2 hnot3
        omega

theorem threeTailMixedDiagram_sub_zero
    (size : ℕ) (hsize : 7 ≤ size) :
    (threeTailMixedDiagram size (by omega)).sub (Finsupp.single 0 1) =
      threeTailMixedDiagram (size - 1) (by omega) := by
  let diagram := threeTailMixedDiagram size (by omega)
  have hcorner : (0, size - 4) ∈ diagram.corners := by
    rw [threeTailMixedDiagram_corners size hsize]
    simp
  have hsubCondition := YoungDiagram.sub_cond (subSingle_sub_cond_kernel hcorner)
  apply (YoungDiagram.rowLen'_eq_iff).mp
  rw [YoungDiagram.sub_rowLen' hsubCondition]
  apply Finsupp.ext
  intro row
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply,
    YoungDiagram.rowLen'_eq_rowLen]
  rw [threeTailMixedDiagram_rowLen, threeTailMixedDiagram_rowLen]
  split_ifs <;> omega

theorem threeTailMixedDiagram_sub_one
    (size : ℕ) (hsize : 7 ≤ size) :
    (threeTailMixedDiagram size (by omega)).sub (Finsupp.single 1 1) =
      twoTailColumnDiagram (size - 1) (by omega) := by
  let diagram := threeTailMixedDiagram size (by omega)
  have hcorner : (1, 1) ∈ diagram.corners := by
    rw [threeTailMixedDiagram_corners size hsize]
    simp
  have hsubCondition := YoungDiagram.sub_cond (subSingle_sub_cond_kernel hcorner)
  apply (YoungDiagram.rowLen'_eq_iff).mp
  rw [YoungDiagram.sub_rowLen' hsubCondition]
  apply Finsupp.ext
  intro row
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply,
    YoungDiagram.rowLen'_eq_rowLen]
  rw [threeTailMixedDiagram_rowLen, twoTailColumnDiagram_rowLen]
  split_ifs <;> omega

theorem threeTailMixedDiagram_sub_two
    (size : ℕ) (hsize : 7 ≤ size) :
    (threeTailMixedDiagram size (by omega)).sub (Finsupp.single 2 1) =
      twoTailRowDiagram (size - 1) (by omega) := by
  let diagram := threeTailMixedDiagram size (by omega)
  have hcorner : (2, 0) ∈ diagram.corners := by
    rw [threeTailMixedDiagram_corners size hsize]
    simp
  have hsubCondition := YoungDiagram.sub_cond (subSingle_sub_cond_kernel hcorner)
  apply (YoungDiagram.rowLen'_eq_iff).mp
  rw [YoungDiagram.sub_rowLen' hsubCondition]
  apply Finsupp.ext
  intro row
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply,
    YoungDiagram.rowLen'_eq_rowLen]
  rw [threeTailMixedDiagram_rowLen, twoTailRowDiagram_rowLen]
  split_ifs <;> omega

theorem threeTailColumnDiagram_rowLen
    (size : ℕ) (hsize : 6 ≤ size) (row : ℕ) :
    (threeTailColumnDiagram size hsize).rowLen row =
      if row = 0 then size - 3 else if row = 1 then 1
      else if row = 2 then 1 else if row = 3 then 1 else 0 := by
  by_cases hrow : row < 4
  · interval_cases row <;>
      simp [threeTailColumnDiagram, YoungDiagram.rowLen_ofRowLens']
  · have hempty : (threeTailColumnDiagram size hsize).row row = ∅ := by
      ext cell
      simp only [YoungDiagram.mem_row_iff]
      unfold threeTailColumnDiagram
      rw [YoungDiagram.mem_ofRowLens]
      simp
      omega
    rw [YoungDiagram.rowLen_eq_card, hempty]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
    simp

theorem threeTailColumnDiagram_corners
    (size : ℕ) (hsize : 7 ≤ size) :
    (threeTailColumnDiagram size (by omega)).corners =
      {(0, size - 4), (3, 0)} := by
  ext cell
  rcases cell with ⟨row, column⟩
  simp only [YoungDiagram.corners, Finset.mem_filter, YoungDiagram.mem_cells,
    Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨hmem, hright, hbelow⟩
    have hmem' := hmem
    unfold threeTailColumnDiagram at hmem'
    rw [YoungDiagram.mem_ofRowLens] at hmem'
    rcases hmem' with ⟨hrow, hcolumn⟩
    simp at hrow
    interval_cases row
    · left
      constructor
      · rfl
      · simp [threeTailColumnDiagram, YoungDiagram.rowLen_ofRowLens'] at hright
        omega
    · simp [threeTailColumnDiagram, YoungDiagram.rowLen_ofRowLens'] at hright
      have hcolumnZero : column = 0 := by omega
      subst column
      have hmem3 : (3, 0) ∈ threeTailColumnDiagram size (by omega) := by
        unfold threeTailColumnDiagram
        rw [YoungDiagram.mem_ofRowLens]
        simp
      rw [YoungDiagram.mem_iff_lt_colLen] at hmem3
      omega
    · simp [threeTailColumnDiagram, YoungDiagram.rowLen_ofRowLens'] at hright
      have hcolumnZero : column = 0 := by omega
      subst column
      have hmem3 : (3, 0) ∈ threeTailColumnDiagram size (by omega) := by
        unfold threeTailColumnDiagram
        rw [YoungDiagram.mem_ofRowLens]
        simp
      rw [YoungDiagram.mem_iff_lt_colLen] at hmem3
      omega
    · right
      constructor
      · rfl
      · simp [threeTailColumnDiagram, YoungDiagram.rowLen_ofRowLens'] at hright
        omega
  · intro hcorner
    rcases hcorner with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · constructor
      · unfold threeTailColumnDiagram
        rw [YoungDiagram.mem_ofRowLens]
        simp
        omega
      constructor
      · simp [threeTailColumnDiagram, YoungDiagram.rowLen_ofRowLens']
        omega
      · have hmem0 : (0, size - 4) ∈ threeTailColumnDiagram size (by omega) := by
          unfold threeTailColumnDiagram
          rw [YoungDiagram.mem_ofRowLens]
          simp
          omega
        have hnot1 : (1, size - 4) ∉ threeTailColumnDiagram size (by omega) := by
          unfold threeTailColumnDiagram
          rw [YoungDiagram.mem_ofRowLens]
          simp
          omega
        rw [YoungDiagram.mem_iff_lt_colLen] at hmem0 hnot1
        omega
    · constructor
      · unfold threeTailColumnDiagram
        rw [YoungDiagram.mem_ofRowLens]
        simp
      constructor
      · simp [threeTailColumnDiagram, YoungDiagram.rowLen_ofRowLens']
      · have hmem3 : (3, 0) ∈ threeTailColumnDiagram size (by omega) := by
          unfold threeTailColumnDiagram
          rw [YoungDiagram.mem_ofRowLens]
          simp
        have hnot4 : (4, 0) ∉ threeTailColumnDiagram size (by omega) := by
          unfold threeTailColumnDiagram
          rw [YoungDiagram.mem_ofRowLens]
          simp
        rw [YoungDiagram.mem_iff_lt_colLen] at hmem3 hnot4
        omega

theorem threeTailColumnDiagram_sub_zero
    (size : ℕ) (hsize : 7 ≤ size) :
    (threeTailColumnDiagram size (by omega)).sub (Finsupp.single 0 1) =
      threeTailColumnDiagram (size - 1) (by omega) := by
  let diagram := threeTailColumnDiagram size (by omega)
  have hcorner : (0, size - 4) ∈ diagram.corners := by
    rw [threeTailColumnDiagram_corners size hsize]
    simp
  have hsubCondition := YoungDiagram.sub_cond (subSingle_sub_cond_kernel hcorner)
  apply (YoungDiagram.rowLen'_eq_iff).mp
  rw [YoungDiagram.sub_rowLen' hsubCondition]
  apply Finsupp.ext
  intro row
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply,
    YoungDiagram.rowLen'_eq_rowLen]
  rw [threeTailColumnDiagram_rowLen, threeTailColumnDiagram_rowLen]
  split_ifs <;> omega

theorem threeTailColumnDiagram_sub_three
    (size : ℕ) (hsize : 7 ≤ size) :
    (threeTailColumnDiagram size (by omega)).sub (Finsupp.single 3 1) =
      twoTailColumnDiagram (size - 1) (by omega) := by
  let diagram := threeTailColumnDiagram size (by omega)
  have hcorner : (3, 0) ∈ diagram.corners := by
    rw [threeTailColumnDiagram_corners size hsize]
    simp
  have hsubCondition := YoungDiagram.sub_cond (subSingle_sub_cond_kernel hcorner)
  apply (YoungDiagram.rowLen'_eq_iff).mp
  rw [YoungDiagram.sub_rowLen' hsubCondition]
  apply Finsupp.ext
  intro row
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply,
    YoungDiagram.rowLen'_eq_rowLen]
  rw [threeTailColumnDiagram_rowLen, twoTailColumnDiagram_rowLen]
  split_ifs <;> omega

theorem threeTailRow_kostka_recursion
    (size : ℕ) (hsize : 7 ≤ size) :
    kostkaNumber (threeTailRowDiagram size (by omega))
        (Multiset.replicate size 1) =
      kostkaNumber (threeTailRowDiagram (size - 1) (by omega))
          (Multiset.replicate (size - 1) 1) +
        kostkaNumber (twoTailRowDiagram (size - 1) (by omega))
          (Multiset.replicate (size - 1) 1) := by
  have hrec := kostkaStandard_corner_recursion_cells
    (diagram := threeTailRowDiagram size (by omega)) (by
      rw [threeTailRowDiagram_card]
      omega)
  rw [threeTailRowDiagram_card] at hrec
  have hsum :
      (∑ cell : (threeTailRowDiagram size (by omega)).corners,
        kostkaNumber ((threeTailRowDiagram size (by omega)).sub
          (Finsupp.single cell.1.1 1))
          (Multiset.replicate (size - 1) 1)) =
        ∑ cell ∈ (threeTailRowDiagram size (by omega)).corners,
          kostkaNumber ((threeTailRowDiagram size (by omega)).sub
            (Finsupp.single cell.1 1))
            (Multiset.replicate (size - 1) 1) := by
    simpa only using Finset.sum_coe_sort
      (threeTailRowDiagram size (by omega)).corners
      (fun cell => kostkaNumber
        ((threeTailRowDiagram size (by omega)).sub
          (Finsupp.single cell.1 1))
        (Multiset.replicate (size - 1) 1))
  rw [hsum, threeTailRowDiagram_corners size hsize] at hrec
  rw [Finset.sum_insert (by simp), Finset.sum_singleton] at hrec
  rw [threeTailRowDiagram_sub_zero size hsize,
    threeTailRowDiagram_sub_one size hsize] at hrec
  exact hrec

theorem threeTailMixed_kostka_recursion
    (size : ℕ) (hsize : 7 ≤ size) :
    kostkaNumber (threeTailMixedDiagram size (by omega))
        (Multiset.replicate size 1) =
      kostkaNumber (threeTailMixedDiagram (size - 1) (by omega))
          (Multiset.replicate (size - 1) 1) +
        kostkaNumber (twoTailColumnDiagram (size - 1) (by omega))
          (Multiset.replicate (size - 1) 1) +
        kostkaNumber (twoTailRowDiagram (size - 1) (by omega))
          (Multiset.replicate (size - 1) 1) := by
  have hrec := kostkaStandard_corner_recursion_cells
    (diagram := threeTailMixedDiagram size (by omega)) (by
      rw [threeTailMixedDiagram_card]
      omega)
  rw [threeTailMixedDiagram_card] at hrec
  have hsum :
      (∑ cell : (threeTailMixedDiagram size (by omega)).corners,
        kostkaNumber ((threeTailMixedDiagram size (by omega)).sub
          (Finsupp.single cell.1.1 1))
          (Multiset.replicate (size - 1) 1)) =
        ∑ cell ∈ (threeTailMixedDiagram size (by omega)).corners,
          kostkaNumber ((threeTailMixedDiagram size (by omega)).sub
            (Finsupp.single cell.1 1))
            (Multiset.replicate (size - 1) 1) := by
    simpa only using Finset.sum_coe_sort
      (threeTailMixedDiagram size (by omega)).corners
      (fun cell => kostkaNumber
        ((threeTailMixedDiagram size (by omega)).sub
          (Finsupp.single cell.1 1))
        (Multiset.replicate (size - 1) 1))
  rw [hsum, threeTailMixedDiagram_corners size hsize] at hrec
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    Finset.sum_singleton] at hrec
  rw [threeTailMixedDiagram_sub_zero size hsize,
    threeTailMixedDiagram_sub_one size hsize,
    threeTailMixedDiagram_sub_two size hsize] at hrec
  omega

theorem threeTailColumn_kostka_recursion
    (size : ℕ) (hsize : 7 ≤ size) :
    kostkaNumber (threeTailColumnDiagram size (by omega))
        (Multiset.replicate size 1) =
      kostkaNumber (threeTailColumnDiagram (size - 1) (by omega))
          (Multiset.replicate (size - 1) 1) +
        kostkaNumber (twoTailColumnDiagram (size - 1) (by omega))
          (Multiset.replicate (size - 1) 1) := by
  have hrec := kostkaStandard_corner_recursion_cells
    (diagram := threeTailColumnDiagram size (by omega)) (by
      rw [threeTailColumnDiagram_card]
      omega)
  rw [threeTailColumnDiagram_card] at hrec
  have hsum :
      (∑ cell : (threeTailColumnDiagram size (by omega)).corners,
        kostkaNumber ((threeTailColumnDiagram size (by omega)).sub
          (Finsupp.single cell.1.1 1))
          (Multiset.replicate (size - 1) 1)) =
        ∑ cell ∈ (threeTailColumnDiagram size (by omega)).corners,
          kostkaNumber ((threeTailColumnDiagram size (by omega)).sub
            (Finsupp.single cell.1 1))
            (Multiset.replicate (size - 1) 1) := by
    simpa only using Finset.sum_coe_sort
      (threeTailColumnDiagram size (by omega)).corners
      (fun cell => kostkaNumber
        ((threeTailColumnDiagram size (by omega)).sub
          (Finsupp.single cell.1 1))
        (Multiset.replicate (size - 1) 1))
  rw [hsum, threeTailColumnDiagram_corners size hsize] at hrec
  rw [Finset.sum_insert (by simp), Finset.sum_singleton] at hrec
  rw [threeTailColumnDiagram_sub_zero size hsize,
    threeTailColumnDiagram_sub_three size hsize] at hrec
  exact hrec

noncomputable def threeTailNewKostkaSum (size : ℕ) (hsize : 6 ≤ size) : ℕ :=
  kostkaNumber (threeTailRowDiagram size hsize) (Multiset.replicate size 1) +
    kostkaNumber (threeTailMixedDiagram size hsize) (Multiset.replicate size 1) +
    kostkaNumber (threeTailColumnDiagram size hsize) (Multiset.replicate size 1)

theorem kostka_3111_kernel :
    kostkaNumber (threeTailColumnDiagram 6 (by omega))
      (Multiset.replicate 6 1) = 10 := by
  rw [hookLength_formula' _ (by simp)]
  norm_num
  suffices hcells : (threeTailColumnDiagram 6 (by omega)).cells =
      {(0,0), (0,1), (0,2), (1,0), (2,0), (3,0)} by
    have hc0 : (threeTailColumnDiagram 6 (by omega)).colLen 0 = 4 := by
      have hmem : (3, 0) ∈ threeTailColumnDiagram 6 (by omega) := by
        exact (show (3, 0) ∈ (threeTailColumnDiagram 6 (by omega)).cells by
          rw [hcells]; simp)
      have hnot : (4, 0) ∉ threeTailColumnDiagram 6 (by omega) := by
        intro h
        have hcell : (4, 0) ∈ (threeTailColumnDiagram 6 (by omega)).cells := h
        rw [hcells] at hcell
        simp at hcell
      rw [YoungDiagram.mem_iff_lt_colLen] at hmem hnot
      omega
    have hc1 : (threeTailColumnDiagram 6 (by omega)).colLen 1 = 1 := by
      have hmem : (0, 1) ∈ threeTailColumnDiagram 6 (by omega) := by
        exact (show (0, 1) ∈ (threeTailColumnDiagram 6 (by omega)).cells by
          rw [hcells]; simp)
      have hnot : (1, 1) ∉ threeTailColumnDiagram 6 (by omega) := by
        intro h
        have hcell : (1, 1) ∈ (threeTailColumnDiagram 6 (by omega)).cells := h
        rw [hcells] at hcell
        simp at hcell
      rw [YoungDiagram.mem_iff_lt_colLen] at hmem hnot
      omega
    have hc2 : (threeTailColumnDiagram 6 (by omega)).colLen 2 = 1 := by
      have hmem : (0, 2) ∈ threeTailColumnDiagram 6 (by omega) := by
        exact (show (0, 2) ∈ (threeTailColumnDiagram 6 (by omega)).cells by
          rw [hcells]; simp)
      have hnot : (1, 2) ∉ threeTailColumnDiagram 6 (by omega) := by
        intro h
        have hcell : (1, 2) ∈ (threeTailColumnDiagram 6 (by omega)).cells := h
        rw [hcells] at hcell
        simp at hcell
      rw [YoungDiagram.mem_iff_lt_colLen] at hmem hnot
      omega
    have hr0 := threeTailColumnDiagram_rowLen 6 (by omega) 0
    have hr1 := threeTailColumnDiagram_rowLen 6 (by omega) 1
    have hr2 := threeTailColumnDiagram_rowLen 6 (by omega) 2
    have hr3 := threeTailColumnDiagram_rowLen 6 (by omega) 3
    norm_num at hr0 hr1 hr2 hr3
    simp [hcells, YoungDiagram.hookLength, hc0, hc1, hc2,
      hr0, hr1, hr2, hr3]
  ext cell
  unfold threeTailColumnDiagram
  simp [YoungDiagram.mem_ofRowLens]
  grind

theorem threeTailNewKostkaSum_triple
    (size : ℕ) (hsize : 6 ≤ size) :
    3 * threeTailNewKostkaSum size hsize =
      size * (size - 2) * (2 * size - 5) - 3 * (size - 1) ^ 2 := by
  induction size using Nat.strong_induction_on with
  | h size ih =>
      by_cases hbase : size = 6
      · subst size
        unfold threeTailNewKostkaSum
        change 3 * (kostkaNumber
            (YoungDiagram.ofRowLens [3, 3] (sorted_pair (by rfl)))
              (Multiset.replicate 6 1) +
          kostkaNumber
            (YoungDiagram.ofRowLens [3, 2, 1]
              (sorted_triple (by norm_num) (by norm_num)))
              (Multiset.replicate 6 1) +
          kostkaNumber
            (threeTailColumnDiagram 6 (by omega))
              (Multiset.replicate 6 1)) =
          6 * (6 - 2) * (2 * 6 - 5) - 3 * (6 - 1) ^ 2
        rw [kostka_33, kostka_321]
        rw [kostka_3111_kernel]
        norm_num
      · have hseven : 7 ≤ size := by omega
        have hrowRec := threeTailRow_kostka_recursion size hseven
        have hmixedRec := threeTailMixed_kostka_recursion size hseven
        have hcolumnRec := threeTailColumn_kostka_recursion size hseven
        have hinduction := ih (size - 1) (by omega) (by omega)
        have htwoRow := twoTailRowDiagram_kostka_double
          (size - 1) (by omega)
        have htwoColumn := twoTailColumnDiagram_kostka_double
          (size - 1) (by omega)
        have hprev1 : size - 1 - 1 = size - 2 := by omega
        have hprev2 : size - 1 - 2 = size - 3 := by omega
        have hprev3 : size - 1 - 3 = size - 4 := by omega
        rw [hprev1, hprev2] at hinduction
        rw [hprev1, hprev2] at htwoColumn
        rw [hprev3] at htwoRow
        let previousSum := threeTailNewKostkaSum (size - 1) (by omega)
        let rowExtra := kostkaNumber (twoTailRowDiagram (size - 1) (by omega))
          (Multiset.replicate (size - 1) 1)
        let columnExtra := kostkaNumber (twoTailColumnDiagram (size - 1) (by omega))
          (Multiset.replicate (size - 1) 1)
        have hsumRec : threeTailNewKostkaSum size hsize =
            previousSum + 2 * (rowExtra + columnExtra) := by
          dsimp [previousSum, rowExtra, columnExtra]
          unfold threeTailNewKostkaSum
          rw [hrowRec, hmixedRec, hcolumnRec]
          ring
        have hpreviousSum : 3 * previousSum =
            (size - 1) * (size - 3) * (2 * (size - 1) - 5) -
              3 * (size - 2) ^ 2 := by
          exact hinduction
        have hdoubleExtras : 2 * (rowExtra + columnExtra) =
            (size - 1) * (size - 4) + (size - 2) * (size - 3) := by
          unfold rowExtra columnExtra
          rw [mul_add, htwoRow, htwoColumn]
        have hpure :
            (size - 1) * (size - 3) * (2 * (size - 1) - 5) -
                3 * (size - 2) ^ 2 +
              3 * ((size - 1) * (size - 4) + (size - 2) * (size - 3)) =
            size * (size - 2) * (2 * size - 5) - 3 * (size - 1) ^ 2 := by
          let offset := size - 7
          have hsizeEq : size = offset + 7 := by
            dsimp [offset]
            omega
          rw [hsizeEq]
          have hleftScale : 2 * (offset + 7 - 1) - 5 = 2 * offset + 7 := by omega
          have hrightScale : 2 * (offset + 7) - 5 = 2 * offset + 9 := by omega
          rw [hleftScale, hrightScale]
          have hm1 : offset + 7 - 1 = offset + 6 := by omega
          have hm2 : offset + 7 - 2 = offset + 5 := by omega
          have hm3 : offset + 7 - 3 = offset + 4 := by omega
          have hm4 : offset + 7 - 4 = offset + 3 := by omega
          rw [hm1, hm2, hm3, hm4]
          have hleftBound :
              3 * (offset + 5) ^ 2 ≤
                (offset + 6) * (offset + 4) * (2 * offset + 7) := by
            have heq :
                (offset + 6) * (offset + 4) * (2 * offset + 7) =
                  3 * (offset + 5) ^ 2 +
                    (2 * offset ^ 3 + 24 * offset ^ 2 + 88 * offset + 93) := by
              ring
            rw [heq]
            omega
          have hrightBound :
              3 * (offset + 6) ^ 2 ≤
                (offset + 7) * (offset + 5) * (2 * offset + 9) := by
            have heq :
                (offset + 7) * (offset + 5) * (2 * offset + 9) =
                  3 * (offset + 6) ^ 2 +
                    (2 * offset ^ 3 + 30 * offset ^ 2 + 142 * offset + 207) := by
              ring
            rw [heq]
            omega
          have hring :
              (offset + 6) * (offset + 4) * (2 * offset + 7) +
                3 * ((offset + 6) * (offset + 3) +
                  (offset + 5) * (offset + 4)) +
                3 * (offset + 6) ^ 2 =
              (offset + 7) * (offset + 5) * (2 * offset + 9) +
                3 * (offset + 5) ^ 2 := by
            ring
          have hleftCancel :
              ((offset + 6) * (offset + 4) * (2 * offset + 7) -
                  3 * (offset + 5) ^ 2) +
                3 * (offset + 5) ^ 2 =
              (offset + 6) * (offset + 4) * (2 * offset + 7) :=
            Nat.sub_add_cancel hleftBound
          have hrightCancel :
              ((offset + 7) * (offset + 5) * (2 * offset + 9) -
                  3 * (offset + 6) ^ 2) +
                3 * (offset + 6) ^ 2 =
              (offset + 7) * (offset + 5) * (2 * offset + 9) :=
            Nat.sub_add_cancel hrightBound
          omega
        rw [hsumRec]
        calc
          3 * (previousSum + 2 * (rowExtra + columnExtra)) =
              3 * previousSum + 3 * (2 * (rowExtra + columnExtra)) := by ring
          _ = ((size - 1) * (size - 3) * (2 * (size - 1) - 5) -
                3 * (size - 2) ^ 2) +
              3 * ((size - 1) * (size - 4) + (size - 2) * (size - 3)) := by
            rw [hpreviousSum, hdoubleExtras]
          _ = size * (size - 2) * (2 * size - 5) -
              3 * (size - 1) ^ 2 := hpure

end FibonacciRibbonKernel
