import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Lean.Elab.Tactic.Omega

namespace FibonacciRibbonKernel

open scoped Classical

/-!
# Young-lattice shapes for the RSK growth diagram

Rows are stored at one fixed sufficient height.  The local growth rule only
uses the operations in this file: add one outer-corner cell, commute two
distinct additions, and bump a repeated addition to the next row.
-/

structure GrowthShape (height : ℕ) where
  rows : Fin height → ℕ
  antitone : ∀ upper lower : Fin height,
    lower.val = upper.val + 1 → rows lower ≤ rows upper

noncomputable instance (height : ℕ) : DecidableEq (GrowthShape height) := by
  classical
  exact Classical.decEq _

@[ext] theorem GrowthShape.ext
    {height : ℕ} {left right : GrowthShape height}
    (hrows : left.rows = right.rows) : left = right := by
  cases left
  cases right
  simp_all

def GrowthShape.empty (height : ℕ) : GrowthShape height where
  rows := fun _ => 0
  antitone := by simp

def GrowthShape.card {height : ℕ} (shape : GrowthShape height) : ℕ :=
  ∑ row, shape.rows row

theorem GrowthShape.rows_antitone
    {height : ℕ} (shape : GrowthShape height)
    (upper lower : Fin height) (hle : upper.val ≤ lower.val) :
    shape.rows lower ≤ shape.rows upper := by
  let P : (value : ℕ) → upper.val ≤ value → Prop := fun value _ =>
    ∀ hvalue : value < height,
      shape.rows ⟨value, hvalue⟩ ≤ shape.rows upper
  have hbase : P upper.val (by omega) := by
    intro hvalue
    have heq : (⟨upper.val, hvalue⟩ : Fin height) = upper := Fin.ext rfl
    rw [heq]
  have hstep : ∀ value (hupper : upper.val ≤ value),
      P value hupper → P (value + 1) (by omega) := by
    intro value hupper hinduction hnext
    have hvalue : value < height := by omega
    have hadjacent := shape.antitone
      ⟨value, hvalue⟩ ⟨value + 1, hnext⟩ rfl
    exact hadjacent.trans (hinduction hvalue)
  have hall : P lower.val hle :=
    Nat.le_induction (P := P) hbase hstep lower.val hle
  exact hall lower.isLt

abbrev GrowthCell {height : ℕ} (shape : GrowthShape height) :=
  Σ row : Fin height, Fin (shape.rows row)

theorem GrowthShape.card_growthCell
    {height : ℕ} (shape : GrowthShape height) :
    Fintype.card (GrowthCell shape) = shape.card := by
  unfold GrowthCell GrowthShape.card
  rw [Fintype.card_sigma]
  simp

theorem GrowthShape.eq_empty_of_card_eq_zero
    {height : ℕ} (shape : GrowthShape height) (hcard : shape.card = 0) :
    shape = GrowthShape.empty height := by
  apply GrowthShape.ext
  funext row
  have hrow : shape.rows row ≤ shape.card := by
    have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin height))
      shape.rows (Finset.mem_univ row)
    unfold GrowthShape.card
    omega
  simp [GrowthShape.empty]
  omega

def GrowthShape.Addable
    {height : ℕ} (shape : GrowthShape height) (row : Fin height) : Prop :=
  row.val = 0 ∨
    ∀ previous : Fin height,
      previous.val + 1 = row.val → shape.rows row < shape.rows previous

theorem GrowthShape.addable_zero
    {height : ℕ} (shape : GrowthShape (height + 1)) :
    shape.Addable 0 := by
  left
  rfl

theorem GrowthShape.addable_row_le_card
    {height : ℕ} (shape : GrowthShape height) (row : Fin height)
    (hadd : shape.Addable row) :
    row.val ≤ shape.card := by
  by_cases hzero : row.val = 0
  · omega
  · have hrowBound := row.isLt
    let previous : Fin height := ⟨row.val - 1, by omega⟩
    have hprevious : shape.rows row < shape.rows previous := by
      exact (Or.resolve_left hadd hzero) previous (by simp [previous]; omega)
    let embed : Fin row.val → GrowthCell shape := fun index => by
      have hindexBound := index.isLt
      let rowIndex : Fin height := ⟨index.val, by omega⟩
      have hanti : shape.rows previous ≤ shape.rows rowIndex := by
        apply shape.rows_antitone rowIndex previous
        simp [rowIndex, previous]
        omega
      have hpositive : 0 < shape.rows rowIndex := by omega
      exact ⟨rowIndex, ⟨0, hpositive⟩⟩
    have hinjective : Function.Injective embed := by
      intro left right heq
      have hrow := congrArg (fun cell : GrowthCell shape => cell.1.val) heq
      exact Fin.ext hrow
    have hcard := Fintype.card_le_of_injective embed hinjective
    rw [shape.card_growthCell] at hcard
    simpa using hcard

noncomputable def GrowthShape.add
    {height : ℕ} (shape : GrowthShape height) (row : Fin height)
    (hadd : shape.Addable row) : GrowthShape height where
  rows := fun index => if index = row then shape.rows index + 1 else shape.rows index
  antitone := by
    intro upper lower hadjacent
    by_cases hupper : upper = row
    · have hlower : lower ≠ row := by
        intro hlower
        have := congrArg Fin.val (hlower.trans hupper.symm)
        omega
      have hbase := shape.antitone upper lower hadjacent
      have hbase' : shape.rows lower ≤ shape.rows row := by
        simpa only [hupper] using hbase
      simp only [hupper, hlower, if_true, if_false]
      exact Nat.le_succ_of_le hbase'
    · by_cases hlower : lower = row
      · have hrowPos : 0 < row.val := by
          have hval := congrArg Fin.val hlower
          omega
        have hadd' := Or.resolve_left hadd (by omega)
        have hbase : shape.rows row < shape.rows upper := by
          apply hadd' upper
          have hval := congrArg Fin.val hlower
          omega
        simp only [hupper, hlower, if_true, if_false]
        simpa only [hlower] using (Nat.succ_le_iff.mpr hbase)
      · simp only [hupper, hlower, if_false]
        exact shape.antitone upper lower hadjacent

@[simp] theorem GrowthShape.add_rows_same
    {height : ℕ} (shape : GrowthShape height) (row : Fin height)
    (hadd : shape.Addable row) :
    (shape.add row hadd).rows row = shape.rows row + 1 := by
  simp [GrowthShape.add]

theorem GrowthShape.add_rows_ne
    {height : ℕ} (shape : GrowthShape height) (row index : Fin height)
    (hadd : shape.Addable row) (hne : index ≠ row) :
    (shape.add row hadd).rows index = shape.rows index := by
  simp [GrowthShape.add, hne]

@[simp] theorem GrowthShape.card_add
    {height : ℕ} (shape : GrowthShape height) (row : Fin height)
    (hadd : shape.Addable row) :
    (shape.add row hadd).card = shape.card + 1 := by
  unfold GrowthShape.card GrowthShape.add
  calc
    (∑ index : Fin height,
        if index = row then shape.rows index + 1 else shape.rows index) =
        ∑ index : Fin height,
          (shape.rows index + if index = row then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro index hindex
      by_cases heq : index = row <;> simp [heq]
    _ = (∑ index : Fin height, shape.rows index) +
          ∑ index : Fin height, if index = row then 1 else 0 := by
      rw [Finset.sum_add_distrib]
    _ = (∑ index : Fin height, shape.rows index) + 1 := by
      rw [Finset.sum_ite_eq']
      simp

theorem GrowthShape.add_ne
    {height : ℕ} (shape : GrowthShape height) (row : Fin height)
    (hadd : shape.Addable row) :
    shape.add row hadd ≠ shape := by
  intro heq
  have hrow := congrArg (fun value : GrowthShape height => value.rows row) heq
  simp at hrow

theorem GrowthShape.add_injective_row
    {height : ℕ} (shape : GrowthShape height)
    {left right : Fin height}
    (hleft : shape.Addable left) (hright : shape.Addable right)
    (heq : shape.add left hleft = shape.add right hright) :
    left = right := by
  by_contra hne
  have hvalue := congrArg
    (fun value : GrowthShape height => value.rows left) heq
  rw [shape.add_rows_same, shape.add_rows_ne right left hright hne] at hvalue
  omega

theorem GrowthShape.addable_after_add_of_ne
    {height : ℕ} (shape : GrowthShape height)
    (first second : Fin height)
    (hfirst : shape.Addable first) (hsecond : shape.Addable second)
  (hne : second ≠ first) :
    (shape.add first hfirst).Addable second := by
  by_cases hzero : second.val = 0
  · exact Or.inl hzero
  · right
    intro previous hprevious
    have hbase := (Or.resolve_left hsecond hzero) previous hprevious
    have hfirstSecond : first ≠ second := Ne.symm hne
    have hsecondUnchanged :
        (shape.add first hfirst).rows second = shape.rows second :=
      shape.add_rows_ne first second hfirst hne
    by_cases hfirstPrevious : first = previous
    · have hpreviousRaised :
          (shape.add first hfirst).rows previous = shape.rows previous + 1 := by
        rw [← hfirstPrevious]
        exact shape.add_rows_same first hfirst
      rw [hsecondUnchanged, hpreviousRaised]
      omega
    · have hpreviousUnchanged :
          (shape.add first hfirst).rows previous = shape.rows previous :=
        shape.add_rows_ne first previous hfirst (Ne.symm hfirstPrevious)
      rw [hsecondUnchanged, hpreviousUnchanged]
      exact hbase

theorem GrowthShape.add_comm
    {height : ℕ} (shape : GrowthShape height)
    (first second : Fin height)
    (hfirst : shape.Addable first) (hsecond : shape.Addable second)
    (hne : first ≠ second) :
    (shape.add first hfirst).add second
        (shape.addable_after_add_of_ne first second hfirst hsecond (Ne.symm hne)) =
      (shape.add second hsecond).add first
        (shape.addable_after_add_of_ne second first hsecond hfirst hne) := by
  apply GrowthShape.ext
  funext row
  simp only [GrowthShape.add]
  have hsecondFirst : second ≠ first := Ne.symm hne
  by_cases hrowFirst : row = first <;>
    by_cases hrowSecond : row = second <;>
      simp [hrowFirst, hrowSecond, hne, hsecondFirst]

theorem GrowthShape.next_addable_after_same
    {height : ℕ} (shape : GrowthShape height) (row : Fin height)
    (hadd : shape.Addable row) (hnext : row.val + 1 < height) :
    (shape.add row hadd).Addable ⟨row.val + 1, hnext⟩ := by
  right
  intro previous hprevious
  have hpreviousEq : previous = row := by
    have hpreviousVal : previous.val + 1 = row.val + 1 := by
      simpa only using hprevious
    apply Fin.ext
    omega
  subst previous
  have hne : (⟨row.val + 1, hnext⟩ : Fin height) ≠ row := by
    intro heq
    have := congrArg Fin.val heq
    simp at this
  rw [shape.add_rows_ne row ⟨row.val + 1, hnext⟩ hadd hne,
    shape.add_rows_same]
  have hanti : shape.rows ⟨row.val + 1, hnext⟩ ≤ shape.rows row :=
    shape.antitone row ⟨row.val + 1, hnext⟩ (by rfl)
  omega

def GrowthShape.Removable
    {height : ℕ} (shape : GrowthShape height) (row : Fin height) : Prop :=
  0 < shape.rows row ∧
    ∀ next : Fin height, next.val = row.val + 1 →
      shape.rows next < shape.rows row

noncomputable def GrowthShape.remove
    {height : ℕ} (shape : GrowthShape height) (row : Fin height)
    (hremove : shape.Removable row) : GrowthShape height where
  rows := fun index => if index = row then shape.rows index - 1 else shape.rows index
  antitone := by
    intro upper lower hadjacent
    by_cases hupper : upper = row
    · have hlower : lower ≠ row := by
        intro hlower
        have hvalue := congrArg Fin.val (hlower.trans hupper.symm)
        omega
      have hstrict : shape.rows lower < shape.rows row := by
        exact hremove.2 lower (by
          have hvalue := congrArg Fin.val hupper
          omega)
      have hpositive := hremove.1
      simp only [hupper, hlower, if_true, if_false]
      omega
    · by_cases hlower : lower = row
      · have hbase := shape.antitone upper lower hadjacent
        have hbase' : shape.rows row ≤ shape.rows upper := by
          simpa only [hlower] using hbase
        simp only [hupper, hlower, if_true, if_false]
        omega
      · simp only [hupper, hlower, if_false]
        exact shape.antitone upper lower hadjacent

@[simp] theorem GrowthShape.remove_rows_same
    {height : ℕ} (shape : GrowthShape height) (row : Fin height)
    (hremove : shape.Removable row) :
    (shape.remove row hremove).rows row = shape.rows row - 1 := by
  simp [GrowthShape.remove]

theorem GrowthShape.remove_rows_ne
    {height : ℕ} (shape : GrowthShape height) (row index : Fin height)
    (hremove : shape.Removable row) (hne : index ≠ row) :
    (shape.remove row hremove).rows index = shape.rows index := by
  simp [GrowthShape.remove, hne]

theorem GrowthShape.removable_add
    {height : ℕ} (shape : GrowthShape height) (row : Fin height)
    (hadd : shape.Addable row) :
    (shape.add row hadd).Removable row := by
  constructor
  · rw [shape.add_rows_same]
    omega
  · intro next hnext
    have hne : next ≠ row := by
      intro heq
      have hvalue := congrArg Fin.val heq
      omega
    rw [shape.add_rows_ne row next hadd hne, shape.add_rows_same]
    have hbase := shape.antitone row next hnext
    omega

@[simp] theorem GrowthShape.remove_add
    {height : ℕ} (shape : GrowthShape height) (row : Fin height)
    (hadd : shape.Addable row) :
    (shape.add row hadd).remove row (shape.removable_add row hadd) = shape := by
  apply GrowthShape.ext
  funext index
  by_cases heq : index = row
  · subst index
    rw [GrowthShape.remove_rows_same, GrowthShape.add_rows_same]
    omega
  · rw [GrowthShape.remove_rows_ne _ row index _ heq,
      GrowthShape.add_rows_ne _ row index hadd heq]

theorem GrowthShape.add_cancel
    {height : ℕ} (left right : GrowthShape height) (row : Fin height)
    (hleft : left.Addable row) (hright : right.Addable row)
    (heq : left.add row hleft = right.add row hright) :
    left = right := by
  apply GrowthShape.ext
  funext index
  have hrows := congrArg (fun shape : GrowthShape height => shape.rows index) heq
  by_cases hindex : index = row
  · subst index
    rw [left.add_rows_same, right.add_rows_same] at hrows
    omega
  · rw [left.add_rows_ne row index hleft hindex,
      right.add_rows_ne row index hright hindex] at hrows
    exact hrows

theorem GrowthShape.add_congr
    {height : ℕ} {left right : GrowthShape height}
    (hbase : left = right) (row : Fin height)
    (hleft : left.Addable row) (hright : right.Addable row) :
    left.add row hleft = right.add row hright := by
  subst right
  rfl

theorem GrowthShape.add_congr_rows
    {height : ℕ} {left right : GrowthShape height}
    (hbase : left = right) (leftRow rightRow : Fin height)
    (hrow : leftRow = rightRow)
    (hleft : left.Addable leftRow) (hright : right.Addable rightRow) :
    left.add leftRow hleft = right.add rightRow hright := by
  subst right
  subst rightRow
  rfl

theorem GrowthShape.remove_addable
    {height : ℕ} (shape : GrowthShape height) (row : Fin height)
    (hremove : shape.Removable row) :
    (shape.remove row hremove).Addable row := by
  by_cases hzero : row.val = 0
  · exact Or.inl hzero
  · right
    intro previous hprevious
    have hpreviousNe : previous ≠ row := by
      intro heq
      have hvalue := congrArg Fin.val heq
      omega
    rw [shape.remove_rows_same,
      shape.remove_rows_ne row previous hremove hpreviousNe]
    have hbase : shape.rows row ≤ shape.rows previous := by
      apply shape.rows_antitone previous row
      omega
    have hpositive := hremove.1
    omega

@[simp] theorem GrowthShape.add_remove
    {height : ℕ} (shape : GrowthShape height) (row : Fin height)
    (hremove : shape.Removable row) :
    (shape.remove row hremove).add row (shape.remove_addable row hremove) = shape := by
  apply GrowthShape.ext
  funext index
  by_cases heq : index = row
  · subst index
    rw [GrowthShape.add_rows_same, GrowthShape.remove_rows_same]
    have hpositive := hremove.1
    omega
  · rw [GrowthShape.add_rows_ne _ row index _ heq,
      GrowthShape.remove_rows_ne _ row index hremove heq]

theorem GrowthShape.removable_previous_of_addable
    {height : ℕ} (shape : GrowthShape height) (row : Fin height)
    (hadd : shape.Addable row) (hpositive : 0 < row.val) :
    shape.Removable ⟨row.val - 1, by omega⟩ := by
  let previous : Fin height := ⟨row.val - 1, by omega⟩
  have hstrict : shape.rows row < shape.rows previous :=
    (Or.resolve_left hadd (by omega)) previous (by simp [previous]; omega)
  constructor
  · change 0 < shape.rows previous
    omega
  · intro next hnext
    have hnextEq : next = row := by
      change next.val = row.val - 1 + 1 at hnext
      apply Fin.ext
      omega
    simpa [hnextEq] using hstrict

theorem GrowthShape.removable_of_add_eq_add_of_ne
    {height : ℕ} (left right : GrowthShape height)
    (leftRow rightRow : Fin height)
    (hleft : left.Addable leftRow) (hright : right.Addable rightRow)
    (hne : leftRow ≠ rightRow)
    (heq : left.add leftRow hleft = right.add rightRow hright) :
    left.Removable rightRow := by
  have hat := congrArg
    (fun shape : GrowthShape height => shape.rows rightRow) heq
  rw [left.add_rows_ne leftRow rightRow hleft (Ne.symm hne),
    right.add_rows_same] at hat
  constructor
  · omega
  · intro next hnext
    have hnextRight : next ≠ rightRow := by
      intro heqNext
      have hvalue := congrArg Fin.val heqNext
      omega
    have hrightAnti := right.antitone rightRow next hnext
    have hnextEq := congrArg
      (fun shape : GrowthShape height => shape.rows next) heq
    by_cases hnextLeft : next = leftRow
    · have hleftNext :
          (left.add leftRow hleft).rows next = left.rows next + 1 := by
        rw [hnextLeft]
        exact left.add_rows_same leftRow hleft
      rw [hleftNext,
        right.add_rows_ne rightRow next hright hnextRight] at hnextEq
      omega
    · rw [left.add_rows_ne leftRow next hleft hnextLeft,
        right.add_rows_ne rightRow next hright hnextRight] at hnextEq
      omega

theorem GrowthShape.distinct_diamond_predecessor
    {height : ℕ} (left right : GrowthShape height)
    (leftRow rightRow : Fin height)
    (hleft : left.Addable leftRow) (hright : right.Addable rightRow)
    (hne : leftRow ≠ rightRow)
    (heq : left.add leftRow hleft = right.add rightRow hright) :
    let hremoveLeft := left.removable_of_add_eq_add_of_ne right
      leftRow rightRow hleft hright hne heq
    let hremoveRight := right.removable_of_add_eq_add_of_ne left
      rightRow leftRow hright hleft (Ne.symm hne) heq.symm
    left.remove rightRow hremoveLeft = right.remove leftRow hremoveRight := by
  dsimp
  let hremoveLeft := left.removable_of_add_eq_add_of_ne right
    leftRow rightRow hleft hright hne heq
  let hremoveRight := right.removable_of_add_eq_add_of_ne left
    rightRow leftRow hright hleft (Ne.symm hne) heq.symm
  apply GrowthShape.ext
  funext index
  have hrows := congrArg (fun shape : GrowthShape height => shape.rows index) heq
  by_cases hindexLeft : index = leftRow
  · subst index
    have hleftRight : leftRow ≠ rightRow := hne
    rw [left.remove_rows_ne rightRow leftRow hremoveLeft hleftRight,
      right.remove_rows_same]
    rw [
      left.add_rows_same,
      right.add_rows_ne rightRow leftRow hright hleftRight] at hrows
    have hpositive := hremoveRight.1
    omega
  · by_cases hindexRight : index = rightRow
    · subst index
      have hrightLeft : rightRow ≠ leftRow := Ne.symm hne
      rw [left.remove_rows_same,
        right.remove_rows_ne leftRow rightRow hremoveRight hrightLeft]
      rw [
        left.add_rows_ne leftRow rightRow hleft hrightLeft,
        right.add_rows_same] at hrows
      have hpositive := hremoveLeft.1
      omega
    · rw [left.remove_rows_ne rightRow index hremoveLeft hindexRight,
        right.remove_rows_ne leftRow index hremoveRight hindexLeft]
      rw [
        left.add_rows_ne leftRow index hleft hindexLeft,
        right.add_rows_ne rightRow index hright hindexRight] at hrows
      exact hrows

end FibonacciRibbonKernel
