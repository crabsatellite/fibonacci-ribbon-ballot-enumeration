import FibonacciRibbonKernel.LocalObstruction
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Lean.Elab.Tactic.Omega

namespace FibonacciRibbonKernel

open scoped Classical

/-- State transition for one defining-representation letter. -/
def plusState {rank : ℕ} (state : Weight rank)
    (letter : Fin (rank + 1)) : Weight rank :=
  state + letterWeight rank letter

/-- State transition for one dual letter, written literally as `-v_y`. -/
def minusState {rank : ℕ} (state : Weight rank)
    (letter : Fin (rank + 1)) : Weight rank :=
  state - letterWeight rank letter

def PlusValid {rank : ℕ} (state : Weight rank)
    (letter : Fin (rank + 1)) : Prop :=
  Dominant (plusState state letter)

def MinusValid {rank : ℕ} (state : Weight rank)
    (letter : Fin (rank + 1)) : Prop :=
  Dominant (minusState state letter)

theorem plus_minus_state_comm
    {rank : ℕ} (state : Weight rank)
    (plusLetter minusLetter : Fin (rank + 1)) :
    plusState (minusState state minusLetter) plusLetter =
      minusState (plusState state plusLetter) minusLetter := by
  funext i
  simp [plusState, minusState, sub_eq_add_neg, add_assoc, add_comm,
    add_left_comm]

set_option linter.unnecessarySeqFocus false in
/--
For distinct letters, a valid `+v_x,-v_y` path is valid in the reverse order.
This is the off-diagonal part of mixed branching.
-/
theorem plus_minus_valid_swap_of_ne
    {rank : ℕ} {state : Weight rank}
    (hstart : Dominant state)
    (plusLetter minusLetter : Fin (rank + 1))
    (hne : plusLetter ≠ minusLetter) :
    (PlusValid state plusLetter ∧
        MinusValid (plusState state plusLetter) minusLetter) ↔
      (MinusValid state minusLetter ∧
        PlusValid (minusState state minusLetter) plusLetter) := by
  constructor
  · rintro ⟨hplus, hend⟩
    have hminus : MinusValid state minusLetter := by
      intro i
      have hs := hstart i
      have hp := hplus i
      have he := hend i
      simp only [plusState, minusState, Pi.add_apply, Pi.sub_apply] at hp he ⊢
      simp only [letterWeight] at hp he ⊢
      split_ifs at hp he ⊢ <;> simp_all <;> omega
    refine ⟨hminus, ?_⟩
    change Dominant (plusState (minusState state minusLetter) plusLetter)
    rw [plus_minus_state_comm]
    exact hend
  · rintro ⟨hminus, hend⟩
    have hplus : PlusValid state plusLetter := by
      intro i
      have hs := hstart i
      have hm := hminus i
      have he := hend i
      simp only [plusState, minusState, Pi.add_apply, Pi.sub_apply] at hm he ⊢
      simp only [letterWeight] at hm he ⊢
      split_ifs at hm he ⊢ <;> simp_all <;> omega
    refine ⟨hplus, ?_⟩
    change Dominant (minusState (plusState state plusLetter) minusLetter)
    rw [← plus_minus_state_comm]
    exact hend

theorem plusValid_zero
    {rank : ℕ} {state : Weight rank} (hstate : Dominant state) :
    PlusValid state (0 : Fin (rank + 1)) :=
  dominant_add_letterWeight_zero hstate

theorem minusValid_last
    {rank : ℕ} {state : Weight rank} (hstate : Dominant state) :
    MinusValid state (Fin.last rank) := by
  have h := dominant_add_tallWeight_last hstate
  simpa [MinusValid, minusState, tallWeight_eq_neg_letterWeight,
    sub_eq_add_neg] using h

theorem plusValid_succ_iff
    {rank : ℕ} {state : Weight rank} (hstate : Dominant state)
    (coordinate : Fin rank) :
    PlusValid state coordinate.succ ↔ 0 < state coordinate := by
  constructor
  · intro hvalid
    have hne : coordinate.succ ≠ coordinate.castSucc := by
      intro h
      have hval := congrArg Fin.val h
      simp at hval
    have hcoord := hvalid coordinate
    simp [plusState, letterWeight, hne] at hcoord
    omega
  · intro hpositive i
    have hi := hstate i
    simp only [plusState, Pi.add_apply]
    simp only [letterWeight]
    split_ifs <;> simp_all <;> omega

theorem minusValid_castSucc_iff
    {rank : ℕ} {state : Weight rank} (hstate : Dominant state)
    (coordinate : Fin rank) :
    MinusValid state coordinate.castSucc ↔ 0 < state coordinate := by
  constructor
  · intro hvalid
    have hne : coordinate.castSucc ≠ coordinate.succ := by
      intro h
      have hval := congrArg Fin.val h
      simp at hval
    have hcoord := hvalid coordinate
    simp [minusState, letterWeight, hne] at hcoord
    omega
  · intro hpositive i
    have hi := hstate i
    simp only [minusState, Pi.sub_apply]
    simp only [letterWeight]
    split_ifs <;> simp_all <;> omega

/-- Cyclic predecessor matching valid defining letters with valid dual letters. -/
def plusToMinusLetter {rank : ℕ} : Fin (rank + 1) → Fin (rank + 1) :=
  Fin.cases (Fin.last rank) (fun coordinate => coordinate.castSucc)

/-- Inverse cyclic successor. -/
def minusToPlusLetter {rank : ℕ} : Fin (rank + 1) → Fin (rank + 1) :=
  Fin.lastCases 0 (fun coordinate => coordinate.succ)

theorem minusToPlus_plusToMinus
    {rank : ℕ} (letter : Fin (rank + 1)) :
    minusToPlusLetter (plusToMinusLetter letter) = letter := by
  refine Fin.cases ?_ (fun coordinate => ?_) letter
  · simp [plusToMinusLetter, minusToPlusLetter]
  · simp [plusToMinusLetter, minusToPlusLetter]

theorem plusToMinus_minusToPlus
    {rank : ℕ} (letter : Fin (rank + 1)) :
    plusToMinusLetter (minusToPlusLetter letter) = letter := by
  refine Fin.lastCases ?_ (fun coordinate => ?_) letter
  · simp [plusToMinusLetter, minusToPlusLetter]
  · simp [plusToMinusLetter, minusToPlusLetter]

def plusMinusLetterEquiv (rank : ℕ) :
    Fin (rank + 1) ≃ Fin (rank + 1) where
  toFun := plusToMinusLetter
  invFun := minusToPlusLetter
  left_inv := minusToPlus_plusToMinus
  right_inv := plusToMinus_minusToPlus

theorem plusValid_iff_minusValid_equiv
    {rank : ℕ} {state : Weight rank} (hstate : Dominant state)
    (letter : Fin (rank + 1)) :
    PlusValid state letter ↔
      MinusValid state (plusMinusLetterEquiv rank letter) := by
  refine Fin.cases ?_ (fun coordinate => ?_) letter
  · change PlusValid state 0 ↔ MinusValid state (Fin.last rank)
    exact ⟨fun _ => minusValid_last hstate, fun _ => plusValid_zero hstate⟩
  · change PlusValid state coordinate.succ ↔
      MinusValid state coordinate.castSucc
    rw [plusValid_succ_iff hstate, minusValid_castSucc_iff hstate]

/-- Literal finite adjacency operator for defining steps. -/
noncomputable def definingAdjacency {rank : ℕ}
    (function : Weight rank → ℕ) (state : Weight rank) : ℕ := by
  classical
  exact ∑ letter : Fin (rank + 1),
    if PlusValid state letter then function (plusState state letter) else 0

/-- Literal finite adjacency operator for dual steps. -/
noncomputable def dualAdjacency {rank : ℕ}
    (function : Weight rank → ℕ) (state : Weight rank) : ℕ := by
  classical
  exact ∑ letter : Fin (rank + 1),
    if MinusValid state letter then function (minusState state letter) else 0

/-- Equal defining and dual outdegrees at every dominant state. -/
theorem definingAdjacency_one_eq_dualAdjacency_one
    {rank : ℕ} {state : Weight rank} (hstate : Dominant state) :
    definingAdjacency (fun _ => 1) state =
      dualAdjacency (fun _ => 1) state := by
  classical
  unfold definingAdjacency dualAdjacency
  apply Fintype.sum_equiv (plusMinusLetterEquiv rank)
  intro letter
  have hvalid := plusValid_iff_minusValid_equiv hstate letter
  by_cases hplus : PlusValid state letter
  · have hminus := hvalid.mp hplus
    simp only [hplus, hminus, if_true]
  · have hminus : ¬ MinusValid state (plusMinusLetterEquiv rank letter) :=
      fun h => hplus (hvalid.mpr h)
    simp only [hplus, hminus, if_false]

noncomputable def definingThenDualTerm {rank : ℕ}
    (function : Weight rank → ℕ) (state : Weight rank)
    (plusLetter minusLetter : Fin (rank + 1)) : ℕ := by
  classical
  exact if PlusValid state plusLetter then
    if MinusValid (plusState state plusLetter) minusLetter then
      function (minusState (plusState state plusLetter) minusLetter)
    else 0
  else 0

noncomputable def dualThenDefiningTerm {rank : ℕ}
    (function : Weight rank → ℕ) (state : Weight rank)
    (plusLetter minusLetter : Fin (rank + 1)) : ℕ := by
  classical
  exact if MinusValid state minusLetter then
    if PlusValid (minusState state minusLetter) plusLetter then
      function (plusState (minusState state minusLetter) plusLetter)
    else 0
  else 0

set_option linter.unnecessarySeqFocus false in
theorem offDiagonal_mixed_term_eq
    {rank : ℕ} {state : Weight rank} (hstate : Dominant state)
    (function : Weight rank → ℕ)
    (plusLetter minusLetter : Fin (rank + 1))
    (hne : plusLetter ≠ minusLetter) :
    definingThenDualTerm function state plusLetter minusLetter =
      dualThenDefiningTerm function state plusLetter minusLetter := by
  classical
  have hswap := plus_minus_valid_swap_of_ne hstate plusLetter minusLetter hne
  unfold definingThenDualTerm dualThenDefiningTerm
  by_cases hp : PlusValid state plusLetter <;>
    by_cases he : MinusValid (plusState state plusLetter) minusLetter <;>
    by_cases hm : MinusValid state minusLetter <;>
    by_cases hr : PlusValid (minusState state minusLetter) plusLetter <;>
    simp_all [plus_minus_state_comm]

theorem definingThenDualTerm_diagonal
    {rank : ℕ} {state : Weight rank} (hstate : Dominant state)
    (function : Weight rank → ℕ) (letter : Fin (rank + 1)) :
    definingThenDualTerm function state letter letter =
      if PlusValid state letter then function state else 0 := by
  classical
  unfold definingThenDualTerm
  by_cases hplus : PlusValid state letter
  · have hreturn :
        minusState (plusState state letter) letter = state := by
      funext i
      simp [plusState, minusState]
    have hminus : MinusValid (plusState state letter) letter := by
      rw [MinusValid, hreturn]
      exact hstate
    simp [hplus, hminus, hreturn]
  · simp [hplus]

theorem dualThenDefiningTerm_diagonal
    {rank : ℕ} {state : Weight rank} (hstate : Dominant state)
    (function : Weight rank → ℕ) (letter : Fin (rank + 1)) :
    dualThenDefiningTerm function state letter letter =
      if MinusValid state letter then function state else 0 := by
  classical
  unfold dualThenDefiningTerm
  by_cases hminus : MinusValid state letter
  · have hreturn :
        plusState (minusState state letter) letter = state := by
      funext i
      simp [plusState, minusState]
    have hplus : PlusValid (minusState state letter) letter := by
      rw [PlusValid, hreturn]
      exact hstate
    simp [hminus, hplus, hreturn]
  · simp [hminus]

theorem mixed_diagonal_sum_eq
    {rank : ℕ} {state : Weight rank} (hstate : Dominant state)
    (function : Weight rank → ℕ) :
    (∑ letter : Fin (rank + 1),
      definingThenDualTerm function state letter letter) =
    ∑ letter : Fin (rank + 1),
      dualThenDefiningTerm function state letter letter := by
  classical
  simp_rw [definingThenDualTerm_diagonal hstate,
    dualThenDefiningTerm_diagonal hstate]
  apply Fintype.sum_equiv (plusMinusLetterEquiv rank)
  intro letter
  have hvalid := plusValid_iff_minusValid_equiv hstate letter
  by_cases hplus : PlusValid state letter
  · have hminus := hvalid.mp hplus
    simp only [hplus, hminus, if_true]
  · have hminus : ¬ MinusValid state (plusMinusLetterEquiv rank letter) :=
      fun h => hplus (hvalid.mpr h)
    simp only [hplus, hminus, if_false]

theorem sum_pair_split_diagonal
    {rank : ℕ} (term : Fin (rank + 1) → Fin (rank + 1) → ℕ) :
    (∑ first, ∑ second, term first second) =
      (∑ letter, term letter letter) +
        ∑ first, ∑ second ∈ Finset.univ.erase first, term first second := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro first hfirst
  rw [← Finset.sum_erase_add (s := Finset.univ)
    (f := term first) (Finset.mem_univ first)]
  exact Nat.add_comm _ _

theorem mixed_offDiagonal_sum_eq
    {rank : ℕ} {state : Weight rank} (hstate : Dominant state)
    (function : Weight rank → ℕ) :
    (∑ first, ∑ second ∈ Finset.univ.erase first,
      definingThenDualTerm function state first second) =
    ∑ first, ∑ second ∈ Finset.univ.erase first,
      dualThenDefiningTerm function state first second := by
  classical
  apply Finset.sum_congr rfl
  intro first hfirst
  apply Finset.sum_congr rfl
  intro second hsecond
  have hne : second ≠ first := Finset.ne_of_mem_erase hsecond
  exact offDiagonal_mixed_term_eq hstate function first second hne.symm

theorem defining_dual_expand
    {rank : ℕ} (function : Weight rank → ℕ) (state : Weight rank) :
    definingAdjacency (dualAdjacency function) state =
      ∑ plusLetter, ∑ minusLetter,
        definingThenDualTerm function state plusLetter minusLetter := by
  classical
  simp [definingAdjacency, dualAdjacency, definingThenDualTerm]

theorem dual_defining_expand
    {rank : ℕ} (function : Weight rank → ℕ) (state : Weight rank) :
    dualAdjacency (definingAdjacency function) state =
      ∑ plusLetter, ∑ minusLetter,
        dualThenDefiningTerm function state plusLetter minusLetter := by
  classical
  simp [definingAdjacency, dualAdjacency, dualThenDefiningTerm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro minusLetter hminusLetter
  by_cases hminus : MinusValid state minusLetter
  · simp [hminus]
  · simp [hminus]

/-- The literal defining and dual adjacency operators commute. -/
theorem definingAdjacency_dualAdjacency_comm
    {rank : ℕ} {state : Weight rank} (hstate : Dominant state)
    (function : Weight rank → ℕ) :
    definingAdjacency (dualAdjacency function) state =
      dualAdjacency (definingAdjacency function) state := by
  rw [defining_dual_expand, dual_defining_expand,
    sum_pair_split_diagonal, sum_pair_split_diagonal,
    mixed_diagonal_sum_eq hstate, mixed_offDiagonal_sum_eq hstate]

end FibonacciRibbonKernel
