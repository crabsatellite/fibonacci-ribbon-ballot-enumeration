import FibonacciRibbonKernel.ColumnWalk
import Lean.Elab.Tactic.Omega

namespace FibonacciRibbonKernel

/-- The increasing full alphabet `0,1,...,rank`. -/
def fullWord (rank : ℕ) : List (Fin (rank + 1)) :=
  List.finRange (rank + 1)

/-- The increasing full alphabet with one letter omitted. -/
def tallWord (rank : ℕ) (omitted : Fin (rank + 1)) :
    List (Fin (rank + 1)) :=
  (fullWord rank).erase omitted

/-- The literal top-to-bottom word read inside a column. -/
def Column.word {rank : ℕ} : Column rank → List (Fin (rank + 1))
  | .singleton letter => [letter]
  | .tall omitted => tallWord rank omitted

/-- Right-end decomposition of the increasing finite alphabet. -/
theorem finRange_eq_castSucc_append_last (rank : ℕ) :
    List.finRange (rank + 1) =
      (List.finRange rank).map Fin.castSucc ++ [Fin.last rank] := by
  apply List.ext_get
  · simp
  · intro index hleft hright
    simp only [List.length_finRange, List.length_append, List.length_map,
      List.length_singleton] at hleft hright
    by_cases hindex : index < rank
    · simp [List.getElem_finRange, hindex]
    · have heq : index = rank := by omega
      subst index
      apply Fin.ext
      simp [List.getElem_finRange]

/-- A singleton `0` followed by the tall column omitting `0` is the full word. -/
theorem singleton_zero_tall_zero_word (rank : ℕ) :
    (Column.singleton (0 : Fin (rank + 1))).word ++
      (Column.tall (0 : Fin (rank + 1))).word = fullWord rank := by
  simp [Column.word, tallWord, fullWord, List.finRange_succ]

/-- The tall column omitting the last letter followed by that letter is full. -/
theorem tall_last_singleton_last_word (rank : ℕ) :
    (Column.tall (Fin.last rank)).word ++
      (Column.singleton (Fin.last rank)).word = fullWord rank := by
  have hnot : Fin.last rank ∉ (List.finRange rank).map Fin.castSucc := by
    intro hmem
    simp only [List.mem_map, List.mem_finRange, true_and] at hmem
    obtain ⟨x, hx⟩ := hmem
    have hval := congrArg Fin.val hx
    simp at hval
    omega
  change tallWord rank (Fin.last rank) ++ [Fin.last rank] = fullWord rank
  unfold tallWord fullWord
  rw [finRange_eq_castSucc_append_last]
  rw [List.erase_append]
  simp [hnot]

/-- Zero-based form of the manuscript parameter reversal `a ↦ n + 1 - a`. -/
def parameterComplement {rank : ℕ} (letter : Fin (rank + 1)) :
    Fin (rank + 1) :=
  letter.rev

theorem parameterComplement_zero (rank : ℕ) :
    parameterComplement (0 : Fin (rank + 1)) = Fin.last rank := by
  simp [parameterComplement]

theorem parameterComplement_last (rank : ℕ) :
    parameterComplement (Fin.last rank) = (0 : Fin (rank + 1)) := by
  simp [parameterComplement]

theorem parameterComplement_involutive (rank : ℕ) :
    Function.Involutive (@parameterComplement rank) := by
  intro letter
  exact Fin.rev_involutive letter

/--
The column determined by one parameter.  `shortPosition = true` is an odd
manuscript position and gives a singleton; `false` gives the complementary
tall column.
-/
def parameterColumn {rank : ℕ}
    (shortPosition : Bool) (parameter : Fin (rank + 1)) : Column rank :=
  if shortPosition then .singleton parameter
  else .tall (parameterComplement parameter)

/--
The forbidden zero-based parameter pair `(0,last)` reads the full increasing
alphabet in either parity.  This is the literal word assertion in the neutral
bad-pair lemma.
-/
theorem badParameterPair_word (rank : ℕ) (shortPosition : Bool) :
    (parameterColumn shortPosition (0 : Fin (rank + 1))).word ++
      (parameterColumn (!shortPosition) (Fin.last rank)).word =
        fullWord rank := by
  cases shortPosition <;>
    simp [parameterColumn, parameterComplement,
      singleton_zero_tall_zero_word, tall_last_singleton_last_word]

end FibonacciRibbonKernel
