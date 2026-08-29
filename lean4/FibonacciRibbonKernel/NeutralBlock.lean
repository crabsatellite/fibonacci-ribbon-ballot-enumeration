import FibonacciRibbonKernel.Basic

namespace FibonacciRibbonKernel

open scoped BigOperators

/-- Every difference coordinate returns to its starting value after `0,1,...,rank`. -/
theorem fullBlockWeight_eq_zero (rank : ℕ) :
    fullBlockWeight rank = 0 := by
  classical
  funext i
  simp only [fullBlockWeight, Fintype.sum_apply, Pi.zero_apply]
  simp [letterWeight]

/-- Omitting one letter from the full block gives the negative of its letter weight. -/
theorem tallWeight_eq_neg_letterWeight (rank : ℕ) (omitted : Fin (rank + 1)) :
    tallWeight rank omitted = -letterWeight rank omitted := by
  classical
  have hsplit := Finset.sum_erase_add (s := Finset.univ)
    (f := letterWeight rank) (Finset.mem_univ omitted)
  rw [← tallWeight, ← fullBlockWeight, fullBlockWeight_eq_zero] at hsplit
  exact eq_neg_of_add_eq_zero_left hsplit

/-- A singleton followed by the complementary tall column is endpoint-neutral. -/
theorem singleton_tall_neutral (rank : ℕ) (letter : Fin (rank + 1)) :
    letterWeight rank letter + tallWeight rank letter = 0 := by
  rw [tallWeight_eq_neg_letterWeight]
  exact add_neg_cancel _

/-- A tall column followed by its omitted singleton is endpoint-neutral. -/
theorem tall_singleton_neutral (rank : ℕ) (letter : Fin (rank + 1)) :
    tallWeight rank letter + letterWeight rank letter = 0 := by
  rw [tallWeight_eq_neg_letterWeight]
  exact neg_add_cancel _

/-- Odd-position bad pair: singleton `0`, then the tall column omitting `0`. -/
theorem oddBadPair_neutral (rank : ℕ) :
    letterWeight rank 0 + tallWeight rank 0 = 0 :=
  singleton_tall_neutral rank 0

/-- Even-position bad pair: the tall column omitting the last letter, then that singleton. -/
theorem evenBadPair_neutral (rank : ℕ) :
    tallWeight rank (Fin.last rank) + letterWeight rank (Fin.last rank) = 0 :=
  tall_singleton_neutral rank (Fin.last rank)

end FibonacciRibbonKernel
