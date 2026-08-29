import FibonacciRibbonKernel.UnrestrictedParameterWords
import Lean.Elab.Tactic.Omega

namespace FibonacciRibbonKernel

/-- The zero-based forbidden adjacency `(0,last)` at a literal list location. -/
def BadAt (rank : ℕ) (parameters : List (Fin (rank + 1)))
    (location : ℕ) : Prop :=
  parameters[location]? = some 0 ∧
    parameters[location + 1]? = some (Fin.last rank)

/-- All forbidden adjacency locations in a parameter list. -/
noncomputable def badLocations (rank : ℕ)
    (parameters : List (Fin (rank + 1))) : Finset ℕ := by
  classical
  exact (Finset.range (parameters.length - 1)).filter
    (BadAt rank parameters)

theorem mem_badLocations_iff
    (rank : ℕ) (parameters : List (Fin (rank + 1))) (location : ℕ) :
    location ∈ badLocations rank parameters ↔
      location < parameters.length - 1 ∧ BadAt rank parameters location := by
  classical
  simp [badLocations]

theorem badAt_adjacent_impossible
    {rank : ℕ} (hrank : 1 ≤ rank)
    {parameters : List (Fin (rank + 1))} {location : ℕ}
    (hbad : BadAt rank parameters location)
    (hnext : BadAt rank parameters (location + 1)) : False := by
  have heqSome : some (Fin.last rank) = some (0 : Fin (rank + 1)) :=
    hbad.2.symm.trans hnext.1
  have heq : Fin.last rank = (0 : Fin (rank + 1)) := Option.some.inj heqSome
  have hval := congrArg Fin.val heq
  simp at hval
  omega

theorem badLocations_nonAdjacent
    {rank : ℕ} (hrank : 1 ≤ rank)
    (parameters : List (Fin (rank + 1))) :
    NonAdjacentEdges (badLocations rank parameters) := by
  intro location hlocation hnext
  have hbad := (mem_badLocations_iff rank parameters location).mp hlocation |>.2
  have hbadNext :=
    (mem_badLocations_iff rank parameters (location + 1)).mp hnext |>.2
  exact badAt_adjacent_impossible hrank hbad hbadNext

theorem badAt_cons_succ
    (rank : ℕ) (head : Fin (rank + 1))
    (tail : List (Fin (rank + 1))) (location : ℕ) :
    BadAt rank (head :: tail) (location + 1) ↔
      BadAt rank tail location := by
  simp [BadAt]

theorem mem_badLocations_cons_succ
    (rank : ℕ) (head : Fin (rank + 1))
    (tail : List (Fin (rank + 1))) (location : ℕ) :
    location + 1 ∈ badLocations rank (head :: tail) ↔
      location ∈ badLocations rank tail := by
  rw [mem_badLocations_iff, mem_badLocations_iff, badAt_cons_succ]
  simp only [List.length_cons]
  constructor <;> rintro ⟨hbound, hbad⟩ <;> refine ⟨?_, hbad⟩ <;> omega

theorem mem_badLocations_cons_cons_add_two
    (rank : ℕ) (first second : Fin (rank + 1))
    (tail : List (Fin (rank + 1))) (location : ℕ) :
    location + 2 ∈ badLocations rank (first :: second :: tail) ↔
      location ∈ badLocations rank tail := by
  rw [show location + 2 = (location + 1) + 1 by omega]
  rw [mem_badLocations_cons_succ rank first (second :: tail) (location + 1)]
  exact mem_badLocations_cons_succ rank second tail location

theorem zero_mem_badLocations_cons_cons_iff
    (rank : ℕ) (first second : Fin (rank + 1))
    (tail : List (Fin (rank + 1))) :
    0 ∈ badLocations rank (first :: second :: tail) ↔
      first = 0 ∧ second = Fin.last rank := by
  rw [mem_badLocations_iff]
  simp [BadAt]

/-- Actual ribbon objects after imposing the unique local obstruction. -/
def AdmissibleRibbonObject (rank columns : ℕ) :=
  {word : UnrestrictedParameterList rank columns //
    badLocations rank word.parameters = ∅}

noncomputable instance admissibleRibbonObjectFintype (rank columns : ℕ) :
    Fintype (AdmissibleRibbonObject rank columns) := by
  classical
  unfold AdmissibleRibbonObject
  infer_instance

/-- The literal ballot-admissible Fibonacci-ribbon count `b_{n,k}`. -/
noncomputable def ribbonCount (rank columns : ℕ) : ℕ :=
  Fintype.card (AdmissibleRibbonObject rank columns)

/-- Unrestricted words containing every edge of a specified matching. -/
def MatchingIntersection (rank columns edges : ℕ)
    (matching : ActualPathMatching columns edges) :=
  {word : UnrestrictedParameterList rank columns //
    matching.edgePositions ⊆ badLocations rank word.parameters}

noncomputable instance matchingIntersectionFintype
    (rank columns edges : ℕ) (matching : ActualPathMatching columns edges) :
    Fintype (MatchingIntersection rank columns edges matching) := by
  classical
  unfold MatchingIntersection
  infer_instance

end FibonacciRibbonKernel
