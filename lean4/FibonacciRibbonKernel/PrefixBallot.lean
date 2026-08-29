import FibonacciRibbonKernel.NeutralBlock
import Lean.Elab.Tactic.Omega

namespace FibonacciRibbonKernel

open scoped BigOperators

/-- Coordinatewise dominance of a difference state. -/
def Dominant {rank : ℕ} (state : Weight rank) : Prop :=
  ∀ i, 0 ≤ state i

/-- Net weight of the letters `< cutoff` in the increasing full alphabet. -/
def fullPrefixWeight (rank cutoff : ℕ) : Weight rank :=
  ∑ x ∈ Finset.univ.filter (fun x : Fin (rank + 1) => x.val < cutoff),
    letterWeight rank x

/-- Net weight of the letters `< cutoff`, with one specified letter omitted. -/
def tallPrefixWeight
    (rank : ℕ) (omitted : Fin (rank + 1)) (cutoff : ℕ) : Weight rank :=
  ∑ x ∈ Finset.univ.filter
      (fun x : Fin (rank + 1) => x.val < cutoff ∧ x ≠ omitted),
    letterWeight rank x

theorem fullPrefixWeight_apply (rank cutoff : ℕ) (i : Fin rank) :
    fullPrefixWeight rank cutoff i =
      (if i.val < cutoff then 1 else 0) -
        (if i.val + 1 < cutoff then 1 else 0) := by
  classical
  simp [fullPrefixWeight, letterWeight]

theorem fullPrefixWeight_nonnegative (rank cutoff : ℕ) :
    Dominant (fullPrefixWeight rank cutoff) := by
  intro i
  rw [fullPrefixWeight_apply]
  split_ifs <;> omega

theorem dominant_add_fullPrefixWeight
    {rank : ℕ} {state : Weight rank} (hstate : Dominant state) (cutoff : ℕ) :
    Dominant (state + fullPrefixWeight rank cutoff) := by
  intro i
  have hprefix := fullPrefixWeight_nonnegative rank cutoff i
  exact add_nonneg (hstate i) hprefix

theorem tallPrefixWeight_apply
    (rank cutoff : ℕ) (omitted : Fin (rank + 1)) (i : Fin rank) :
    tallPrefixWeight rank omitted cutoff i =
      (if i.val < cutoff ∧ i.castSucc ≠ omitted then 1 else 0) -
        (if i.val + 1 < cutoff ∧ i.succ ≠ omitted then 1 else 0) := by
  classical
  simp [tallPrefixWeight, letterWeight]

theorem tallPrefixWeight_at_end
    (rank : ℕ) (omitted : Fin (rank + 1)) :
    tallPrefixWeight rank omitted (rank + 1) = tallWeight rank omitted := by
  classical
  funext i
  simp [tallPrefixWeight, tallWeight, letterWeight]

/--
Every internal prefix of a tall column is dominant whenever its starting and
final states are dominant.  This is the internal-prefix part of the literal
column-walk lemma.
-/
theorem dominant_add_tallPrefixWeight_of_endpoint
    {rank : ℕ} {state : Weight rank} (omitted : Fin (rank + 1))
    (hstart : Dominant state)
    (hend : Dominant (state + tallWeight rank omitted))
    (cutoff : ℕ) :
    Dominant (state + tallPrefixWeight rank omitted cutoff) := by
  intro i
  rw [Pi.add_apply, tallPrefixWeight_apply]
  by_cases hp : i.val < cutoff ∧ i.castSucc ≠ omitted
  · by_cases hn : i.val + 1 < cutoff ∧ i.succ ≠ omitted
    · simp [hp, hn]
      exact hstart i
    · simp [hp, hn]
      exact add_nonneg (hstart i) (by omega)
  · by_cases hn : i.val + 1 < cutoff ∧ i.succ ≠ omitted
    · have hi : i.val < cutoff :=
        lt_trans (Nat.lt_succ_self i.val) hn.1
      have heq : i.castSucc = omitted := by
        by_contra hne
        exact hp ⟨hi, hne⟩
      subst omitted
      have hne : i.castSucc ≠ i.succ := by
        intro h
        have hval := congrArg Fin.val h
        simp at hval
      have hfinal := hend i
      simp [tallWeight_eq_neg_letterWeight, letterWeight, hne] at hfinal
      simpa [hne, hn] using hfinal
    · simp [hp, hn]
      exact hstart i

end FibonacciRibbonKernel
