import FibonacciRibbonKernel.MixedBranching
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card

namespace FibonacciRibbonKernel

open scoped Classical

/-- Equality of counting functions on the manuscript state space `D_n`. -/
def AgreeOnDominant {rank : ℕ}
    (left right : Weight rank → ℕ) : Prop :=
  ∀ state, Dominant state → left state = right state

theorem definingAdjacency_congr_on_dominant
    {rank : ℕ} {left right : Weight rank → ℕ}
    (heq : AgreeOnDominant left right) :
    AgreeOnDominant (definingAdjacency left) (definingAdjacency right) := by
  intro state hstate
  classical
  unfold definingAdjacency
  apply Finset.sum_congr rfl
  intro letter hletter
  by_cases hvalid : PlusValid state letter
  · simp only [hvalid, if_true]
    exact heq _ hvalid
  · simp only [hvalid, if_false]

theorem dualAdjacency_congr_on_dominant
    {rank : ℕ} {left right : Weight rank → ℕ}
    (heq : AgreeOnDominant left right) :
    AgreeOnDominant (dualAdjacency left) (dualAdjacency right) := by
  intro state hstate
  classical
  unfold dualAdjacency
  apply Finset.sum_congr rfl
  intro letter hletter
  by_cases hvalid : MinusValid state letter
  · simp only [hvalid, if_true]
    exact heq _ hvalid
  · simp only [hvalid, if_false]

/-- Repeated defining adjacency, with exponent zero acting as the identity. -/
noncomputable def definingIterate {rank : ℕ} :
    ℕ → (Weight rank → ℕ) → Weight rank → ℕ
  | 0, function => function
  | steps + 1, function => definingAdjacency (definingIterate steps function)

/-- Push one dual step through any number of defining steps on `1`. -/
theorem dual_after_definingIterate_one
    {rank : ℕ} (steps : ℕ) :
    AgreeOnDominant
      (dualAdjacency (definingIterate steps (fun _ : Weight rank => 1)))
      (definingIterate (steps + 1) (fun _ : Weight rank => 1)) := by
  induction steps with
  | zero =>
      intro state hstate
      exact (definingAdjacency_one_eq_dualAdjacency_one hstate).symm
  | succ steps ih =>
      intro state hstate
      calc
        dualAdjacency
            (definingIterate (steps + 1) (fun _ => 1)) state =
          definingAdjacency
            (dualAdjacency (definingIterate steps (fun _ => 1))) state :=
              (definingAdjacency_dualAdjacency_comm hstate
                (definingIterate steps (fun _ => 1))).symm
        _ = definingAdjacency
            (definingIterate (steps + 1) (fun _ => 1)) state :=
              definingAdjacency_congr_on_dominant ih state hstate
        _ = definingIterate (steps + 2) (fun _ => 1) state := rfl

/--
Count valid paths for a literal list of defining (`true`) and dual (`false`)
steps, starting at a specified difference state.
-/
noncomputable def mixedPathCount {rank : ℕ} :
    Weight rank → List Bool → ℕ
  | _, [] => 1
  | state, true :: remaining =>
      definingAdjacency (fun next => mixedPathCount next remaining) state
  | state, false :: remaining =>
      dualAdjacency (fun next => mixedPathCount next remaining) state

/-- Every mixed defining/dual pattern has the pure defining total count. -/
theorem mixedPathCount_eq_definingIterate
    {rank : ℕ} (steps : List Bool) :
    AgreeOnDominant
      (fun state : Weight rank => mixedPathCount state steps)
      (definingIterate steps.length (fun _ : Weight rank => 1)) := by
  induction steps with
  | nil =>
      intro state hstate
      rfl
  | cons step remaining ih =>
      cases step with
      | false =>
          intro state hstate
          calc
            mixedPathCount state (false :: remaining) =
                dualAdjacency
                  (fun next => mixedPathCount next remaining) state := rfl
            _ = dualAdjacency
                  (definingIterate remaining.length (fun _ => 1)) state :=
                dualAdjacency_congr_on_dominant ih state hstate
            _ = definingIterate (remaining.length + 1) (fun _ => 1) state :=
                dual_after_definingIterate_one remaining.length state hstate
            _ = definingIterate (List.length (false :: remaining))
                  (fun _ => 1) state := by simp
      | true =>
          intro state hstate
          calc
            mixedPathCount state (true :: remaining) =
                definingAdjacency
                  (fun next => mixedPathCount next remaining) state := rfl
            _ = definingAdjacency
                  (definingIterate remaining.length (fun _ => 1)) state :=
                definingAdjacency_congr_on_dominant ih state hstate
            _ = definingIterate (List.length (true :: remaining))
                  (fun _ => 1) state := by simp [definingIterate]

/-- Alternating manuscript column kinds, beginning with the rightmost short column. -/
def alternatingSteps : Bool → ℕ → List Bool
  | _, 0 => []
  | shortPosition, count + 1 =>
      shortPosition :: alternatingSteps (!shortPosition) count

theorem alternatingSteps_length (shortPosition : Bool) (count : ℕ) :
    (alternatingSteps shortPosition count).length = count := by
  induction count generalizing shortPosition with
  | zero => rfl
  | succ count ih => simp [alternatingSteps, ih]

/-- The unrestricted manuscript count before imposing the local obstruction. -/
noncomputable def unrestrictedCount (rank columns : ℕ) : ℕ :=
  mixedPathCount (0 : Weight rank) (alternatingSteps true columns)

/-- Operator reduction of the unrestricted mixed walk to a pure defining walk. -/
theorem unrestrictedCount_eq_pureDefiningCount (rank columns : ℕ) :
    unrestrictedCount rank columns =
      definingIterate columns (fun _ => 1) (0 : Weight rank) := by
  unfold unrestrictedCount
  have h := mixedPathCount_eq_definingIterate
    (rank := rank) (alternatingSteps true columns) 0 (dominant_zero rank)
  simpa [alternatingSteps_length] using h

set_option linter.unusedVariables false in
/-- Kernel carrier of a finite pure defining path from a specified state. -/
def DefiningPathFrom {rank : ℕ} (state : Weight rank) : ℕ → Type
  | 0 => PUnit
  | columns + 1 =>
      Σ letter : Fin (rank + 1),
        {tail : DefiningPathFrom (plusState state letter) columns //
          PlusValid state letter}

noncomputable instance definingPathFromFintype
    {rank : ℕ} (state : Weight rank) (columns : ℕ) :
    Fintype (DefiningPathFrom state columns) := by
  induction columns generalizing state with
  | zero =>
      simp only [DefiningPathFrom]
      infer_instance
  | succ columns ih =>
      simp only [DefiningPathFrom]
      letI (letter : Fin (rank + 1)) :
          Fintype (DefiningPathFrom (plusState state letter) columns) :=
        ih (plusState state letter)
      infer_instance

theorem definingIterate_one_eq_card_paths
    {rank : ℕ} (columns : ℕ) (state : Weight rank) :
    definingIterate columns (fun _ : Weight rank => 1) state =
      Fintype.card (DefiningPathFrom state columns) := by
  induction columns generalizing state with
  | zero => simp [definingIterate, DefiningPathFrom]
  | succ columns ih =>
      rw [show definingIterate (columns + 1) (fun _ : Weight rank => 1) state =
        definingAdjacency
          (definingIterate columns (fun _ : Weight rank => 1)) state from rfl]
      classical
      unfold definingAdjacency
      simp_rw [ih]
      rw [show Fintype.card (DefiningPathFrom state (columns + 1)) =
        ∑ letter : Fin (rank + 1),
          Fintype.card
            {tail : DefiningPathFrom (plusState state letter) columns //
              PlusValid state letter} by
        change Fintype.card
            (Σ letter : Fin (rank + 1),
              {tail : DefiningPathFrom (plusState state letter) columns //
                PlusValid state letter}) =
          ∑ letter : Fin (rank + 1),
            Fintype.card
              {tail : DefiningPathFrom (plusState state letter) columns //
                PlusValid state letter}
        exact Fintype.card_sigma]
      apply Finset.sum_congr rfl
      intro letter hletter
      by_cases hvalid : PlusValid state letter
      · simp [hvalid]
      · simp [hvalid]

end FibonacciRibbonKernel
