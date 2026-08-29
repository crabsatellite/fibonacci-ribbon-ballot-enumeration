import FibonacciRibbonKernel.RegevDomination
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Analysis.Convex.Measure

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set Bornology
open scoped Classical Topology

/-- The last coordinate chart on Matsumoto's traceless hyperplane. -/
noncomputable def tracelessExtend {rank : ℕ}
    (coordinates : Fin rank → ℝ) : Fin (rank + 1) → ℝ :=
  Fin.lastCases (-∑ row, coordinates row) coordinates

@[simp] theorem tracelessExtend_last
    {rank : ℕ} (coordinates : Fin rank → ℝ) :
    tracelessExtend coordinates (Fin.last rank) = -∑ row, coordinates row := by
  simp [tracelessExtend]

@[simp] theorem tracelessExtend_castSucc
    {rank : ℕ} (coordinates : Fin rank → ℝ) (row : Fin rank) :
    tracelessExtend coordinates row.castSucc = coordinates row := by
  simp [tracelessExtend]

theorem tracelessExtend_add {rank : ℕ}
    (left right : Fin rank → ℝ) :
    tracelessExtend (left + right) =
      tracelessExtend left + tracelessExtend right := by
  funext row
  cases row using Fin.lastCases with
  | last =>
      simp [Finset.sum_add_distrib]
      ring
  | cast row => simp

theorem tracelessExtend_smul {rank : ℕ}
    (scalar : ℝ) (coordinates : Fin rank → ℝ) :
    tracelessExtend (scalar • coordinates) =
      scalar • tracelessExtend coordinates := by
  funext row
  cases row using Fin.lastCases with
  | last =>
      simp [Finset.mul_sum]
  | cast row => simp

theorem tracelessExtend_sum {rank : ℕ}
    (coordinates : Fin rank → ℝ) :
    ∑ row, tracelessExtend coordinates row = 0 := by
  rw [Fin.sum_univ_castSucc, tracelessExtend_last]
  simp

theorem continuous_tracelessExtend_apply
    {rank : ℕ} (row : Fin (rank + 1)) :
    Continuous (fun coordinates : Fin rank → ℝ =>
      tracelessExtend coordinates row) := by
  cases row using Fin.lastCases with
  | last =>
      simp only [tracelessExtend_last]
      fun_prop
  | cast row =>
      simp only [tracelessExtend_castSucc]
      fun_prop

/-- Ordered chamber in the `d-1` coordinate chart of the traceless
hyperplane, with `d=rank+1`. -/
def regevChamber (rank : ℕ) : Set (Fin rank → ℝ) :=
  {coordinates | Antitone (tracelessExtend coordinates)}

theorem regevChamber_mem_iff {rank : ℕ}
    (coordinates : Fin rank → ℝ) :
    coordinates ∈ regevChamber rank ↔
      ∀ row next : Fin (rank + 1), row ≤ next →
        tracelessExtend coordinates next ≤ tracelessExtend coordinates row :=
  Iff.rfl

theorem regevChamber_convex (rank : ℕ) :
    Convex ℝ (regevChamber rank) := by
  intro left hleft right hright leftWeight rightWeight
    hleftWeight hrightWeight hweights
  rw [regevChamber_mem_iff] at hleft hright ⊢
  intro row next hrowNext
  rw [tracelessExtend_add, tracelessExtend_smul,
    tracelessExtend_smul]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (hleft row next hrowNext) hleftWeight)
    (mul_le_mul_of_nonneg_left (hright row next hrowNext) hrightWeight)

theorem regevChamber_isClosed (rank : ℕ) :
    IsClosed (regevChamber rank) := by
  have hhalfspace (row next : Fin (rank + 1)) :
      IsClosed {coordinates : Fin rank → ℝ |
        tracelessExtend coordinates next ≤ tracelessExtend coordinates row} :=
    isClosed_le (continuous_tracelessExtend_apply next)
      (continuous_tracelessExtend_apply row)
  have hrepresentation : regevChamber rank =
      ⋂ row : Fin (rank + 1), ⋂ next : Fin (rank + 1),
        ⋂ (_h : row ≤ next),
          {coordinates : Fin rank → ℝ |
            tracelessExtend coordinates next ≤
              tracelessExtend coordinates row} := by
    ext coordinates
    simp only [regevChamber, Set.mem_setOf_eq, Set.mem_iInter]
    exact Iff.rfl
  rw [hrepresentation]
  exact isClosed_iInter fun row =>
    isClosed_iInter fun next =>
      isClosed_iInter fun h => hhalfspace row next

def regevTruncatedChamber (rank : ℕ) (radius : ℝ) :
    Set (Fin rank → ℝ) :=
  regevChamber rank ∩ Metric.closedBall 0 radius

theorem regevTruncatedChamber_convex (rank : ℕ) (radius : ℝ) :
    Convex ℝ (regevTruncatedChamber rank radius) :=
  (regevChamber_convex rank).inter (convex_closedBall 0 radius)

theorem regevTruncatedChamber_isClosed (rank : ℕ) (radius : ℝ) :
    IsClosed (regevTruncatedChamber rank radius) :=
  (regevChamber_isClosed rank).inter Metric.isClosed_closedBall

theorem regevTruncatedChamber_isBounded (rank : ℕ) (radius : ℝ) :
    Bornology.IsBounded (regevTruncatedChamber rank radius) :=
  (Metric.isBounded_closedBall.subset inter_subset_right)

theorem regevTruncatedChamber_measurableSet (rank : ℕ) (radius : ℝ) :
    MeasurableSet (regevTruncatedChamber rank radius) :=
  (regevTruncatedChamber_isClosed rank radius).measurableSet

theorem regevTruncatedChamber_null_frontier (rank : ℕ) (radius : ℝ) :
    volume (frontier (regevTruncatedChamber rank radius)) = 0 :=
  (regevTruncatedChamber_convex rank radius).addHaar_frontier volume

end FibonacciRibbonKernel
