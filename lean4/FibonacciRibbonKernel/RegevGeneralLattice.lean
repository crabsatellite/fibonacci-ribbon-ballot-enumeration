import FibonacciRibbonKernel.RegevChamberExtension

namespace FibonacciRibbonKernel

open Filter
open scoped Classical Topology

noncomputable def generalRegevScale (rank size : ℕ) : ℝ :=
  Real.sqrt ((size : ℝ) / (rank + 1 : ℝ))

noncomputable def generalRegevMesh (rank size : ℕ) : ℕ :=
  ⌊generalRegevScale rank size⌋₊

def generalRegevCenterFloor (rank size : ℕ) : ℕ :=
  size / (rank + 1)

noncomputable def generalRegevCenterFraction (rank size : ℕ) : ℝ :=
  (size % (rank + 1) : ℕ) / (rank + 1 : ℝ)

noncomputable def generalRegevShift (rank size : ℕ) : ℝ :=
  -generalRegevCenterFraction rank size / generalRegevScale rank size

def generalShapeIntegerCoordinates
    {rank size : ℕ} (shape : BoundedPartition rank size) :
    Fin rank → ℤ :=
  fun row => (shape.1 row.castSucc).val - generalRegevCenterFloor rank size

noncomputable def generalAffineLatticePoint
    (rank size : ℕ) (coordinates : Fin rank → ℤ) :
    Fin rank → ℝ :=
  fun row => (coordinates row : ℝ) / generalRegevScale rank size +
    generalRegevShift rank size

theorem generalRegevCenterFraction_nonneg (rank size : ℕ) :
    0 ≤ generalRegevCenterFraction rank size := by
  unfold generalRegevCenterFraction
  positivity

theorem generalRegevCenterFraction_lt_one (rank size : ℕ) :
    generalRegevCenterFraction rank size < 1 := by
  unfold generalRegevCenterFraction
  have hmod : size % (rank + 1) < rank + 1 :=
    Nat.mod_lt _ (Nat.succ_pos rank)
  exact (div_lt_one (by positivity : (0 : ℝ) < rank + 1)).2
    (by exact_mod_cast hmod)

theorem generalRegevCenter_decompose (rank size : ℕ) :
    (size : ℝ) / (rank + 1 : ℝ) =
      generalRegevCenterFloor rank size +
        generalRegevCenterFraction rank size := by
  unfold generalRegevCenterFloor generalRegevCenterFraction
  have hdimension : rank + 1 ≠ 0 := Nat.succ_ne_zero rank
  have hdivision := Nat.div_add_mod size (rank + 1)
  field_simp
  exact_mod_cast hdivision.symm

theorem generalRegevScale_pos
    {rank size : ℕ} (hsize : 1 ≤ size) :
    0 < generalRegevScale rank size := by
  unfold generalRegevScale
  apply Real.sqrt_pos.2
  positivity

theorem generalRegevLocalScale_eq_inverse
    {rank size : ℕ} (hsize : 1 ≤ size) :
    Real.sqrt ((rank + 1 : ℝ) / (size : ℝ)) =
      (generalRegevScale rank size)⁻¹ := by
  have hfirstNonneg : 0 ≤ (rank + 1 : ℝ) / (size : ℝ) := by
    positivity
  have hmul :
      Real.sqrt ((rank + 1 : ℝ) / (size : ℝ)) *
          generalRegevScale rank size = 1 := by
    unfold generalRegevScale
    rw [← Real.sqrt_mul hfirstNonneg]
    have hinside :
        (rank + 1 : ℝ) / (size : ℝ) *
            ((size : ℝ) / (rank + 1 : ℝ)) = 1 := by
      field_simp
    rw [hinside, Real.sqrt_one]
  exact eq_inv_of_mul_eq_one_left hmul

theorem generalShapePoint_eq_affineLatticePoint
    {rank size : ℕ} (hsize : 1 ≤ size)
    (shape : BoundedPartition rank size) :
    generalShapePoint shape =
      generalAffineLatticePoint rank size
        (generalShapeIntegerCoordinates shape) := by
  funext row
  unfold generalShapePoint generalAffineLatticePoint
  unfold generalShapeIntegerCoordinates generalRegevShift
  unfold regevCenteredRow
  rw [generalRegevLocalScale_eq_inverse hsize]
  rw [generalRegevCenter_decompose rank size]
  push_cast
  field_simp [generalRegevScale_pos hsize |>.ne']
  ring

theorem generalRegevScale_tendsto_atTop (rank : ℕ) :
    Tendsto (fun size : ℕ => generalRegevScale rank size) atTop atTop := by
  unfold generalRegevScale
  apply Real.tendsto_sqrt_atTop.comp
  exact tendsto_natCast_atTop_atTop.atTop_div_const (by positivity)

theorem generalRegevMesh_tendsto_atTop (rank : ℕ) :
    Tendsto (fun size : ℕ => generalRegevMesh rank size) atTop atTop := by
  unfold generalRegevMesh
  exact (tendsto_nat_floor_atTop (α := ℝ)).comp
    (generalRegevScale_tendsto_atTop rank)

theorem generalRegevMesh_div_scale_tendsto_one (rank : ℕ) :
    Tendsto
      (fun size : ℕ =>
        (generalRegevMesh rank size : ℝ) /
          generalRegevScale rank size)
      atTop (nhds 1) := by
  exact tendsto_nat_floor_div_atTop.comp
    (generalRegevScale_tendsto_atTop rank)

theorem generalRegevShift_tendsto_zero (rank : ℕ) :
    Tendsto (fun size : ℕ => generalRegevShift rank size)
      atTop (nhds 0) := by
  have hinverse : Tendsto
      (fun size : ℕ => (generalRegevScale rank size)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (generalRegevScale_tendsto_atTop rank)
  have hzero : Tendsto
      (fun size : ℕ =>
        generalRegevCenterFraction rank size *
          (generalRegevScale rank size)⁻¹)
      atTop (nhds 0) := by
    apply squeeze_zero
    · intro size
      exact mul_nonneg (generalRegevCenterFraction_nonneg rank size)
        (inv_nonneg.2 (Real.sqrt_nonneg _))
    · intro size
      have hfraction : generalRegevCenterFraction rank size ≤ 1 :=
        (generalRegevCenterFraction_lt_one rank size).le
      unfold generalRegevScale
      exact mul_le_mul_of_nonneg_right hfraction
        (inv_nonneg.2 (Real.sqrt_nonneg _))
    · simpa [generalRegevScale] using hinverse
  simpa [generalRegevShift, div_eq_mul_inv, neg_mul] using hzero.neg

end FibonacciRibbonKernel
