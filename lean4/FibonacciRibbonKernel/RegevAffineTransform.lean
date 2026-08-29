import FibonacciRibbonKernel.RegevCompactCutoff

namespace FibonacciRibbonKernel

open Filter Set
open scoped Classical Topology

noncomputable def generalAffineTransform
    (rank size : ℕ) (coordinates : Fin rank → ℝ) :
    Fin rank → ℝ :=
  ((generalRegevMesh rank size : ℝ) / generalRegevScale rank size) • coordinates +
    fun _ => generalRegevShift rank size

@[simp] theorem generalAffineTransform_apply
    (rank size : ℕ) (coordinates : Fin rank → ℝ) (row : Fin rank) :
    generalAffineTransform rank size coordinates row =
      ((generalRegevMesh rank size : ℝ) / generalRegevScale rank size) *
        coordinates row + generalRegevShift rank size :=
  rfl

theorem generalAffineTransform_integerPoint
    {rank size : ℕ} (hsize : 1 ≤ size)
    (hmesh : 1 ≤ generalRegevMesh rank size)
    (coordinates : Fin rank → ℤ) :
    generalAffineTransform rank size
        (quadraticIntegerPoint (generalRegevMesh rank size) coordinates) =
      generalAffineLatticePoint rank size coordinates := by
  funext row
  unfold generalAffineTransform quadraticIntegerPoint
  unfold generalAffineLatticePoint
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hscaleNe : generalRegevScale rank size ≠ 0 :=
    (generalRegevScale_pos hsize).ne'
  have hmeshNe : (generalRegevMesh rank size : ℝ) ≠ 0 := by
    positivity
  field_simp

noncomputable def generalAffineError
    (rank size : ℕ) (radius : ℝ) : ℝ :=
  |(generalRegevMesh rank size : ℝ) / generalRegevScale rank size - 1| * radius +
    |generalRegevShift rank size|

theorem generalAffineError_tendsto_zero
    (rank : ℕ) (radius : ℝ) :
    Tendsto (fun size : ℕ => generalAffineError rank size radius)
      atTop (nhds 0) := by
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hratio := (generalRegevMesh_div_scale_tendsto_one rank).sub hone
  have habsRatio : Tendsto
      (fun size : ℕ =>
        |(generalRegevMesh rank size : ℝ) /
          generalRegevScale rank size - 1|)
      atTop (nhds 0) := by
    simpa using hratio.abs
  have hfirst : Tendsto
      (fun size : ℕ =>
        |(generalRegevMesh rank size : ℝ) /
          generalRegevScale rank size - 1| * radius)
      atTop (nhds 0) := by
    simpa using habsRatio.mul_const radius
  have hshift : Tendsto
      (fun size : ℕ => |generalRegevShift rank size|)
      atTop (nhds 0) := by
    simpa using (generalRegevShift_tendsto_zero rank).abs
  simpa [generalAffineError] using hfirst.add hshift

theorem norm_const_le_abs
    {rank : ℕ} (value : ℝ) :
    ‖(fun _ : Fin rank => value)‖ ≤ |value| := by
  rw [pi_norm_le_iff_of_nonneg (abs_nonneg value)]
  intro row
  simp [Real.norm_eq_abs]

theorem dist_generalAffineTransform_le
    (rank size : ℕ) {radius : ℝ}
    {coordinates : Fin rank → ℝ}
    (hcoordinates : coordinates ∈ Metric.closedBall 0 radius) :
    dist (generalAffineTransform rank size coordinates) coordinates ≤
      generalAffineError rank size radius := by
  have hnorm : ‖coordinates‖ ≤ radius := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hcoordinates
  let ratio := (generalRegevMesh rank size : ℝ) /
    generalRegevScale rank size
  let shiftVector : Fin rank → ℝ := fun _ => generalRegevShift rank size
  have hidentity : generalAffineTransform rank size coordinates - coordinates =
      (ratio - 1) • coordinates + shiftVector := by
    ext row
    rw [Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      generalAffineTransform_apply]
    dsimp only [ratio, shiftVector]
    simp only [smul_eq_mul]
    ring
  rw [dist_eq_norm, hidentity]
  calc
    ‖(ratio - 1) • coordinates + shiftVector‖ ≤
        ‖(ratio - 1) • coordinates‖ + ‖shiftVector‖ := norm_add_le _ _
    _ ≤ |ratio - 1| * ‖coordinates‖ +
        |generalRegevShift rank size| := by
      rw [norm_smul, Real.norm_eq_abs]
      have hshiftVector : ‖shiftVector‖ ≤
          |generalRegevShift rank size| := by
        dsimp only [shiftVector]
        exact norm_const_le_abs (generalRegevShift rank size)
      exact add_le_add_right hshiftVector _
    _ ≤ |ratio - 1| * radius +
        |generalRegevShift rank size| := by
      gcongr
    _ = generalAffineError rank size radius := by
      rfl

theorem generalAffineTransform_function_uniform_on_closedBall
    (rank : ℕ) (radius : ℝ) (function : (Fin rank → ℝ) → ℝ)
    (hfunction : Continuous function) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ size : ℕ in atTop,
      ∀ coordinates ∈ Metric.closedBall (0 : Fin rank → ℝ) radius,
        dist (function (generalAffineTransform rank size coordinates))
          (function coordinates) < ε := by
  let compactRadius := max radius 0 + 1
  have hcompact : IsCompact
      (Metric.closedBall (0 : Fin rank → ℝ) compactRadius) :=
    ProperSpace.isCompact_closedBall _ _
  have huniform := hcompact.uniformContinuousOn_of_continuous
    hfunction.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huniform
  obtain ⟨δ, hδ, huniformδ⟩ := huniform ε hε
  have herror := generalAffineError_tendsto_zero rank (max radius 0)
  have hsmall : ∀ᶠ size : ℕ in atTop,
      generalAffineError rank size (max radius 0) < min 1 δ := by
    exact herror.eventually (Iio_mem_nhds (lt_min zero_lt_one hδ))
  filter_upwards [hsmall] with size hsize coordinates hcoordinates
  have hradiusLe : radius ≤ max radius 0 := le_max_left _ _
  have hcoordinatesLarge : coordinates ∈
      Metric.closedBall (0 : Fin rank → ℝ) (max radius 0) :=
    Metric.closedBall_subset_closedBall hradiusLe hcoordinates
  have hdist := dist_generalAffineTransform_le rank size hcoordinatesLarge
  have hdistδ : dist (generalAffineTransform rank size coordinates) coordinates < δ :=
    hdist.trans_lt (hsize.trans_le (min_le_right _ _))
  have hcoordinatesCompact : coordinates ∈
      Metric.closedBall (0 : Fin rank → ℝ) compactRadius :=
    Metric.closedBall_subset_closedBall (by
      dsimp only [compactRadius]
      linarith) hcoordinatesLarge
  have htransformedCompact : generalAffineTransform rank size coordinates ∈
      Metric.closedBall (0 : Fin rank → ℝ) compactRadius := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have hnorm : ‖coordinates‖ ≤ max radius 0 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hcoordinatesLarge
    have hdistOne : dist (generalAffineTransform rank size coordinates) coordinates < 1 :=
      hdist.trans_lt (hsize.trans_le (min_le_left _ _))
    have htriangle := dist_triangle
      (generalAffineTransform rank size coordinates) coordinates 0
    rw [dist_zero_right, dist_zero_right] at htriangle
    dsimp only [compactRadius]
    linarith
  exact huniformδ _ htransformedCompact _ hcoordinatesCompact hdistδ

theorem generalAffineTransform_preimage_closedBall
    (rank size : ℕ) (radius : ℝ)
    (hratio : 1 / 2 ≤
      (generalRegevMesh rank size : ℝ) / generalRegevScale rank size)
    (hshift : |generalRegevShift rank size| ≤ 1)
    {coordinates : Fin rank → ℝ}
    (htransformed : generalAffineTransform rank size coordinates ∈
      Metric.closedBall 0 radius) :
    coordinates ∈ Metric.closedBall 0 (2 * (radius + 1)) := by
  have htransformedNorm :
      ‖generalAffineTransform rank size coordinates‖ ≤ radius := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using htransformed
  let ratio := (generalRegevMesh rank size : ℝ) /
    generalRegevScale rank size
  let shiftVector : Fin rank → ℝ := fun _ => generalRegevShift rank size
  have hidentity : ratio • coordinates =
      generalAffineTransform rank size coordinates - shiftVector := by
    ext row
    rw [Pi.smul_apply, Pi.sub_apply, generalAffineTransform_apply]
    dsimp only [ratio, shiftVector]
    simp only [smul_eq_mul]
    ring
  have hshiftNorm : ‖shiftVector‖ ≤ 1 :=
    (norm_const_le_abs (rank := rank) (generalRegevShift rank size)).trans hshift
  have hratioNonneg : 0 ≤ ratio := by
    dsimp only [ratio]
    nlinarith
  have hscaledNorm : ratio * ‖coordinates‖ ≤ radius + 1 := by
    calc
      ratio * ‖coordinates‖ = ‖ratio • coordinates‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hratioNonneg]
      _ = ‖generalAffineTransform rank size coordinates - shiftVector‖ := by
        rw [hidentity]
      _ ≤ ‖generalAffineTransform rank size coordinates‖ + ‖shiftVector‖ :=
        norm_sub_le _ _
      _ ≤ radius + 1 := by linarith
  rw [Metric.mem_closedBall, dist_zero_right]
  have hnormNonneg := norm_nonneg coordinates
  nlinarith

theorem generalAffineTransform_preimage_compact_support
    (rank size : ℕ) (radius : ℝ)
    (_hradius : 0 ≤ radius)
    (hratio : 1 / 2 ≤
      (generalRegevMesh rank size : ℝ) / generalRegevScale rank size)
    (hshift : |generalRegevShift rank size| ≤ 1)
    {coordinates : Fin rank → ℝ}
    (hnonzero : regevCompactChamberExtension rank radius
      (generalAffineTransform rank size coordinates) ≠ 0) :
    coordinates ∈ Metric.closedBall 0 (2 * (radius + 2)) := by
  have htransformed : generalAffineTransform rank size coordinates ∈
      Metric.closedBall 0 (radius + 1) := by
    by_contra hnot
    exact hnonzero
      (regevCompactChamberExtension_eq_zero_of_not_mem hnot)
  have hclosed := generalAffineTransform_preimage_closedBall
    rank size (radius + 1) hratio hshift htransformed
  simpa only [add_assoc, one_add_one_eq_two] using hclosed

end FibonacciRibbonKernel
