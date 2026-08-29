import FibonacciRibbonKernel.RegevUniformLocal

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set
open scoped Classical Topology Pointwise

def QuadraticTruncatedShape (rank mesh : ℕ) (radius : ℝ) :=
  {shape : BoundedPartition rank (quadraticSize rank mesh) //
    quadraticShapePoint shape ∈ Metric.closedBall 0 radius}

noncomputable instance quadraticTruncatedShapeFintype
    (rank mesh : ℕ) (radius : ℝ) :
    Fintype (QuadraticTruncatedShape rank mesh radius) := by
  unfold QuadraticTruncatedShape
  infer_instance

noncomputable def quadraticTruncatedNormalizedSum
    (rank mesh : ℕ) (radius : ℝ) : ℝ :=
  ∑ shape : QuadraticTruncatedShape rank mesh radius,
    matsumotoLocalNormalizedTableau shape.1

def QuadraticTruncatedRiemannPoint
    (rank mesh : ℕ) (radius : ℝ) :=
  ↑(regevTruncatedChamber rank radius ∩
    ((mesh : ℝ)⁻¹ • regevIntegerLattice rank))

noncomputable def quadraticShapePointRiemannEquiv
    (rank mesh : ℕ) (hmesh : 1 ≤ mesh) (radius : ℝ)
    (hradius : 0 ≤ radius)
    (hmeshRadius : ((rank + 1 : ℕ) : ℝ) * radius ≤ mesh) :
    QuadraticTruncatedShape rank mesh radius ≃
      QuadraticTruncatedRiemannPoint rank mesh radius := by
  unfold QuadraticTruncatedShape QuadraticTruncatedRiemannPoint
  apply (Equiv.subtypeEquivRight ?_).trans
    (boundedPartitionQuadraticRiemannPointEquiv
      rank mesh hmesh radius hradius hmeshRadius)
  intro shape
  rfl

@[simp] theorem quadraticShapePointRiemannEquiv_apply_val
    (rank mesh : ℕ) (hmesh : 1 ≤ mesh) (radius : ℝ)
    (hradius : 0 ≤ radius)
    (hmeshRadius : ((rank + 1 : ℕ) : ℝ) * radius ≤ mesh)
    (shape : QuadraticTruncatedShape rank mesh radius) :
    ((quadraticShapePointRiemannEquiv rank mesh hmesh radius
      hradius hmeshRadius) shape).1 = quadraticShapePoint shape.1 :=
  rfl

theorem quadratic_truncated_sum_reindex
    (rank mesh : ℕ) (hmesh : 1 ≤ mesh) (radius : ℝ)
    (hradius : 0 ≤ radius)
    (hmeshRadius : ((rank + 1 : ℕ) : ℝ) * radius ≤ mesh) :
    quadraticTruncatedNormalizedSum rank mesh radius =
      ∑' point : QuadraticTruncatedRiemannPoint rank mesh radius,
        matsumotoLocalNormalizedTableau
          ((quadraticShapePointRiemannEquiv rank mesh hmesh radius
            hradius hmeshRadius).symm point).1 := by
  let equivalence := quadraticShapePointRiemannEquiv
    rank mesh hmesh radius hradius hmeshRadius
  unfold quadraticTruncatedNormalizedSum
  calc
    (∑ shape : QuadraticTruncatedShape rank mesh radius,
        matsumotoLocalNormalizedTableau shape.1) =
      ∑' shape : QuadraticTruncatedShape rank mesh radius,
        matsumotoLocalNormalizedTableau shape.1 := by
          rw [tsum_fintype]
    _ = ∑' point : QuadraticTruncatedRiemannPoint rank mesh radius,
        matsumotoLocalNormalizedTableau (equivalence.symm point).1 := by
      exact (equivalence.symm.tsum_eq
        (fun shape => matsumotoLocalNormalizedTableau shape.1)).symm

noncomputable def quadraticTruncatedRiemannSum
    (rank mesh : ℕ) (radius : ℝ) : ℝ :=
  (∑' point : QuadraticTruncatedRiemannPoint rank mesh radius,
    regevLocalIntegrand rank point.1) / mesh ^ rank

noncomputable def quadraticTruncatedNormalizedAverage
    (rank mesh : ℕ) (radius : ℝ) : ℝ :=
  quadraticTruncatedNormalizedSum rank mesh radius / mesh ^ rank

noncomputable def quadraticTruncatedPointDensity
    (rank mesh : ℕ) (radius : ℝ) : ℝ :=
  (Nat.card (QuadraticTruncatedRiemannPoint rank mesh radius) : ℝ) /
    mesh ^ rank

theorem quadratic_truncated_riemann_sum_tendsto
    (rank : ℕ) (radius : ℝ) :
    Tendsto (fun mesh => quadraticTruncatedRiemannSum rank mesh radius)
      atTop
      (nhds (∫ coordinates in regevTruncatedChamber rank radius,
        regevLocalIntegrand rank coordinates)) := by
  simpa [quadraticTruncatedRiemannSum,
    QuadraticTruncatedRiemannPoint] using
      regev_truncated_riemann_sum_tendsto rank radius

theorem quadratic_truncated_pointDensity_tendsto
    (rank : ℕ) (radius : ℝ) :
    Tendsto (fun mesh => quadraticTruncatedPointDensity rank mesh radius)
      atTop (nhds (volume.real (regevTruncatedChamber rank radius))) := by
  unfold quadraticTruncatedPointDensity QuadraticTruncatedRiemannPoint
  unfold regevIntegerLattice
  simpa only [Fintype.card_fin] using
    tendsto_card_div_pow_atTop_volume
      (regevTruncatedChamber rank radius)
      (regevTruncatedChamber_isBounded rank radius)
      (regevTruncatedChamber_measurableSet rank radius)
      (regevTruncatedChamber_null_frontier rank radius)

theorem quadratic_truncated_sum_error_bound
    (rank mesh : ℕ) (hmesh : 1 ≤ mesh) (radius : ℝ)
    (hradius : 0 ≤ radius)
    (hmeshRadius : ((rank + 1 : ℕ) : ℝ) * radius ≤ mesh)
    (error : ℝ) (_herror : 0 ≤ error)
    (huniform : ∀ shape : BoundedPartition rank (quadraticSize rank mesh),
      quadraticShapePoint shape ∈ Metric.closedBall 0 radius →
      dist (matsumotoLocalNormalizedTableau shape)
        (regevLocalIntegrand rank (quadraticShapePoint shape)) ≤ error) :
    |quadraticTruncatedNormalizedSum rank mesh radius -
        ∑' point : QuadraticTruncatedRiemannPoint rank mesh radius,
          regevLocalIntegrand rank point.1| ≤
      (Nat.card (QuadraticTruncatedRiemannPoint rank mesh radius) : ℝ) * error := by
  let equivalence := quadraticShapePointRiemannEquiv
    rank mesh hmesh radius hradius hmeshRadius
  rw [quadratic_truncated_sum_reindex rank mesh hmesh radius
    hradius hmeshRadius]
  letI : Fintype (QuadraticTruncatedRiemannPoint rank mesh radius) :=
    Fintype.ofEquiv (QuadraticTruncatedShape rank mesh radius) equivalence
  rw [tsum_fintype, tsum_fintype, ← Finset.sum_sub_distrib]
  calc
    |∑ point : QuadraticTruncatedRiemannPoint rank mesh radius,
        (matsumotoLocalNormalizedTableau (equivalence.symm point).1 -
          regevLocalIntegrand rank point.1)| ≤
      ∑ point : QuadraticTruncatedRiemannPoint rank mesh radius,
        |matsumotoLocalNormalizedTableau (equivalence.symm point).1 -
          regevLocalIntegrand rank point.1| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _point : QuadraticTruncatedRiemannPoint rank mesh radius,
        error := by
      apply Finset.sum_le_sum
      intro point hpoint
      have hpointEq := congrArg Subtype.val
        (equivalence.apply_symm_apply point)
      change quadraticShapePoint (equivalence.symm point).1 = point.1 at hpointEq
      change |matsumotoLocalNormalizedTableau (equivalence.symm point).1 -
          regevLocalIntegrand rank point.1| ≤ error
      rw [← hpointEq]
      rw [← Real.dist_eq]
      exact huniform (equivalence.symm point).1 (equivalence.symm point).2
    _ = (Nat.card (QuadraticTruncatedRiemannPoint rank mesh radius) : ℝ) *
        error := by
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      have hcard :
          Nat.card (QuadraticTruncatedRiemannPoint rank mesh radius) =
            Fintype.card (QuadraticTruncatedRiemannPoint rank mesh radius) :=
        Nat.card_eq_fintype_card
      rw [Finset.card_univ]
      exact_mod_cast hcard.symm

theorem quadratic_truncated_average_sub_riemann_tendsto_zero
    (rank : ℕ) (radius : ℝ) (hradius : 0 ≤ radius) :
    Tendsto
      (fun mesh => quadraticTruncatedNormalizedAverage rank mesh radius -
        quadraticTruncatedRiemannSum rank mesh radius)
      atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  rw [← Filter.eventually_atTop]
  let bound := volume.real (regevTruncatedChamber rank radius) + 1
  have hboundPos : 0 < bound := by
    dsimp only [bound]
    exact add_pos_of_nonneg_of_pos (measureReal_nonneg) zero_lt_one
  let localError := ε / (2 * bound)
  have hlocalErrorPos : 0 < localError := by
    dsimp only [localError]
    positivity
  have huniform := matsumoto_quadratic_local_uniform_on_closedBall
    rank radius localError hlocalErrorPos
  have hdensity := quadratic_truncated_pointDensity_tendsto rank radius
  have hdensityBound : ∀ᶠ mesh in atTop,
      quadraticTruncatedPointDensity rank mesh radius < bound := by
    have hmem : Set.Iio bound ∈
        nhds (volume.real (regevTruncatedChamber rank radius)) :=
      Iio_mem_nhds (by
      dsimp only [bound]
      linarith)
    exact hdensity.eventually hmem
  have heventMesh : ∀ᶠ mesh : ℕ in atTop, 1 ≤ mesh :=
    Filter.eventually_ge_atTop 1
  have heventRadius : ∀ᶠ mesh : ℕ in atTop,
      ((rank + 1 : ℕ) : ℝ) * radius ≤ mesh := by
    filter_upwards [Filter.eventually_ge_atTop
      ⌈((rank + 1 : ℕ) : ℝ) * radius⌉₊] with mesh hmesh
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr hmesh)
  filter_upwards [huniform, hdensityBound, heventMesh, heventRadius]
    with mesh huniformMesh hdensityMesh hmesh hmeshRadius
  have hraw := quadratic_truncated_sum_error_bound
    rank mesh hmesh radius hradius hmeshRadius localError
    hlocalErrorPos.le
    (fun shape hshape => (huniformMesh shape hshape).le)
  have hmeshPowerPos : (0 : ℝ) < mesh ^ rank := by positivity
  have havg :
      |quadraticTruncatedNormalizedAverage rank mesh radius -
          quadraticTruncatedRiemannSum rank mesh radius| ≤
        quadraticTruncatedPointDensity rank mesh radius * localError := by
    unfold quadraticTruncatedNormalizedAverage
    unfold quadraticTruncatedRiemannSum quadraticTruncatedPointDensity
    rw [← sub_div, abs_div, abs_of_pos hmeshPowerPos]
    exact (div_le_div_of_nonneg_right hraw hmeshPowerPos.le).trans_eq
      (by ring)
  have hstrict :
      quadraticTruncatedPointDensity rank mesh radius * localError < ε := by
    calc
      quadraticTruncatedPointDensity rank mesh radius * localError <
          bound * localError :=
        mul_lt_mul_of_pos_right hdensityMesh hlocalErrorPos
      _ = ε / 2 := by
        dsimp only [localError]
        field_simp
      _ < ε := by linarith
  calc
    dist (quadraticTruncatedNormalizedAverage rank mesh radius -
        quadraticTruncatedRiemannSum rank mesh radius) 0 =
      |quadraticTruncatedNormalizedAverage rank mesh radius -
        quadraticTruncatedRiemannSum rank mesh radius| := by
          rw [Real.dist_eq, sub_zero]
    _ ≤ quadraticTruncatedPointDensity rank mesh radius * localError := havg
    _ < ε := hstrict

theorem quadratic_truncated_normalizedAverage_tendsto
    (rank : ℕ) (radius : ℝ) (hradius : 0 ≤ radius) :
    Tendsto (fun mesh => quadraticTruncatedNormalizedAverage rank mesh radius)
      atTop
      (nhds (∫ coordinates in regevTruncatedChamber rank radius,
        regevLocalIntegrand rank coordinates)) := by
  have hdifference :=
    quadratic_truncated_average_sub_riemann_tendsto_zero rank radius hradius
  have hriemann := quadratic_truncated_riemann_sum_tendsto rank radius
  have hadd := hdifference.add hriemann
  simpa [sub_add_cancel] using hadd

end FibonacciRibbonKernel
