import FibonacciRibbonKernel.RegevAffineTransform

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set Submodule Pointwise
open scoped Classical Topology Pointwise

noncomputable def integerBallPointDensity
    (rank mesh : ℕ) (radius : ℝ) : ℝ :=
  (Nat.card (IntegerBallIndex rank mesh radius) : ℝ) / mesh ^ rank

theorem integerBallPointDensity_tendsto
    (rank : ℕ) (radius : ℝ) :
    Tendsto (fun mesh => integerBallPointDensity rank mesh radius)
      atTop (nhds (volume.real
        (Metric.closedBall (0 : Fin rank → ℝ) radius))) := by
  have hdensity := tendsto_card_div_pow_atTop_volume
    (Metric.closedBall (0 : Fin rank → ℝ) radius)
    Metric.isBounded_closedBall Metric.isClosed_closedBall.measurableSet
    (closedBall_null_frontier rank radius)
  apply hdensity.congr'
  filter_upwards [eventually_ge_atTop 1] with mesh hmesh
  unfold integerBallPointDensity
  simp only [Fintype.card_fin]
  congr 1
  have hcard := (Nat.card_congr
    (integerBallPointEquiv rank mesh hmesh radius)).symm
  exact_mod_cast hcard

noncomputable def generalStandardCompactAverage
    (rank size : ℕ) (radius : ℝ) : ℝ :=
  (∑' coordinates : Fin rank → ℤ,
    regevCompactChamberExtension rank radius
      (quadraticIntegerPoint (generalRegevMesh rank size) coordinates)) /
    generalRegevMesh rank size ^ rank

noncomputable def generalAffineMeshCompactAverage
    (rank size : ℕ) (radius : ℝ) : ℝ :=
  (∑' coordinates : Fin rank → ℤ,
    regevCompactChamberExtension rank radius
      (generalAffineTransform rank size
        (quadraticIntegerPoint (generalRegevMesh rank size) coordinates))) /
    generalRegevMesh rank size ^ rank

noncomputable def generalAffineScaleCompactAverage
    (rank size : ℕ) (radius : ℝ) : ℝ :=
  (∑' coordinates : Fin rank → ℤ,
    regevCompactChamberExtension rank radius
      (generalAffineTransform rank size
        (quadraticIntegerPoint (generalRegevMesh rank size) coordinates))) /
    generalRegevScale rank size ^ rank

theorem generalStandardCompactAverage_tendsto
    (rank : ℕ) (radius : ℝ) :
    Tendsto (fun size => generalStandardCompactAverage rank size radius)
      atTop
      (nhds (∫ coordinates,
        regevCompactChamberExtension rank radius coordinates)) := by
  exact (compact_extension_integer_riemann_tendsto rank radius).comp
    (generalRegevMesh_tendsto_atTop rank)

theorem general_affine_mesh_sub_standard_tendsto_zero
    (rank : ℕ) (radius : ℝ) (hradius : 0 ≤ radius) :
    Tendsto
      (fun size => generalAffineMeshCompactAverage rank size radius -
        generalStandardCompactAverage rank size radius)
      atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  rw [← Filter.eventually_atTop]
  let supportRadius := 2 * (radius + 2)
  let densityBound :=
    volume.real (Metric.closedBall (0 : Fin rank → ℝ) supportRadius) + 1
  have hdensityBoundPos : 0 < densityBound := by
    dsimp only [densityBound]
    exact add_pos_of_nonneg_of_pos measureReal_nonneg zero_lt_one
  let localError := ε / (2 * densityBound)
  have hlocalError : 0 < localError := by
    dsimp only [localError]
    positivity
  have huniform := generalAffineTransform_function_uniform_on_closedBall
    rank supportRadius (regevCompactChamberExtension rank radius)
    (continuous_regevCompactChamberExtension rank radius)
    localError hlocalError
  have hdensity := integerBallPointDensity_tendsto rank supportRadius
  have hdensityEventually : ∀ᶠ size : ℕ in atTop,
      integerBallPointDensity rank (generalRegevMesh rank size) supportRadius <
        densityBound := by
    have hcomposed := hdensity.comp (generalRegevMesh_tendsto_atTop rank)
    exact hcomposed.eventually (Iio_mem_nhds (by
      dsimp only [densityBound]
      linarith))
  have hmeshEventually : ∀ᶠ size : ℕ in atTop,
      1 ≤ generalRegevMesh rank size :=
    (generalRegevMesh_tendsto_atTop rank).eventually (eventually_ge_atTop 1)
  have hratioEventually : ∀ᶠ size : ℕ in atTop,
      1 / 2 ≤ (generalRegevMesh rank size : ℝ) /
        generalRegevScale rank size :=
    (generalRegevMesh_div_scale_tendsto_one rank).eventually
      (Ici_mem_nhds (by norm_num))
  have hshiftEventually : ∀ᶠ size : ℕ in atTop,
      |generalRegevShift rank size| ≤ 1 := by
    have hshiftAbs := (generalRegevShift_tendsto_zero rank).abs
    exact hshiftAbs.eventually (Iic_mem_nhds (by norm_num))
  filter_upwards [huniform, hdensityEventually, hmeshEventually,
    hratioEventually, hshiftEventually]
    with size huniformSize hdensitySize hmesh hratio hshift
  have hsupportStandard : ∀ coordinates,
      regevCompactChamberExtension rank radius coordinates ≠ 0 →
        coordinates ∈ Metric.closedBall 0 supportRadius := by
    intro coordinates hnonzero
    have hin : coordinates ∈ Metric.closedBall 0 (radius + 1) := by
      by_contra hnot
      exact hnonzero
        (regevCompactChamberExtension_eq_zero_of_not_mem hnot)
    exact Metric.closedBall_subset_closedBall (by
      dsimp only [supportRadius]
      linarith) hin
  have hsupportAffine : ∀ coordinates,
      regevCompactChamberExtension rank radius
        (generalAffineTransform rank size coordinates) ≠ 0 →
      coordinates ∈ Metric.closedBall 0 supportRadius := by
    intro coordinates hnonzero
    exact generalAffineTransform_preimage_compact_support
      rank size radius hradius hratio hshift hnonzero
  let equivalence := integerBallPointEquiv rank
    (generalRegevMesh rank size) hmesh supportRadius
  letI : Fintype (IntegerBallIndex rank (generalRegevMesh rank size)
      supportRadius) := by
    letI : NeZero (generalRegevMesh rank size) := ⟨by omega⟩
    have hfinite : Set.Finite
        (Metric.closedBall (0 : Fin rank → ℝ) supportRadius ∩
          ((generalRegevMesh rank size : ℝ)⁻¹ •
            (regevIntegerLattice rank : Set (Fin rank → ℝ)))) := by
      unfold regevIntegerLattice
      rw [← coe_pointwise_smul,
        ZSpan.smul _ (inv_ne_zero (NeZero.ne _))]
      exact ZSpan.setFinite_inter _ Metric.isBounded_closedBall
    letI : Fintype ↑(Metric.closedBall (0 : Fin rank → ℝ) supportRadius ∩
        ((generalRegevMesh rank size : ℝ)⁻¹ •
          (regevIntegerLattice rank : Set (Fin rank → ℝ)))) :=
      hfinite.fintype
    exact Fintype.ofEquiv _ equivalence.symm
  have hactualSupport := integer_full_sum_eq_ball_sum
    rank (generalRegevMesh rank size) supportRadius
    (fun coordinates => regevCompactChamberExtension rank radius
      (generalAffineTransform rank size coordinates)) hsupportAffine
  have hstandardSupport := integer_full_sum_eq_ball_sum
    rank (generalRegevMesh rank size) supportRadius
    (regevCompactChamberExtension rank radius) hsupportStandard
  have hraw :
      |(∑' coordinates : Fin rank → ℤ,
          regevCompactChamberExtension rank radius
            (generalAffineTransform rank size
              (quadraticIntegerPoint (generalRegevMesh rank size) coordinates))) -
        ∑' coordinates : Fin rank → ℤ,
          regevCompactChamberExtension rank radius
            (quadraticIntegerPoint (generalRegevMesh rank size) coordinates)| ≤
      (Nat.card (IntegerBallIndex rank (generalRegevMesh rank size)
        supportRadius) : ℝ) * localError := by
    rw [hactualSupport, hstandardSupport, tsum_fintype, tsum_fintype,
      ← Finset.sum_sub_distrib]
    calc
      |∑ coordinates : IntegerBallIndex rank (generalRegevMesh rank size)
          supportRadius,
        (regevCompactChamberExtension rank radius
            (generalAffineTransform rank size
              (quadraticIntegerPoint (generalRegevMesh rank size) coordinates.1)) -
          regevCompactChamberExtension rank radius
            (quadraticIntegerPoint (generalRegevMesh rank size) coordinates.1))| ≤
        ∑ coordinates : IntegerBallIndex rank (generalRegevMesh rank size)
          supportRadius,
          |regevCompactChamberExtension rank radius
              (generalAffineTransform rank size
                (quadraticIntegerPoint (generalRegevMesh rank size) coordinates.1)) -
            regevCompactChamberExtension rank radius
              (quadraticIntegerPoint (generalRegevMesh rank size) coordinates.1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _coordinates : IntegerBallIndex rank
          (generalRegevMesh rank size) supportRadius, localError := by
        apply Finset.sum_le_sum
        intro coordinates hcoordinates
        rw [← Real.dist_eq]
        exact (huniformSize _ coordinates.2).le
      _ = (Nat.card (IntegerBallIndex rank (generalRegevMesh rank size)
          supportRadius) : ℝ) * localError := by
        rw [Finset.sum_const, nsmul_eq_mul]
        congr 1
        rw [Finset.card_univ]
        exact_mod_cast (Nat.card_eq_fintype_card :
          Nat.card (IntegerBallIndex rank (generalRegevMesh rank size)
            supportRadius) = _).symm
  have hmeshPowerPos : (0 : ℝ) < generalRegevMesh rank size ^ rank := by
    positivity
  have hnormalized :
      |generalAffineMeshCompactAverage rank size radius -
        generalStandardCompactAverage rank size radius| ≤
      integerBallPointDensity rank (generalRegevMesh rank size) supportRadius *
        localError := by
    unfold generalAffineMeshCompactAverage generalStandardCompactAverage
    rw [← sub_div, abs_div, abs_of_pos hmeshPowerPos]
    exact (div_le_div_of_nonneg_right hraw hmeshPowerPos.le).trans_eq (by
      unfold integerBallPointDensity
      ring)
  have hstrict :
      integerBallPointDensity rank (generalRegevMesh rank size) supportRadius *
        localError < ε := by
    calc
      _ < densityBound * localError :=
        mul_lt_mul_of_pos_right hdensitySize hlocalError
      _ = ε / 2 := by
        dsimp only [localError]
        field_simp
      _ < ε := by linarith
  rw [Real.dist_eq, sub_zero]
  exact hnormalized.trans_lt hstrict

theorem generalAffineMeshCompactAverage_tendsto
    (rank : ℕ) (radius : ℝ) (hradius : 0 ≤ radius) :
    Tendsto (fun size => generalAffineMeshCompactAverage rank size radius)
      atTop
      (nhds (∫ coordinates,
        regevCompactChamberExtension rank radius coordinates)) := by
  have hdifference := general_affine_mesh_sub_standard_tendsto_zero
    rank radius hradius
  have hstandard := generalStandardCompactAverage_tendsto rank radius
  simpa [sub_add_cancel] using hdifference.add hstandard

theorem generalAffineScaleCompactAverage_tendsto
    (rank : ℕ) (radius : ℝ) (hradius : 0 ≤ radius) :
    Tendsto (fun size => generalAffineScaleCompactAverage rank size radius)
      atTop
      (nhds (∫ coordinates,
        regevCompactChamberExtension rank radius coordinates)) := by
  have hmeshAverage := generalAffineMeshCompactAverage_tendsto
    rank radius hradius
  have hratioPower : Tendsto
      (fun size : ℕ => ((generalRegevMesh rank size : ℝ) /
        generalRegevScale rank size) ^ rank)
      atTop (nhds 1) := by
    simpa using (generalRegevMesh_div_scale_tendsto_one rank).pow rank
  have hproduct := hratioPower.mul hmeshAverage
  have hproduct' : Tendsto
      (fun size => ((generalRegevMesh rank size : ℝ) /
          generalRegevScale rank size) ^ rank *
        generalAffineMeshCompactAverage rank size radius)
      atTop
      (nhds (∫ coordinates,
        regevCompactChamberExtension rank radius coordinates)) := by
    simpa using hproduct
  have hmeshEventually : ∀ᶠ size : ℕ in atTop,
      1 ≤ generalRegevMesh rank size :=
    (generalRegevMesh_tendsto_atTop rank).eventually
      (eventually_ge_atTop 1)
  apply hproduct'.congr'
  filter_upwards [hmeshEventually] with size hmesh
  unfold generalAffineScaleCompactAverage generalAffineMeshCompactAverage
  have hscaleNe : generalRegevScale rank size ≠ 0 := by
    have hsize : 1 ≤ size := by
      by_contra hnot
      have hzero : size = 0 := Nat.eq_zero_of_not_pos hnot
      subst size
      simp [generalRegevMesh, generalRegevScale] at hmesh
    exact (generalRegevScale_pos hsize).ne'
  have hmeshNe : (generalRegevMesh rank size : ℝ) ≠ 0 := by positivity
  rw [div_pow]
  field_simp [pow_ne_zero rank hmeshNe, pow_ne_zero rank hscaleNe]

end FibonacciRibbonKernel
