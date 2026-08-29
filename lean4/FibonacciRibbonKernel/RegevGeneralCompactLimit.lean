import FibonacciRibbonKernel.RegevGeneralCompactSum

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set
open scoped Classical Topology

noncomputable def generalIntegerBallScaleDensity
    (rank size : ℕ) (radius : ℝ) : ℝ :=
  (Nat.card (IntegerBallIndex rank (generalRegevMesh rank size) radius) : ℝ) /
    generalRegevScale rank size ^ rank

theorem generalIntegerBallScaleDensity_tendsto
    (rank : ℕ) (radius : ℝ) :
    Tendsto (fun size => generalIntegerBallScaleDensity rank size radius)
      atTop (nhds (volume.real
        (Metric.closedBall (0 : Fin rank → ℝ) radius))) := by
  have hdensity := (integerBallPointDensity_tendsto rank radius).comp
    (generalRegevMesh_tendsto_atTop rank)
  have hratio : Tendsto
      (fun size : ℕ => ((generalRegevMesh rank size : ℝ) /
        generalRegevScale rank size) ^ rank)
      atTop (nhds 1) := by
    simpa using (generalRegevMesh_div_scale_tendsto_one rank).pow rank
  have hproduct := hratio.mul hdensity
  have htarget : Tendsto
      (fun size : ℕ => ((generalRegevMesh rank size : ℝ) /
          generalRegevScale rank size) ^ rank *
        integerBallPointDensity rank (generalRegevMesh rank size) radius)
      atTop (nhds (volume.real
        (Metric.closedBall (0 : Fin rank → ℝ) radius))) := by
    simpa using hproduct
  apply htarget.congr'
  filter_upwards [(generalRegevMesh_tendsto_atTop rank).eventually
    (eventually_ge_atTop 1)] with size hmesh
  unfold generalIntegerBallScaleDensity integerBallPointDensity
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

noncomputable def generalCompactShapeToIntegerBall
    (rank size : ℕ) (hsize : 1 ≤ size)
    (hmesh : 1 ≤ generalRegevMesh rank size)
    (radius : ℝ)
    (hratio : 1 / 2 ≤ (generalRegevMesh rank size : ℝ) /
      generalRegevScale rank size)
    (hshift : |generalRegevShift rank size| ≤ 1) :
    GeneralCompactShape rank size radius →
      IntegerBallIndex rank (generalRegevMesh rank size) (2 * (radius + 1)) :=
  fun shape =>
    ⟨generalShapeIntegerCoordinates shape.1, by
      have htransform := generalAffineTransform_integerPoint hsize hmesh
        (generalShapeIntegerCoordinates shape.1)
      have hpoint := generalShapePoint_eq_affineLatticePoint hsize shape.1
      apply generalAffineTransform_preimage_closedBall
        rank size radius hratio hshift
      rw [htransform, ← hpoint]
      exact shape.2⟩

theorem generalCompactShapeToIntegerBall_injective
    (rank size : ℕ) (hsize : 1 ≤ size)
    (hmesh : 1 ≤ generalRegevMesh rank size)
    (radius : ℝ)
    (hratio : 1 / 2 ≤ (generalRegevMesh rank size : ℝ) /
      generalRegevScale rank size)
    (hshift : |generalRegevShift rank size| ≤ 1) :
    Function.Injective
      (generalCompactShapeToIntegerBall rank size hsize hmesh radius
        hratio hshift) := by
  intro first second heq
  apply Subtype.ext
  apply generalShapeIntegerCoordinates_injective hsize
  exact congrArg Subtype.val heq

theorem general_weighted_compact_sub_local_tendsto_zero
    (rank : ℕ) (radius : ℝ) (_hradius : 0 ≤ radius) :
    Tendsto
      (fun size => generalWeightedCompactTableauAverage rank size radius -
        generalWeightedCompactLocalAverage rank size radius)
      atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  rw [← Filter.eventually_atTop]
  let supportRadius := 2 * (radius + 1 + 1)
  let densityBound := volume.real
    (Metric.closedBall (0 : Fin rank → ℝ) supportRadius) + 1
  have hdensityBoundPos : 0 < densityBound := by
    dsimp only [densityBound]
    exact add_pos_of_nonneg_of_pos measureReal_nonneg zero_lt_one
  let localError := ε / (2 * densityBound)
  have hlocalError : 0 < localError := by
    dsimp only [localError]
    positivity
  have huniform := matsumoto_general_local_uniform_on_closedBall
    rank (radius + 1) localError hlocalError
  have hdensity := generalIntegerBallScaleDensity_tendsto rank supportRadius
  have hdensityEventually : ∀ᶠ size : ℕ in atTop,
      generalIntegerBallScaleDensity rank size supportRadius < densityBound :=
    hdensity.eventually (Iio_mem_nhds (by
      dsimp only [densityBound]
      linarith))
  have hsizeEventually : ∀ᶠ size : ℕ in atTop, 1 ≤ size :=
    eventually_ge_atTop 1
  have hmeshEventually : ∀ᶠ size : ℕ in atTop,
      1 ≤ generalRegevMesh rank size :=
    (generalRegevMesh_tendsto_atTop rank).eventually (eventually_ge_atTop 1)
  have hratioEventually : ∀ᶠ size : ℕ in atTop,
      1 / 2 ≤ (generalRegevMesh rank size : ℝ) /
        generalRegevScale rank size :=
    (generalRegevMesh_div_scale_tendsto_one rank).eventually
      (Ici_mem_nhds (by norm_num))
  have hshiftEventually : ∀ᶠ size : ℕ in atTop,
      |generalRegevShift rank size| ≤ 1 :=
    ((generalRegevShift_tendsto_zero rank).abs).eventually
      (Iic_mem_nhds (by norm_num))
  filter_upwards [huniform, hdensityEventually, hsizeEventually,
    hmeshEventually, hratioEventually, hshiftEventually]
    with size huniformSize hdensitySize hsize hmesh hratio hshift
  let compactMap := generalCompactShapeToIntegerBall
    rank size hsize hmesh (radius + 1) hratio hshift
  letI : Fintype (IntegerBallIndex rank (generalRegevMesh rank size)
      supportRadius) :=
    integerBallIndexFintype rank (generalRegevMesh rank size) hmesh supportRadius
  have hcard : Fintype.card (GeneralCompactShape rank size (radius + 1)) ≤
      Fintype.card (IntegerBallIndex rank (generalRegevMesh rank size)
        supportRadius) :=
    Fintype.card_le_of_injective compactMap
      (generalCompactShapeToIntegerBall_injective rank size hsize hmesh
        (radius + 1) hratio hshift)
  have hraw :
      |(∑ shape : BoundedPartition rank size,
          regevRadialCutoff radius (generalShapePoint shape) *
            matsumotoLocalNormalizedTableau shape) -
        ∑ shape : BoundedPartition rank size,
          regevRadialCutoff radius (generalShapePoint shape) *
            regevLocalIntegrand rank (generalShapePoint shape)| ≤
      (Nat.card (IntegerBallIndex rank (generalRegevMesh rank size)
        supportRadius) : ℝ) * localError := by
    rw [← Finset.sum_sub_distrib]
    have hterm : ∀ shape : BoundedPartition rank size,
        |regevRadialCutoff radius (generalShapePoint shape) *
          matsumotoLocalNormalizedTableau shape -
          regevRadialCutoff radius (generalShapePoint shape) *
            regevLocalIntegrand rank (generalShapePoint shape)| ≤
        if generalShapePoint shape ∈ Metric.closedBall 0 (radius + 1)
          then localError else 0 := by
      intro shape
      by_cases hball : generalShapePoint shape ∈
          Metric.closedBall 0 (radius + 1)
      · rw [if_pos hball, ← mul_sub, abs_mul,
          abs_of_nonneg (regevRadialCutoff_nonneg radius _)]
        have hcutoff := regevRadialCutoff_le_one radius
          (generalShapePoint shape)
        have hdist := (huniformSize shape hball).le
        rw [Real.dist_eq] at hdist
        calc
          regevRadialCutoff radius (generalShapePoint shape) *
              |matsumotoLocalNormalizedTableau shape -
                regevLocalIntegrand rank (generalShapePoint shape)| ≤
            1 * localError :=
          mul_le_mul hcutoff hdist (abs_nonneg _) (by norm_num)
          _ = localError := one_mul _
      · rw [if_neg hball, regevRadialCutoff_eq_zero_of_not_mem hball]
        simp
    calc
      |∑ shape : BoundedPartition rank size,
        (regevRadialCutoff radius (generalShapePoint shape) *
          matsumotoLocalNormalizedTableau shape -
          regevRadialCutoff radius (generalShapePoint shape) *
            regevLocalIntegrand rank (generalShapePoint shape))| ≤
        ∑ shape : BoundedPartition rank size,
          |regevRadialCutoff radius (generalShapePoint shape) *
            matsumotoLocalNormalizedTableau shape -
            regevRadialCutoff radius (generalShapePoint shape) *
              regevLocalIntegrand rank (generalShapePoint shape)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ shape : BoundedPartition rank size,
          if generalShapePoint shape ∈ Metric.closedBall 0 (radius + 1)
            then localError else 0 := by
        exact Finset.sum_le_sum fun shape hshape => hterm shape
      _ = (Fintype.card (GeneralCompactShape rank size (radius + 1)) : ℝ) *
          localError := by
        have hpartition := Fintype.sum_subtype_add_sum_subtype
          (fun shape : BoundedPartition rank size =>
            generalShapePoint shape ∈ Metric.closedBall 0 (radius + 1))
          (fun shape => if generalShapePoint shape ∈
            Metric.closedBall 0 (radius + 1) then localError else 0)
        have hsubtype :
            (∑ shape : BoundedPartition rank size,
              if generalShapePoint shape ∈ Metric.closedBall 0 (radius + 1)
                then localError else 0) =
              ∑ _shape : {shape : BoundedPartition rank size //
                generalShapePoint shape ∈ Metric.closedBall 0 (radius + 1)},
                localError := by
          calc
            _ = (∑ shape : {shape : BoundedPartition rank size //
                  generalShapePoint shape ∈ Metric.closedBall 0 (radius + 1)},
                  if generalShapePoint shape.1 ∈
                    Metric.closedBall 0 (radius + 1) then localError else 0) +
                ∑ shape : {shape : BoundedPartition rank size //
                  ¬ generalShapePoint shape ∈ Metric.closedBall 0 (radius + 1)},
                  if generalShapePoint shape.1 ∈
                    Metric.closedBall 0 (radius + 1) then localError else 0 :=
              hpartition.symm
            _ = (∑ _shape : {shape : BoundedPartition rank size //
                  generalShapePoint shape ∈ Metric.closedBall 0 (radius + 1)},
                  localError) + 0 := by
              congr 1
              · apply Finset.sum_congr rfl
                intro shape hshape
                rw [if_pos shape.2]
              · apply Finset.sum_eq_zero
                intro shape hshape
                rw [if_neg shape.2]
            _ = _ := add_zero _
        rw [hsubtype, Finset.sum_const, nsmul_eq_mul,
          Finset.card_univ]
        change (Fintype.card {shape : BoundedPartition rank size //
          generalShapePoint shape ∈ Metric.closedBall 0 (radius + 1)} : ℝ) *
            localError =
          (Fintype.card (GeneralCompactShape rank size (radius + 1)) : ℝ) *
            localError
        rfl
      _ ≤ (Nat.card (IntegerBallIndex rank (generalRegevMesh rank size)
          supportRadius) : ℝ) * localError := by
        apply mul_le_mul_of_nonneg_right _ hlocalError.le
        exact_mod_cast hcard.trans_eq Nat.card_eq_fintype_card.symm
  have hscalePowerPos : (0 : ℝ) < generalRegevScale rank size ^ rank := by
    positivity [generalRegevScale_pos (rank := rank) hsize]
  have hnormalized :
      |generalWeightedCompactTableauAverage rank size radius -
        generalWeightedCompactLocalAverage rank size radius| ≤
      generalIntegerBallScaleDensity rank size supportRadius * localError := by
    unfold generalWeightedCompactTableauAverage
    unfold generalWeightedCompactLocalAverage
    rw [← sub_div, abs_div, abs_of_pos hscalePowerPos]
    exact (div_le_div_of_nonneg_right hraw hscalePowerPos.le).trans_eq (by
      unfold generalIntegerBallScaleDensity
      ring)
  have hstrict :
      generalIntegerBallScaleDensity rank size supportRadius * localError < ε := by
    calc
      _ < densityBound * localError :=
        mul_lt_mul_of_pos_right hdensitySize hlocalError
      _ = ε / 2 := by
        dsimp only [localError]
        field_simp
      _ < ε := by linarith
  rw [Real.dist_eq, sub_zero]
  exact hnormalized.trans_lt hstrict

theorem generalWeightedCompactTableauAverage_tendsto
    (rank : ℕ) (radius : ℝ) (hradius : 0 ≤ radius) :
    Tendsto (fun size => generalWeightedCompactTableauAverage rank size radius)
      atTop
      (nhds (∫ coordinates,
        regevCompactChamberExtension rank radius coordinates)) := by
  have hdiff := general_weighted_compact_sub_local_tendsto_zero
    rank radius hradius
  have hscaleEventually : ∀ᶠ size : ℕ in atTop,
      (rank : ℝ) * (radius + 1) ≤ generalRegevScale rank size :=
    (generalRegevScale_tendsto_atTop rank).eventually
      (eventually_ge_atTop ((rank : ℝ) * (radius + 1)))
  have hsizeEventually : ∀ᶠ size : ℕ in atTop, 1 ≤ size :=
    eventually_ge_atTop 1
  have hmeshEventually : ∀ᶠ size : ℕ in atTop,
      1 ≤ generalRegevMesh rank size :=
    (generalRegevMesh_tendsto_atTop rank).eventually (eventually_ge_atTop 1)
  have hlocalEq : ∀ᶠ size : ℕ in atTop,
      generalWeightedCompactLocalAverage rank size radius =
        generalAffineScaleCompactAverage rank size radius := by
    filter_upwards [hscaleEventually, hsizeEventually, hmeshEventually]
      with size hscale hsize hmesh
    exact generalWeightedCompactLocalAverage_eq_affine
      rank size hsize hmesh radius hradius hscale
  have haffine := generalAffineScaleCompactAverage_tendsto rank radius hradius
  have hlocal := haffine.congr' (Filter.EventuallyEq.symm hlocalEq)
  simpa [sub_add_cancel] using hdiff.add hlocal

end FibonacciRibbonKernel
