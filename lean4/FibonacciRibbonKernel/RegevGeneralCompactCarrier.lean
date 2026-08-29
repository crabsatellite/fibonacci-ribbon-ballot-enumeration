import FibonacciRibbonKernel.RegevGeneralCarrier

namespace FibonacciRibbonKernel

open Set
open scoped Classical

noncomputable def generalChartPoint
    {rank size : ℕ} (chart : GeneralChartTuple rank size) :
    Fin rank → ℝ :=
  generalAffineLatticePoint rank size chart.coordinates

theorem generalFraction_mul_dimension (rank size : ℕ) :
    generalRegevCenterFraction rank size * (rank + 1 : ℝ) =
      (size % (rank + 1) : ℕ) := by
  unfold generalRegevCenterFraction
  have hdimension : (rank + 1 : ℝ) ≠ 0 := by positivity
  field_simp

theorem tracelessExtend_generalAffineLatticePoint
    {rank size : ℕ} (hsize : 1 ≤ size)
    (coordinates : Fin rank → ℤ) (row : Fin (rank + 1)) :
    tracelessExtend (generalAffineLatticePoint rank size coordinates) row =
      (((generalExtendInt rank size coordinates row : ℤ) : ℝ) -
        generalRegevCenterFraction rank size) /
          generalRegevScale rank size := by
  cases row using Fin.lastCases with
  | cast row =>
      rw [tracelessExtend_castSucc, generalExtendInt_castSucc]
      unfold generalAffineLatticePoint generalRegevShift
      ring
  | last =>
      rw [tracelessExtend_last, generalExtendInt_last]
      unfold generalAffineLatticePoint generalRegevShift
      have hscaleNe : generalRegevScale rank size ≠ 0 :=
        (generalRegevScale_pos (rank := rank) hsize).ne'
      have hsumdiv :
          (∑ row : Fin rank,
            ((coordinates row : ℝ) / generalRegevScale rank size +
              -generalRegevCenterFraction rank size /
                generalRegevScale rank size)) =
          (∑ row : Fin rank, (coordinates row : ℝ)) /
              generalRegevScale rank size +
            (rank : ℝ) *
              (-generalRegevCenterFraction rank size /
                generalRegevScale rank size) := by
        have hcard : (Finset.univ : Finset (Fin rank)).card = rank := by simp
        rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_const,
          nsmul_eq_mul, hcard]
      rw [hsumdiv]
      have hfraction := generalFraction_mul_dimension rank size
      rw [Int.cast_sub, Int.cast_natCast]
      push_cast
      change -((∑ row : Fin rank, (coordinates row : ℝ)) /
            generalRegevScale rank size +
          (rank : ℝ) * (-generalRegevCenterFraction rank size /
            generalRegevScale rank size)) =
        (((size % (rank + 1) : ℕ) : ℝ) -
            (∑ row : Fin rank, (coordinates row : ℝ)) -
              generalRegevCenterFraction rank size) /
          generalRegevScale rank size
      field_simp [hscaleNe]
      linarith

theorem generalAffineLatticePoint_mem_chamber_iff
    {rank size : ℕ} (hsize : 1 ≤ size)
    (coordinates : Fin rank → ℤ) :
    generalAffineLatticePoint rank size coordinates ∈ regevChamber rank ↔
      Antitone (generalExtendInt rank size coordinates) := by
  have hscale : 0 < generalRegevScale rank size :=
    generalRegevScale_pos (rank := rank) hsize
  rw [regevChamber_mem_iff]
  constructor
  · intro hcentered row next hrowNext
    have hineq := hcentered row next hrowNext
    rw [tracelessExtend_generalAffineLatticePoint hsize,
      tracelessExtend_generalAffineLatticePoint hsize] at hineq
    have hcast : ((generalExtendInt rank size coordinates next : ℤ) : ℝ) ≤
        ((generalExtendInt rank size coordinates row : ℤ) : ℝ) := by
      have := (div_le_div_iff_of_pos_right hscale).1 hineq
      linarith
    exact_mod_cast hcast
  · intro hinteger row next hrowNext
    rw [tracelessExtend_generalAffineLatticePoint hsize,
      tracelessExtend_generalAffineLatticePoint hsize]
    apply (div_le_div_iff_of_pos_right hscale).2
    have hcast : ((generalExtendInt rank size coordinates next : ℤ) : ℝ) ≤
        ((generalExtendInt rank size coordinates row : ℤ) : ℝ) := by
      exact_mod_cast hinteger hrowNext
    linarith

theorem generalChartPoint_mem_chamber
    {rank size : ℕ} (hsize : 1 ≤ size)
    (chart : GeneralChartTuple rank size) :
    generalChartPoint chart ∈ regevChamber rank :=
  (generalAffineLatticePoint_mem_chamber_iff hsize chart.coordinates).2
    chart.antitone

theorem abs_tracelessExtend_le_rank_mul_norm
    {rank : ℕ} (coordinates : Fin rank → ℝ)
    (row : Fin (rank + 1)) :
    |tracelessExtend coordinates row| ≤ (rank : ℝ) * ‖coordinates‖ := by
  calc
    |tracelessExtend coordinates row| ≤
        regevCoordinateAbsSum coordinates :=
      abs_tracelessExtend_le_absSum coordinates row
    _ = ∑ index, ‖coordinates index‖ := by
      unfold regevCoordinateAbsSum
      apply Finset.sum_congr rfl
      intro index hindex
      rw [Real.norm_eq_abs]
    _ ≤ Fintype.card (Fin rank) • ‖coordinates‖ :=
      Pi.sum_norm_apply_le_norm coordinates
    _ = (rank : ℝ) * ‖coordinates‖ := by
      simp [Fintype.card_fin, nsmul_eq_mul]

theorem generalAffine_rawRow_reconstruct
    {rank size : ℕ} (hsize : 1 ≤ size)
    (coordinates : Fin rank → ℤ) (row : Fin (rank + 1)) :
    (((generalRegevCenterFloor rank size : ℤ) +
        generalExtendInt rank size coordinates row : ℤ) : ℝ) =
      generalRegevScale rank size ^ 2 +
        tracelessExtend (generalAffineLatticePoint rank size coordinates) row *
          generalRegevScale rank size := by
  rw [tracelessExtend_generalAffineLatticePoint hsize]
  have hscaleNe : generalRegevScale rank size ≠ 0 :=
    (generalRegevScale_pos (rank := rank) hsize).ne'
  have hscaleSquare : generalRegevScale rank size ^ 2 =
      (size : ℝ) / (rank + 1 : ℝ) := by
    unfold generalRegevScale
    rw [Real.sq_sqrt]
    positivity
  rw [hscaleSquare, generalRegevCenter_decompose rank size]
  push_cast
  field_simp [hscaleNe]
  ring

theorem generalAffine_lower_of_mem_closedBall
    {rank size : ℕ} (hsize : 1 ≤ size)
    (radius : ℝ) (_hradius : 0 ≤ radius)
    (hscale : (rank : ℝ) * radius ≤ generalRegevScale rank size)
    (coordinates : Fin rank → ℤ)
    (hball : generalAffineLatticePoint rank size coordinates ∈
      Metric.closedBall 0 radius) :
    ∀ row, -(generalRegevCenterFloor rank size : ℤ) ≤
      generalExtendInt rank size coordinates row := by
  intro row
  have hnorm : ‖generalAffineLatticePoint rank size coordinates‖ ≤ radius := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hball
  have hcoordinateAbs := abs_tracelessExtend_le_rank_mul_norm
    (generalAffineLatticePoint rank size coordinates) row
  have hlowerCentered :
      -(generalRegevScale rank size) ≤
        tracelessExtend (generalAffineLatticePoint rank size coordinates) row := by
    have habsLower := neg_abs_le
      (tracelessExtend (generalAffineLatticePoint rank size coordinates) row)
    have hrankNorm : (rank : ℝ) *
        ‖generalAffineLatticePoint rank size coordinates‖ ≤
          (rank : ℝ) * radius := by gcongr
    linarith
  have hreconstruct := generalAffine_rawRow_reconstruct
    hsize coordinates row
  have hscaleNonneg : 0 ≤ generalRegevScale rank size :=
    (generalRegevScale_pos hsize).le
  have hrawNonneg : (0 : ℝ) ≤
      (((generalRegevCenterFloor rank size : ℤ) +
        generalExtendInt rank size coordinates row : ℤ) : ℝ) := by
    rw [hreconstruct]
    nlinarith
  have hrawNonnegInt : (0 : ℤ) ≤
      (generalRegevCenterFloor rank size : ℤ) +
        generalExtendInt rank size coordinates row := by
    exact_mod_cast hrawNonneg
  omega

def GeneralCompactShape (rank size : ℕ) (radius : ℝ) :=
  {shape : BoundedPartition rank size //
    generalShapePoint shape ∈ Metric.closedBall 0 radius}

noncomputable instance generalCompactShapeFintype
    (rank size : ℕ) (radius : ℝ) :
    Fintype (GeneralCompactShape rank size radius) := by
  unfold GeneralCompactShape
  infer_instance

def GeneralCompactLatticePoint (rank size : ℕ) (radius : ℝ) :=
  {coordinates : Fin rank → ℤ //
    generalAffineLatticePoint rank size coordinates ∈ regevChamber rank ∧
    generalAffineLatticePoint rank size coordinates ∈ Metric.closedBall 0 radius}

theorem generalShapePoint_mem_chamber
    {rank size : ℕ} (hsize : 1 ≤ size)
    (shape : BoundedPartition rank size) :
    generalShapePoint shape ∈ regevChamber rank := by
  rw [generalShapePoint_eq_affineLatticePoint hsize]
  have hchart := generalChartPoint_mem_chamber hsize
    ((boundedPartitionGeneralChartEquiv rank size) shape)
  simpa [generalChartPoint] using hchart

noncomputable def generalCompactShapeLatticeEquiv
    (rank size : ℕ) (hsize : 1 ≤ size) (radius : ℝ) (hradius : 0 ≤ radius)
    (hscale : (rank : ℝ) * radius ≤ generalRegevScale rank size) :
    GeneralCompactShape rank size radius ≃
      GeneralCompactLatticePoint rank size radius := by
  let chartEquiv := boundedPartitionGeneralChartEquiv rank size
  exact {
    toFun := fun shape =>
      ⟨(chartEquiv shape.1).coordinates,
        generalChartPoint_mem_chamber hsize (chartEquiv shape.1),
        by
          change generalAffineLatticePoint rank size
            ((boundedPartitionGeneralChartEquiv rank size) shape.1).coordinates ∈
              Metric.closedBall 0 radius
          rw [boundedPartitionGeneralChartEquiv_coordinates]
          rw [← generalShapePoint_eq_affineLatticePoint hsize shape.1]
          exact shape.2⟩
    invFun := fun point =>
      let chart : GeneralChartTuple rank size :=
        ⟨point.1,
          (generalAffineLatticePoint_mem_chamber_iff hsize point.1).1 point.2.1,
          generalAffine_lower_of_mem_closedBall hsize radius hradius hscale
            point.1 point.2.2⟩
      ⟨chartEquiv.symm chart, by
        rw [generalShapePoint_eq_affineLatticePoint hsize]
        rw [← boundedPartitionGeneralChartEquiv_coordinates]
        change generalAffineLatticePoint rank size
          (chartEquiv (chartEquiv.symm chart)).coordinates ∈
            Metric.closedBall 0 radius
        rw [chartEquiv.apply_symm_apply]
        exact point.2.2⟩
    left_inv := fun shape => by
      apply Subtype.ext
      apply chartEquiv.injective
      rw [chartEquiv.apply_symm_apply]
    right_inv := fun point => by
      apply Subtype.ext
      change (chartEquiv (chartEquiv.symm _)).coordinates = point.1
      rw [chartEquiv.apply_symm_apply]
  }

end FibonacciRibbonKernel
