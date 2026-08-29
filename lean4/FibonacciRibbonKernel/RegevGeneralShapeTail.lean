import FibonacciRibbonKernel.RegevShiftedGaussian

namespace FibonacciRibbonKernel

open Set
open scoped Classical

theorem generalShapePoint_injective
    {rank size : ℕ} (hsize : 1 ≤ size) :
    Function.Injective
      (generalShapePoint : BoundedPartition rank size → Fin rank → ℝ) := by
  intro first second hpoints
  apply Subtype.ext
  funext row
  apply Fin.ext
  have hcentered : regevCenteredRow first row =
      regevCenteredRow second row := by
    calc
      regevCenteredRow first row =
          tracelessExtend (generalShapePoint first) row :=
        (tracelessExtend_generalShapePoint first row).symm
      _ = tracelessExtend (generalShapePoint second) row := by rw [hpoints]
      _ = regevCenteredRow second row :=
        tracelessExtend_generalShapePoint second row
  have hfirst := regevCenteredRow_reconstruct first hsize row
  have hsecond := regevCenteredRow_reconstruct second hsize row
  rw [hcentered] at hfirst
  exact_mod_cast hfirst.trans hsecond.symm

theorem generalShapeIntegerCoordinates_injective
    {rank size : ℕ} (hsize : 1 ≤ size) :
    Function.Injective
      (generalShapeIntegerCoordinates :
        BoundedPartition rank size → Fin rank → ℤ) := by
  intro first second hcoordinates
  apply generalShapePoint_injective hsize
  rw [generalShapePoint_eq_affineLatticePoint hsize first]
  rw [generalShapePoint_eq_affineLatticePoint hsize second]
  rw [hcoordinates]

theorem generalRegevScale_one_le
    {rank size : ℕ} (hsize : rank + 1 ≤ size) :
    1 ≤ generalRegevScale rank size := by
  unfold generalRegevScale
  rw [Real.le_sqrt (by norm_num) (by positivity)]
  norm_num
  have hdimension : (0 : ℝ) < rank + 1 := by positivity
  rw [le_div_iff₀ hdimension]
  have hcast : ((rank + 1 : ℕ) : ℝ) ≤ size := by exact_mod_cast hsize
  simpa using hcast

theorem abs_generalRegevShift_le_one
    {rank size : ℕ} (hsize : rank + 1 ≤ size) :
    |generalRegevShift rank size| ≤ 1 := by
  have hscale := generalRegevScale_one_le hsize
  have hscalePos : 0 < generalRegevScale rank size := zero_lt_one.trans_le hscale
  unfold generalRegevShift
  rw [abs_div, abs_neg,
    abs_of_nonneg (generalRegevCenterFraction_nonneg rank size),
    abs_of_pos hscalePos]
  exact (div_le_one hscalePos).2
    ((generalRegevCenterFraction_lt_one rank size).le.trans hscale)

def GeneralTailShape (rank size : ℕ) (radius : ℝ) :=
  {shape : BoundedPartition rank size //
    generalShapePoint shape ∉ Metric.closedBall 0 radius}

noncomputable instance generalTailShapeFintype
    (rank size : ℕ) (radius : ℝ) :
    Fintype (GeneralTailShape rank size radius) := by
  unfold GeneralTailShape
  infer_instance

noncomputable def generalTailShapeToShiftedTail
    (rank size : ℕ) (hsize : 1 ≤ size) (radius : ℝ) :
    GeneralTailShape rank size radius →
      regevShiftedPiGaussianTailIndex
        (generalRegevScale rank size) (generalRegevShift rank size)
        radius rank :=
  fun shape =>
    ⟨generalShapeIntegerCoordinates shape.1, by
      have hnot : ¬ dist (generalShapePoint shape.1) 0 ≤ radius := by
        simpa only [Metric.mem_closedBall] using shape.2
      have hstrict : radius < ‖generalShapePoint shape.1‖ := by
        simpa only [dist_zero_right] using lt_of_not_ge hnot
      rw [generalShapePoint_eq_affineLatticePoint
        hsize shape.1] at hstrict
      exact hstrict⟩

theorem generalTailShapeToShiftedTail_injective
    {rank size : ℕ} (hsize : 1 ≤ size) (radius : ℝ) :
    Function.Injective
      (generalTailShapeToShiftedTail rank size hsize radius) := by
  intro first second heq
  apply Subtype.ext
  apply generalShapeIntegerCoordinates_injective hsize
  exact congrArg Subtype.val heq

theorem regevCoordinateSeparableGaussian_general_eq_shiftedPi
    {rank size : ℕ} (hsize : 1 ≤ size)
    (shape : BoundedPartition rank size) :
    regevCoordinateSeparableGaussian rank (generalShapePoint shape) =
      regevShiftedPiGaussian
        (regevCoordinateGaussianCoefficient rank / 2)
        (generalRegevScale rank size) (generalRegevShift rank size) rank
        (generalShapeIntegerCoordinates shape) := by
  rw [generalShapePoint_eq_affineLatticePoint hsize shape]
  unfold regevCoordinateSeparableGaussian regevShiftedPiGaussian
  unfold regevPiProduct regevShiftedGaussianLine
  unfold generalAffineLatticePoint
  rfl

theorem abs_matsumoto_general_le_shiftedPiGaussian
    {rank size : ℕ} (hsize : 1 ≤ size)
    (shape : BoundedPartition rank size) :
    |matsumotoLocalNormalizedTableau shape| ≤
      regevCoordinateAbsorptionConstant rank *
        regevShiftedPiGaussian
          (regevCoordinateGaussianCoefficient rank / 2)
          (generalRegevScale rank size) (generalRegevShift rank size) rank
          (generalShapeIntegerCoordinates shape) := by
  calc
    |matsumotoLocalNormalizedTableau shape| ≤
        regevCoordinateDominatingKernel rank (generalShapePoint shape) := by
      have hbound := abs_matsumotoLocalNormalizedTableau_gaussian_bound
        shape hsize
      unfold regevCoordinateDominatingKernel
      rw [show regevRowEnvelopeProduct shape =
          regevCoordinateRowEnvelope rank (generalShapePoint shape) by
        unfold regevRowEnvelopeProduct regevCoordinateRowEnvelope
        apply Finset.prod_congr rfl
        intro row hrow
        rw [tracelessExtend_generalShapePoint shape row]] at hbound
      rw [show regevPairEnvelopeProduct shape =
          regevCoordinatePairEnvelope rank (generalShapePoint shape) by
        unfold regevPairEnvelopeProduct regevCoordinatePairEnvelope
        apply Finset.prod_congr rfl
        intro row hrow
        apply Finset.prod_congr rfl
        intro next hnext
        rw [tracelessExtend_generalShapePoint shape row,
          tracelessExtend_generalShapePoint shape next]] at hbound
      rw [show (∑ row : Fin (rank + 1),
          regevCenteredRow shape row ^ 2 /
            (2 * regevEntropyDenominator rank)) =
          ∑ row : Fin (rank + 1),
            tracelessExtend (generalShapePoint shape) row ^ 2 /
              (2 * regevEntropyDenominator rank) by
        apply Finset.sum_congr rfl
        intro row hrow
        rw [tracelessExtend_generalShapePoint shape row]] at hbound
      exact hbound
    _ ≤ regevCoordinateAbsorptionConstant rank *
        regevCoordinateSeparableGaussian rank (generalShapePoint shape) :=
      regevCoordinateDominatingKernel_le_separableGaussian rank _
    _ = _ := by
      rw [regevCoordinateSeparableGaussian_general_eq_shiftedPi hsize shape]

noncomputable def generalTailAbsoluteNormalizedAverage
    (rank size : ℕ) (radius : ℝ) : ℝ :=
  (∑ shape : GeneralTailShape rank size radius,
    |matsumotoLocalNormalizedTableau shape.1|) /
      generalRegevScale rank size ^ rank

theorem generalTailAbsoluteNormalizedAverage_bound
    (rank : ℕ) {size : ℕ} (hsize : rank + 1 ≤ size)
    (radius : ℝ) (hradius : 0 ≤ radius) :
    generalTailAbsoluteNormalizedAverage rank size radius ≤
      regevCoordinateAbsorptionConstant rank *
        (Real.exp (-((regevCoordinateGaussianCoefficient rank / 2) / 2) *
            radius ^ 2) *
          (Real.exp ((regevCoordinateGaussianCoefficient rank / 2) / 2) *
            (2 + 2 * Real.sqrt (Real.pi /
              ((regevCoordinateGaussianCoefficient rank / 2) / 4)))) ^ rank) := by
  let coefficient := regevCoordinateGaussianCoefficient rank / 2
  let scale := generalRegevScale rank size
  let shift := generalRegevShift rank size
  have hsizeOne : 1 ≤ size := (Nat.succ_le_succ (Nat.zero_le rank)).trans hsize
  let map := generalTailShapeToShiftedTail rank size hsizeOne radius
  have hcoefficient : 0 < coefficient := by
    dsimp only [coefficient]
    positivity [regevCoordinateGaussianCoefficient_pos rank]
  have hscale : 1 ≤ scale := generalRegevScale_one_le hsize
  have hshift : |shift| ≤ 1 := abs_generalRegevShift_le_one hsize
  have hconstantNonneg : 0 ≤ regevCoordinateAbsorptionConstant rank := by
    unfold regevCoordinateAbsorptionConstant regevCoordinateEnvelopeConstant
    positivity
  have hleft : Summable (fun shape : GeneralTailShape rank size radius =>
      |matsumotoLocalNormalizedTableau shape.1|) := Summable.of_finite
  have hgaussian := summable_regevShiftedPiGaussian
    hcoefficient (zero_lt_one.trans_le hscale) hshift rank
  have hgaussianTail := hgaussian.subtype
    (regevShiftedPiGaussianTailIndex scale shift radius rank)
  have hright := hgaussianTail.mul_left
    (regevCoordinateAbsorptionConstant rank)
  have hsum :
      (∑' shape : GeneralTailShape rank size radius,
        |matsumotoLocalNormalizedTableau shape.1|) ≤
      ∑' point : regevShiftedPiGaussianTailIndex scale shift radius rank,
        regevCoordinateAbsorptionConstant rank *
          regevShiftedPiGaussian coefficient scale shift rank point.1 := by
    exact hleft.tsum_le_tsum_of_inj map
      (generalTailShapeToShiftedTail_injective hsizeOne radius)
      (fun point _ => mul_nonneg hconstantNonneg
        (regevShiftedPiGaussian_nonneg coefficient scale shift rank point.1))
      (fun shape => abs_matsumoto_general_le_shiftedPiGaussian
        hsizeOne shape.1)
      hright
  have hnormalized := div_le_div_of_nonneg_right hsum
    (pow_nonneg (zero_lt_one.trans_le hscale).le rank)
  have htail := regevShiftedPiGaussian_tail_bound
    hcoefficient hscale hshift hradius rank
  unfold generalTailAbsoluteNormalizedAverage
  calc
    _ = (∑' shape : GeneralTailShape rank size radius,
        |matsumotoLocalNormalizedTableau shape.1|) / scale ^ rank := by
      rw [tsum_fintype]
    _ ≤ (∑' point : regevShiftedPiGaussianTailIndex scale shift radius rank,
        regevCoordinateAbsorptionConstant rank *
          regevShiftedPiGaussian coefficient scale shift rank point.1) /
            scale ^ rank := hnormalized
    _ = regevCoordinateAbsorptionConstant rank *
        ((∑' point : regevShiftedPiGaussianTailIndex scale shift radius rank,
          regevShiftedPiGaussian coefficient scale shift rank point.1) /
            scale ^ rank) := by
      rw [tsum_mul_left]
      ring
    _ ≤ regevCoordinateAbsorptionConstant rank *
        (Real.exp (-(coefficient / 2) * radius ^ 2) *
          (Real.exp (coefficient / 2) *
            (2 + 2 * Real.sqrt (Real.pi / (coefficient / 4)))) ^ rank) :=
      mul_le_mul_of_nonneg_left htail hconstantNonneg
    _ = _ := by rfl

end FibonacciRibbonKernel
