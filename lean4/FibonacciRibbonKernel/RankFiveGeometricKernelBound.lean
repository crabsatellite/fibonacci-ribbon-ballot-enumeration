import FibonacciRibbonKernel.RankFiveGeometricPointwise

namespace FibonacciRibbonKernel

open scoped BigOperators

noncomputable def rankFiveGeometricGaussianCoefficient : ℝ :=
  2 / (5 * Real.pi ^ 2)

theorem rankFiveGeometricGaussianCoefficient_pos :
    0 < rankFiveGeometricGaussianCoefficient := by
  unfold rankFiveGeometricGaussianCoefficient
  positivity

theorem sum_sq_le_two_pi_sq_of_scaledCube
    {index : ℕ} {coordinates : Fin 2 → ℝ}
    (hcoordinates : coordinates ∈ positiveScaledCube 2 index) :
    ∑ coordinate, coordinates coordinate ^ 2 ≤
      2 * Real.pi ^ 2 * (index + 1 : ℝ) := by
  rw [show (∑ coordinate : Fin 2, coordinates coordinate ^ 2) =
      coordinates 0 ^ 2 + coordinates 1 ^ 2 by
    rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
    simp]
  have hzero := (hcoordinates 0 (Set.mem_univ 0)).2
  have hone := (hcoordinates 1 (Set.mem_univ 1)).2
  have hzeroPos := (hcoordinates 0 (Set.mem_univ 0)).1.le
  have honePos := (hcoordinates 1 (Set.mem_univ 1)).1.le
  have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ index + 1 by positivity)
  nlinarith [sq_le_sq₀ hzeroPos (by positivity) |>.2 hzero,
    sq_le_sq₀ honePos (by positivity) |>.2 hone]

theorem normalizedRankFiveGeometricKernel_nonneg
    {index : ℕ} {coordinates : Fin 2 → ℝ}
    (hscale : 0 ≤ oddCosineSumScale coordinates index) :
    0 ≤ normalizedRankFiveGeometricKernel coordinates index := by
  unfold normalizedRankFiveGeometricKernel
  exact pow_nonneg (div_nonneg hscale (by norm_num)) _

theorem normalizedRankFiveGeometricKernel_le_gaussian
    (index : ℕ) (coordinates : Fin 2 → ℝ)
    (hcube : coordinates ∈ positiveScaledCube 2 index)
    (hscaleMid : oddCosineScaleMidpoint 2 ≤
      oddCosineSumScale coordinates index) :
    normalizedRankFiveGeometricKernel coordinates index ≤
      Real.exp (4 / 5 : ℝ) *
        Real.exp (-rankFiveGeometricGaussianCoefficient *
          ∑ coordinate, coordinates coordinate ^ 2) := by
  have hscalePos : 0 < oddCosineSumScale coordinates index :=
    (oddCosineScaleMidpoint_gt_two (dimension := 2) (by norm_num)).trans_le
      hscaleMid |>.trans' zero_lt_two
  rcases index with _ | index
  · unfold normalizedRankFiveGeometricKernel
    rw [pow_zero]
    have hsquares : (∑ coordinate, coordinates coordinate ^ 2) ≤
        2 * Real.pi ^ 2 := by
      simpa using sum_sq_le_two_pi_sq_of_scaledCube hcube
    have hcoefficientPos : 0 < 2 / (5 * Real.pi ^ 2) := by
      positivity
    have hproduct :
        (2 / (5 * Real.pi ^ 2)) *
            (∑ coordinate, coordinates coordinate ^ 2) ≤ 4 / 5 := by
      calc
        (2 / (5 * Real.pi ^ 2)) *
            (∑ coordinate, coordinates coordinate ^ 2) ≤
            (2 / (5 * Real.pi ^ 2)) * (2 * Real.pi ^ 2) :=
          mul_le_mul_of_nonneg_left hsquares hcoefficientPos.le
        _ = 4 / 5 := by
          field_simp [ne_of_gt Real.pi_pos]
          norm_num
    rw [← Real.exp_add]
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    unfold rankFiveGeometricGaussianCoefficient
    linarith
  · let current := oddCosineSumScale coordinates (index + 1)
    let ratio := current / 5
    let squares : ℝ := ∑ coordinate, coordinates coordinate ^ 2
    have hratioPos : 0 < ratio := by
      dsimp only [ratio, current]
      positivity
    have hlog := Real.log_le_sub_one_of_pos hratioPos
    have hcoordinate : ∀ coordinate,
        |coordinates coordinate| ≤
          Real.pi * Real.sqrt (((index + 1 : ℕ) : ℝ) + 1) := by
      intro coordinate
      have hmem := hcube coordinate (Set.mem_univ coordinate)
      rw [abs_of_pos hmem.1]
      exact hmem.2
    have hdeficit := cosineSumScale_le_quadratic coordinates hcoordinate
    have hsquaresNonneg : 0 ≤ squares := by positivity
    have hsquaresEq : squares = coordinates 0 ^ 2 + coordinates 1 ^ 2 := by
      dsimp only [squares]
      rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
      simp
    have hscaledLog :
        (index + 1 : ℝ) * Real.log ratio ≤
          -rankFiveGeometricGaussianCoefficient * squares := by
      have hcurrent : current - 5 ≤
          -(4 / (Real.pi ^ 2 * (index + 2 : ℝ))) * squares := by
        dsimp only [current]
        unfold oddCosineSumScale
        rw [hsquaresEq]
        rw [show (index + 2 : ℝ) = (((index + 1 : ℕ) : ℝ) + 1) by
          push_cast
          ring]
        norm_num at hdeficit ⊢
        linarith
      have hratioSub : ratio - 1 = (current - 5) / 5 := by
        dsimp only [ratio]
        ring
      have hmul := mul_le_mul_of_nonneg_left hlog
        (show (0 : ℝ) ≤ index + 1 by positivity)
      rw [hratioSub] at hmul
      unfold rankFiveGeometricGaussianCoefficient
      have hindexRatio : (1 / 2 : ℝ) ≤
          (index + 1 : ℝ) / (index + 2 : ℝ) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      have hindexRatioNonneg : 0 ≤
          (index + 1 : ℝ) / (index + 2 : ℝ) :=
        (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hindexRatio
      have hscaledCurrent :
          (index + 1 : ℝ) * ((current - 5) / 5) ≤
            -(4 / (5 * Real.pi ^ 2)) *
              ((index + 1 : ℝ) / (index + 2 : ℝ)) * squares := by
        calc
          (index + 1 : ℝ) * ((current - 5) / 5) =
              ((index + 1 : ℝ) / 5) * (current - 5) := by ring
          _ ≤ ((index + 1 : ℝ) / 5) *
              (-(4 / (Real.pi ^ 2 * (index + 2 : ℝ))) * squares) :=
            mul_le_mul_of_nonneg_left hcurrent (by positivity)
          _ = -(4 / (5 * Real.pi ^ 2)) *
              ((index + 1 : ℝ) / (index + 2 : ℝ)) * squares := by
            field_simp [ne_of_gt Real.pi_pos]
      have hcoefficient :
          -(4 / (5 * Real.pi ^ 2)) *
              ((index + 1 : ℝ) / (index + 2 : ℝ)) ≤
            -(2 / (5 * Real.pi ^ 2)) := by
        have h := mul_le_mul_of_nonpos_left hindexRatio
          (neg_nonpos.mpr (show 0 ≤ 4 / (5 * Real.pi ^ 2) by positivity))
        calc
          -(4 / (5 * Real.pi ^ 2)) *
              ((index + 1 : ℝ) / (index + 2 : ℝ)) ≤
              -(4 / (5 * Real.pi ^ 2)) * (1 / 2) := h
          _ = -(2 / (5 * Real.pi ^ 2)) := by
            field_simp [ne_of_gt Real.pi_pos]
            norm_num
      have hweighted := mul_le_mul_of_nonneg_right hcoefficient hsquaresNonneg
      calc
        (index + 1 : ℝ) * Real.log ratio ≤
            (index + 1 : ℝ) * ((current - 5) / 5) := hmul
        _ ≤ -(4 / (5 * Real.pi ^ 2)) *
              ((index + 1 : ℝ) / (index + 2 : ℝ)) * squares := hscaledCurrent
        _ ≤ -(2 / (5 * Real.pi ^ 2)) * squares := hweighted
    unfold normalizedRankFiveGeometricKernel
    change ratio ^ (index + 1) ≤ _
    calc
      ratio ^ (index + 1) =
          Real.exp ((index + 1 : ℝ) * Real.log ratio) := by
        have hcast : (index + 1 : ℝ) = (((index + 1 : ℕ) : ℕ) : ℝ) := by
          norm_num
        rw [hcast, Real.exp_nat_mul, Real.exp_log hratioPos]
      _ ≤ Real.exp (-rankFiveGeometricGaussianCoefficient * squares) :=
        Real.exp_le_exp.mpr hscaledLog
      _ ≤ Real.exp (4 / 5 : ℝ) *
          Real.exp (-rankFiveGeometricGaussianCoefficient * squares) := by
        exact le_mul_of_one_le_left (Real.exp_pos _).le
          (by
            rw [← Real.exp_zero]
            exact Real.exp_le_exp.mpr (by norm_num))

end FibonacciRibbonKernel
