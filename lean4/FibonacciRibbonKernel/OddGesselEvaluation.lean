import FibonacciRibbonKernel.RealSeriesEvaluation

namespace FibonacciRibbonKernel

open PowerSeries

theorem realExponentialSeries_hasSum (parameter : ℝ) :
    RealPowerSeriesHasSum realExponentialSeries parameter
      (Real.exp parameter) := by
  unfold RealPowerSeriesHasSum realPowerSeriesTerm realExponentialSeries
  have h := NormedSpace.expSeries_div_hasSum_exp parameter
  rw [show (fun power : ℕ =>
      PowerSeries.coeff power
          (PowerSeries.map (Rat.castHom ℝ) (PowerSeries.exp ℚ)) *
        parameter ^ power) =
      fun power => parameter ^ power / (power.factorial : ℝ) by
    funext power
    rw [PowerSeries.coeff_map, PowerSeries.coeff_exp]
    simp only [map_div₀, map_one]
    have hcast :
        (Rat.castHom ℝ) ((algebraMap ℚ ℚ) (power.factorial : ℚ)) =
          (power.factorial : ℝ) := by
      norm_num
    rw [hcast]
    ring]
  simpa only [Real.exp_eq_exp_ℝ] using h

theorem symmetricLiteralBesselJR_hasSum
    (order : ℤ) (parameter : ℝ) :
    RealPowerSeriesHasSum (symmetricLiteralBesselJR order) parameter
      (realBesselCosineIntegral order parameter / Real.pi) := by
  have hraw := realBesselIntegralSeries_hasSum order parameter
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hdiv := hraw.div_const Real.pi
  unfold RealPowerSeriesHasSum realPowerSeriesTerm
  apply HasSum.congr_fun hdiv
  intro power
  rw [realBesselIntegralSeries_coeff_eq,
    symmetricLiteralBesselJR_coeff]
  field_simp

theorem oddFormalGesselMatrixR_entry_hasSum
    (dimension : ℕ) (parameter : ℝ)
    (row column : Fin dimension) :
    RealPowerSeriesHasSum
      (oddFormalGesselMatrixR dimension row column) parameter
      ((realBesselCosineIntegral ((row.val : ℤ) - column.val) parameter -
          realBesselCosineIntegral
            ((row.val + column.val + 2 : ℕ) : ℤ) parameter) /
        Real.pi) := by
  unfold oddFormalGesselMatrixR
  have hleft := symmetricLiteralBesselJR_hasSum
    ((row.val : ℤ) - column.val) parameter
  have hright := symmetricLiteralBesselJR_hasSum
    ((row.val + column.val + 2 : ℕ) : ℤ) parameter
  convert hleft.sub hright using 1
  ring

theorem oddFormalGesselDet_two_hasSum
    (parameter : ℝ) :
    RealPowerSeriesHasSum (oddFormalGesselMatrixR 2).det parameter
      ((1 / Real.pi) ^ 2 * (oddRealGesselMatrix 2 parameter).det) := by
  rw [Matrix.det_fin_two]
  have h00 := oddFormalGesselMatrixR_entry_hasSum 2 parameter 0 0
  have h11 := oddFormalGesselMatrixR_entry_hasSum 2 parameter 1 1
  have h01 := oddFormalGesselMatrixR_entry_hasSum 2 parameter 0 1
  have h10 := oddFormalGesselMatrixR_entry_hasSum 2 parameter 1 0
  have hdet := (h00.mul h11).sub (h01.mul h10)
  convert hdet using 1
  rw [Matrix.det_fin_two]
  unfold oddRealGesselMatrix
  simp only [Fin.val_zero, Fin.val_one]
  ring

theorem oddFormalGesselSeriesR_two_hasSum
    (parameter : ℝ) :
    RealPowerSeriesHasSum (oddFormalGesselSeriesR 2) parameter
      (Real.exp parameter * (1 / Real.pi) ^ 2 *
        (oddRealGesselMatrix 2 parameter).det) := by
  unfold oddFormalGesselSeriesR
  have hexp := realExponentialSeries_hasSum parameter
  have hdet := oddFormalGesselDet_two_hasSum parameter
  convert hexp.mul hdet using 1
  ring

end FibonacciRibbonKernel
