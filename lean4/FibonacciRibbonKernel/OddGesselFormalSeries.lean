import FibonacciRibbonKernel.RealBesselFormalBridge

namespace FibonacciRibbonKernel

open PowerSeries

noncomputable def realExponentialSeries : ℝ⟦X⟧ :=
  PowerSeries.map (Rat.castHom ℝ) (PowerSeries.exp ℚ)

noncomputable def oddFormalGesselMatrixR
    (dimension : ℕ) : Matrix (Fin dimension) (Fin dimension) ℝ⟦X⟧ :=
  fun row column =>
    symmetricLiteralBesselJR ((row.val : ℤ) - column.val) -
      symmetricLiteralBesselJR
        ((row.val + column.val + 2 : ℕ) : ℤ)

noncomputable def oddFormalGesselSeriesR (dimension : ℕ) : ℝ⟦X⟧ :=
  realExponentialSeries * (oddFormalGesselMatrixR dimension).det

theorem realBesselIntegralMatrixSeries_eq_smul
    (dimension : ℕ) :
    (fun row column : Fin dimension =>
      realBesselIntegralSeries ((row.val : ℤ) - column.val) -
        realBesselIntegralSeries
          ((row.val + column.val + 2 : ℕ) : ℤ)) =
      fun row column => PowerSeries.C Real.pi *
        oddFormalGesselMatrixR dimension row column := by
  ext row column
  unfold oddFormalGesselMatrixR
  rw [realBesselIntegralSeries_eq_literal,
    realBesselIntegralSeries_eq_literal]
  ring

theorem symmetricLiteralBesselJR_intCast (order : ℕ) :
    symmetricLiteralBesselJR (order : ℤ) =
      PowerSeries.map (Rat.castHom ℝ) (literalBesselJ order) := by
  unfold symmetricLiteralBesselJR symmetricLiteralBesselJ
  rw [Int.natAbs_natCast]

theorem oddFormalGesselSeriesR_two :
    oddFormalGesselSeriesR 2 =
      PowerSeries.map (Rat.castHom ℝ) gesselHeightFiveSeries := by
  unfold oddFormalGesselSeriesR oddFormalGesselMatrixR
  rw [Matrix.det_fin_two]
  simp only [Fin.val_zero, Fin.val_one]
  change realExponentialSeries *
      ((symmetricLiteralBesselJR 0 - symmetricLiteralBesselJR 2) *
          (symmetricLiteralBesselJR 0 - symmetricLiteralBesselJR 4) -
        (symmetricLiteralBesselJR (-1) - symmetricLiteralBesselJR 3) *
          (symmetricLiteralBesselJR 1 - symmetricLiteralBesselJR 3)) = _
  rw [symmetricLiteralBesselJR_neg 1]
  change realExponentialSeries *
      ((PowerSeries.map (Rat.castHom ℝ) (literalBesselJ 0) -
          PowerSeries.map (Rat.castHom ℝ) (literalBesselJ 2)) *
        (PowerSeries.map (Rat.castHom ℝ) (literalBesselJ 0) -
          PowerSeries.map (Rat.castHom ℝ) (literalBesselJ 4)) -
        (PowerSeries.map (Rat.castHom ℝ) (literalBesselJ 1) -
          PowerSeries.map (Rat.castHom ℝ) (literalBesselJ 3)) *
        (PowerSeries.map (Rat.castHom ℝ) (literalBesselJ 1) -
          PowerSeries.map (Rat.castHom ℝ) (literalBesselJ 3))) = _
  unfold realExponentialSeries gesselHeightFiveSeries
  simp only [map_mul, map_sub, map_pow]
  ring

theorem mapped_heightFive_factorialSeries_eq_oddFormalGessel :
    PowerSeries.map (Rat.castHom ℝ)
        (factorialSeries fun size => (heightFiveTableauCount size : ℚ)) =
      oddFormalGesselSeriesR 2 := by
  rw [factorialSeries_heightFiveTableauCount_eq_gessel,
    oddFormalGesselSeriesR_two]

end FibonacciRibbonKernel
