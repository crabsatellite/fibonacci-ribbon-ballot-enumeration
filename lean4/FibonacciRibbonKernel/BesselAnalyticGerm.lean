import FibonacciRibbonKernel.BesselSeriesConvergence
import Mathlib.Analysis.Analytic.ConvergenceRadius
import Mathlib.Analysis.Analytic.OfScalars

namespace FibonacciRibbonKernel

noncomputable def besselOrdinaryFPowerSeries
    (degree : ℕ) (index : Fin (degree + 1)) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ fun coefficient =>
    (besselFactorialCoeff degree coefficient index : ℝ)

noncomputable def oddBesselOrdinaryFPowerSeries
    (degree : ℕ) (index : Fin (degree + 1)) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ fun coefficient =>
    (oddBesselFactorialCoeff degree coefficient index : ℝ)

noncomputable def besselSafeRadius (degree : ℕ) : NNReal :=
  Real.toNNReal (1 / (2 * degree + 1 : ℝ))

noncomputable def oddBesselSafeRadius (degree : ℕ) : NNReal :=
  Real.toNNReal (1 / (2 * degree + 2 : ℝ))

theorem besselSafeRadius_pos (degree : ℕ) :
    0 < besselSafeRadius degree := by
  rw [besselSafeRadius, Real.toNNReal_pos]
  positivity

theorem oddBesselSafeRadius_pos (degree : ℕ) :
    0 < oddBesselSafeRadius degree := by
  rw [oddBesselSafeRadius, Real.toNNReal_pos]
  positivity

theorem besselOrdinaryFPowerSeries_radius_pos
    (degree : ℕ) (index : Fin (degree + 1)) :
    0 < (besselOrdinaryFPowerSeries degree index).radius := by
  let radius := besselSafeRadius degree
  let series := besselOrdinaryFPowerSeries degree index
  have hx : (2 * degree : ℝ) * |(radius : ℝ)| < 1 := by
    dsimp only [radius, besselSafeRadius]
    rw [Real.coe_toNNReal _ (by positivity)]
    rw [abs_of_pos (by positivity)]
    rw [one_div, mul_inv_lt_iff₀ (by positivity : (0 : ℝ) < 2 * degree + 1)]
    linarith
  have habsolute := besselOrdinaryEval_summable_abs degree index radius hx
  have hsummable : Summable (fun coefficient : ℕ =>
      ‖series coefficient‖ * (radius : ℝ) ^ coefficient) := by
    apply habsolute.congr
    intro coefficient
    have hcoefficientNonneg :
        (0 : ℝ) ≤ besselFactorialCoeff degree coefficient index := by
      exact_mod_cast besselFactorialCoeff_nonneg degree coefficient index
    have hradiusNonneg : (0 : ℝ) ≤ (radius : ℝ) := radius.property
    rw [abs_mul, abs_pow, abs_of_nonneg hcoefficientNonneg,
      abs_of_nonneg hradiusNonneg]
    congr 1
    dsimp only [series, besselOrdinaryFPowerSeries]
    rw [FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs,
      abs_of_nonneg hcoefficientNonneg]
  have hradiusLe : (radius : ENNReal) ≤ series.radius :=
    series.le_radius_of_summable_norm hsummable
  have hradiusPos : 0 < radius := by
    simpa only [radius] using besselSafeRadius_pos degree
  have hseriesRadius : (0 : ENNReal) < series.radius :=
    (ENNReal.coe_pos.mpr hradiusPos).trans_le hradiusLe
  simpa only [series] using hseriesRadius

theorem oddBesselOrdinaryFPowerSeries_radius_pos
    (degree : ℕ) (index : Fin (degree + 1)) :
    0 < (oddBesselOrdinaryFPowerSeries degree index).radius := by
  let radius := oddBesselSafeRadius degree
  let series := oddBesselOrdinaryFPowerSeries degree index
  have hx : (2 * degree + 1 : ℝ) * |(radius : ℝ)| < 1 := by
    dsimp only [radius, oddBesselSafeRadius]
    rw [Real.coe_toNNReal _ (by positivity)]
    rw [abs_of_pos (by positivity)]
    rw [one_div, mul_inv_lt_iff₀ (by positivity : (0 : ℝ) < 2 * degree + 2)]
    linarith
  have habsolute := oddBesselOrdinaryEval_summable_abs degree index radius hx
  have hsummable : Summable (fun coefficient : ℕ =>
      ‖series coefficient‖ * (radius : ℝ) ^ coefficient) := by
    apply habsolute.congr
    intro coefficient
    have hcoefficientNonneg :
        (0 : ℝ) ≤ oddBesselFactorialCoeff degree coefficient index := by
      exact_mod_cast oddBesselFactorialCoeff_nonneg degree coefficient index
    have hradiusNonneg : (0 : ℝ) ≤ (radius : ℝ) := radius.property
    rw [abs_mul, abs_pow, abs_of_nonneg hcoefficientNonneg,
      abs_of_nonneg hradiusNonneg]
    congr 1
    dsimp only [series, oddBesselOrdinaryFPowerSeries]
    rw [FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs,
      abs_of_nonneg hcoefficientNonneg]
  have hradiusLe : (radius : ENNReal) ≤ series.radius :=
    series.le_radius_of_summable_norm hsummable
  have hradiusPos : 0 < radius := by
    simpa only [radius] using oddBesselSafeRadius_pos degree
  have hseriesRadius : (0 : ENNReal) < series.radius :=
    (ENNReal.coe_pos.mpr hradiusPos).trans_le hradiusLe
  simpa only [series] using hseriesRadius

theorem besselOrdinaryFPowerSeries_sum_eq
    (degree : ℕ) (index : Fin (degree + 1)) :
    (besselOrdinaryFPowerSeries degree index).sum =
      besselOrdinaryEval degree index := by
  funext x
  unfold besselOrdinaryFPowerSeries besselOrdinaryEval
  unfold FormalMultilinearSeries.sum
  apply tsum_congr
  intro coefficient
  simp [smul_eq_mul, mul_comm]

theorem oddBesselOrdinaryFPowerSeries_sum_eq
    (degree : ℕ) (index : Fin (degree + 1)) :
    (oddBesselOrdinaryFPowerSeries degree index).sum =
      oddBesselOrdinaryEval degree index := by
  funext x
  unfold oddBesselOrdinaryFPowerSeries oddBesselOrdinaryEval
  unfold FormalMultilinearSeries.sum
  apply tsum_congr
  intro coefficient
  simp [smul_eq_mul, mul_comm]

theorem besselOrdinaryEval_hasFPowerSeriesOnBall
    (degree : ℕ) (index : Fin (degree + 1)) :
    HasFPowerSeriesOnBall (besselOrdinaryEval degree index)
      (besselOrdinaryFPowerSeries degree index) 0
      (besselOrdinaryFPowerSeries degree index).radius := by
  have hseries :=
    (besselOrdinaryFPowerSeries degree index).hasFPowerSeriesOnBall
      (besselOrdinaryFPowerSeries_radius_pos degree index)
  rw [besselOrdinaryFPowerSeries_sum_eq] at hseries
  exact hseries

theorem oddBesselOrdinaryEval_hasFPowerSeriesOnBall
    (degree : ℕ) (index : Fin (degree + 1)) :
    HasFPowerSeriesOnBall (oddBesselOrdinaryEval degree index)
      (oddBesselOrdinaryFPowerSeries degree index) 0
      (oddBesselOrdinaryFPowerSeries degree index).radius := by
  have hseries :=
    (oddBesselOrdinaryFPowerSeries degree index).hasFPowerSeriesOnBall
      (oddBesselOrdinaryFPowerSeries_radius_pos degree index)
  rw [oddBesselOrdinaryFPowerSeries_sum_eq] at hseries
  exact hseries

end FibonacciRibbonKernel
