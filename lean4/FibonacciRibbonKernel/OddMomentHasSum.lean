import FibonacciRibbonKernel.OddGesselEvaluation

namespace FibonacciRibbonKernel

open MeasureTheory
open NormedSpace
open scoped BigOperators

noncomputable def oddWeylMomentSeriesTerm
    (dimension : ℕ) (parameter : ℝ) (power : ℕ)
    (angles : Fin dimension → ℝ) : ℝ :=
  oddWeylAngleWeight dimension angles *
    oddCosineCubeScale angles ^ power /
      (power.factorial : ℝ) * parameter ^ power

theorem abs_oddCosineCubeScale_le
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    |oddCosineCubeScale angles| ≤ 2 * dimension + 1 := by
  unfold oddCosineCubeScale cosineCubeScale
  calc
    |1 + 2 * ∑ coordinate, Real.cos (angles coordinate)| ≤
        1 + |2 * ∑ coordinate, Real.cos (angles coordinate)| := by
      simpa using abs_add_le (1 : ℝ)
        (2 * ∑ coordinate, Real.cos (angles coordinate))
    _ = 1 + 2 * |∑ coordinate, Real.cos (angles coordinate)| := by
      rw [abs_mul]
      norm_num
    _ ≤ 1 + 2 * ∑ _coordinate : Fin dimension, (1 : ℝ) := by
      gcongr
      calc
        |∑ coordinate, Real.cos (angles coordinate)| ≤
            ∑ coordinate, |Real.cos (angles coordinate)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _coordinate : Fin dimension, (1 : ℝ) := by
          gcongr with coordinate
          exact Real.abs_cos_le_one _
    _ = 2 * dimension + 1 := by
      simp [mul_comm, add_comm]

theorem integrable_norm_oddWeylAngleWeight (dimension : ℕ) :
    Integrable (fun angles : Fin dimension → ℝ =>
      ‖oddWeylAngleWeight dimension angles‖)
      (cosineCubeProductMeasure dimension) :=
  (integrable_continuous_cosineCube
    (continuous_oddWeylAngleWeight dimension)).norm

theorem integrable_oddWeylMomentSeriesTerm
    (dimension : ℕ) (parameter : ℝ) (power : ℕ) :
    Integrable (oddWeylMomentSeriesTerm dimension parameter power)
      (cosineCubeProductMeasure dimension) := by
  apply integrable_continuous_cosineCube
  unfold oddWeylMomentSeriesTerm oddCosineCubeScale
  exact (((continuous_oddWeylAngleWeight dimension).mul
    ((continuous_const.add (continuous_cosineCubeScale dimension)).pow power)).div_const _).mul
      continuous_const

theorem norm_oddWeylMomentSeriesTerm_le
    (dimension : ℕ) (parameter : ℝ) (power : ℕ)
    (angles : Fin dimension → ℝ) :
    ‖oddWeylMomentSeriesTerm dimension parameter power angles‖ ≤
      ‖oddWeylAngleWeight dimension angles‖ *
        ((2 * dimension + 1 : ℝ) * |parameter|) ^ power /
          (power.factorial : ℝ) := by
  unfold oddWeylMomentSeriesTerm
  simp only [norm_mul, norm_div, Real.norm_eq_abs, norm_pow]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ power.factorial)]
  have hscale := abs_oddCosineCubeScale_le dimension angles
  calc
    ‖oddWeylAngleWeight dimension angles‖ *
          |oddCosineCubeScale angles| ^ power /
        (power.factorial : ℝ) * |parameter| ^ power ≤
      ‖oddWeylAngleWeight dimension angles‖ *
          (2 * dimension + 1 : ℝ) ^ power /
        (power.factorial : ℝ) * |parameter| ^ power := by
      gcongr
    _ = _ := by rw [mul_pow, Real.norm_eq_abs]; ring

theorem summable_oddWeylMomentBound
    (dimension : ℕ) (parameter : ℝ)
    (angles : Fin dimension → ℝ) :
    Summable (fun power : ℕ =>
      ‖oddWeylAngleWeight dimension angles‖ *
        ((2 * dimension + 1 : ℝ) * |parameter|) ^ power /
          (power.factorial : ℝ)) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp
    ((2 * dimension + 1 : ℝ) * |parameter|)).mul_left
      ‖oddWeylAngleWeight dimension angles‖
  rw [show (fun power : ℕ =>
      ‖oddWeylAngleWeight dimension angles‖ *
        ((2 * dimension + 1 : ℝ) * |parameter|) ^ power /
          (power.factorial : ℝ)) =
      fun power => ‖oddWeylAngleWeight dimension angles‖ *
        (((2 * dimension + 1 : ℝ) * |parameter|) ^ power /
          (power.factorial : ℝ)) by
    funext power
    ring]
  exact h.summable

theorem tsum_oddWeylMomentBound
    (dimension : ℕ) (parameter : ℝ)
    (angles : Fin dimension → ℝ) :
    (∑' power : ℕ,
      ‖oddWeylAngleWeight dimension angles‖ *
        ((2 * dimension + 1 : ℝ) * |parameter|) ^ power /
          (power.factorial : ℝ)) =
      ‖oddWeylAngleWeight dimension angles‖ *
        Real.exp ((2 * dimension + 1 : ℝ) * |parameter|) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp
    ((2 * dimension + 1 : ℝ) * |parameter|)).mul_left
      ‖oddWeylAngleWeight dimension angles‖
  rw [show (fun power : ℕ =>
      ‖oddWeylAngleWeight dimension angles‖ *
        ((2 * dimension + 1 : ℝ) * |parameter|) ^ power /
          (power.factorial : ℝ)) =
      fun power => ‖oddWeylAngleWeight dimension angles‖ *
        (((2 * dimension + 1 : ℝ) * |parameter|) ^ power /
          (power.factorial : ℝ)) by
    funext power
    ring]
  simpa only [Real.exp_eq_exp_ℝ] using h.tsum_eq

theorem hasSum_oddWeylMomentSeriesTerm_pointwise
    (dimension : ℕ) (parameter : ℝ)
    (angles : Fin dimension → ℝ) :
    HasSum (fun power =>
      oddWeylMomentSeriesTerm dimension parameter power angles)
      (Real.exp (parameter * oddCosineCubeScale angles) *
        oddWeylAngleWeight dimension angles) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp
    (parameter * oddCosineCubeScale angles)).mul_right
      (oddWeylAngleWeight dimension angles)
  rw [show (fun power =>
      oddWeylMomentSeriesTerm dimension parameter power angles) =
      fun power =>
        (parameter * oddCosineCubeScale angles) ^ power /
          (power.factorial : ℝ) *
            oddWeylAngleWeight dimension angles by
    funext power
    unfold oddWeylMomentSeriesTerm
    rw [mul_pow]
    ring]
  simpa only [Real.exp_eq_exp_ℝ, mul_comm] using h

theorem integral_oddWeylMomentSeriesTerm
    (dimension : ℕ) (parameter : ℝ) (power : ℕ) :
    (∫ angles : Fin dimension → ℝ,
      oddWeylMomentSeriesTerm dimension parameter power angles
      ∂cosineCubeProductMeasure dimension) =
      oddWeylGeometricMoment dimension power /
          (power.factorial : ℝ) * parameter ^ power := by
  unfold oddWeylMomentSeriesTerm oddWeylGeometricMoment
    weightedCosineCubeMoment weightedCosineCubePowerIntegrand
  rw [show (fun angles : Fin dimension → ℝ =>
      oddWeylAngleWeight dimension angles *
          oddCosineCubeScale angles ^ power /
        (power.factorial : ℝ) * parameter ^ power) =
      fun angles =>
        (parameter ^ power / (power.factorial : ℝ)) *
          (oddCosineCubeScale angles ^ power *
            oddWeylAngleWeight dimension angles) by
    funext angles
    ring]
  rw [integral_const_mul]
  ring

theorem oddWeylGeometricMoment_hasSum
    (dimension : ℕ) (parameter : ℝ) :
    HasSum (fun power =>
      oddWeylGeometricMoment dimension power /
        (power.factorial : ℝ) * parameter ^ power)
      (oddWeylExponentialIntegral dimension parameter) := by
  have hsum := hasSum_integral_of_dominated_convergence
    (fun power : ℕ => fun angles : Fin dimension → ℝ =>
      ‖oddWeylAngleWeight dimension angles‖ *
        ((2 * dimension + 1 : ℝ) * |parameter|) ^ power /
          (power.factorial : ℝ))
    (fun power =>
      (integrable_oddWeylMomentSeriesTerm dimension parameter power).aestronglyMeasurable)
    (fun power => Filter.Eventually.of_forall fun angles =>
      norm_oddWeylMomentSeriesTerm_le dimension parameter power angles)
    (Filter.Eventually.of_forall fun angles =>
      summable_oddWeylMomentBound dimension parameter angles)
    (by
      rw [show (fun angles : Fin dimension → ℝ =>
          ∑' power : ℕ,
            ‖oddWeylAngleWeight dimension angles‖ *
              ((2 * dimension + 1 : ℝ) * |parameter|) ^ power /
                (power.factorial : ℝ)) =
        fun angles =>
          ‖oddWeylAngleWeight dimension angles‖ *
            Real.exp ((2 * dimension + 1 : ℝ) * |parameter|) by
          funext angles
          exact tsum_oddWeylMomentBound dimension parameter angles]
      exact (integrable_norm_oddWeylAngleWeight dimension).mul_const _)
    (Filter.Eventually.of_forall fun angles =>
      hasSum_oddWeylMomentSeriesTerm_pointwise dimension parameter angles)
  unfold oddWeylExponentialIntegral
  rw [show (fun angles : Fin dimension → ℝ =>
      Real.exp (parameter * oddCosineCubeScale angles) *
        oddWeylAngleWeight dimension angles) =
      fun angles => Real.exp (parameter * oddCosineCubeScale angles) *
        oddWeylAngleWeight dimension angles by rfl] at hsum
  rw [show (fun power =>
      oddWeylGeometricMoment dimension power /
        (power.factorial : ℝ) * parameter ^ power) =
      fun power => ∫ angles : Fin dimension → ℝ,
        oddWeylMomentSeriesTerm dimension parameter power angles
        ∂cosineCubeProductMeasure dimension by
    funext power
    exact (integral_oddWeylMomentSeriesTerm dimension parameter power).symm]
  exact hsum

end FibonacciRibbonKernel
