import FibonacciRibbonKernel.RankSixEvenWeylAndreief
import FibonacciRibbonKernel.SixPfaffianBessel

namespace FibonacciRibbonKernel

open Filter MeasureTheory PowerSeries NormedSpace

noncomputable def rankSixEvenFormalGesselMatrixR :
    Matrix (Fin 3) (Fin 3) ℝ⟦X⟧ :=
  fun row column =>
    symmetricLiteralBesselJR ((row.val : ℤ) - column.val) +
      symmetricLiteralBesselJR
        ((row.val + column.val + 1 : ℕ) : ℤ)

theorem rankSixEvenFormalGessel_entry_eq_mapped
    (row column : Fin 3) :
    rankSixEvenFormalGesselMatrixR row column =
      PowerSeries.map (Rat.castHom ℝ) (gesselHeightSixMatrix row column) := by
  fin_cases row <;> fin_cases column <;>
    norm_num [rankSixEvenFormalGesselMatrixR, gesselHeightSixMatrix,
      symmetricLiteralBesselJR, symmetricLiteralBesselJ]

theorem rankSixEvenFormalGesselDet_eq_mapped_heightSix :
    rankSixEvenFormalGesselMatrixR.det =
      PowerSeries.map (Rat.castHom ℝ) gesselHeightSixSeries := by
  rw [gesselHeightSixSeries_eq_det, Matrix.det_fin_three,
    Matrix.det_fin_three]
  simp_rw [rankSixEvenFormalGessel_entry_eq_mapped]
  simp only [map_add, map_sub, map_mul]

theorem mapped_heightSix_factorialSeries_eq_rankSixEvenGessel :
    PowerSeries.map (Rat.castHom ℝ)
        (factorialSeries fun size => (heightSixTableauCount size : ℚ)) =
      rankSixEvenFormalGesselMatrixR.det := by
  rw [factorialSeries_heightSixTableauCount_eq_gessel,
    rankSixEvenFormalGesselDet_eq_mapped_heightSix]

theorem rankSixEvenFormalGessel_entry_hasSum
    (parameter : ℝ) (row column : Fin 3) :
    RealPowerSeriesHasSum
      (rankSixEvenFormalGesselMatrixR row column) parameter
      (rankSixEvenRealGesselMatrix parameter row column / Real.pi) := by
  unfold rankSixEvenFormalGesselMatrixR rankSixEvenRealGesselMatrix
  have hl := symmetricLiteralBesselJR_hasSum
    ((row.val : ℤ) - column.val) parameter
  have hr := symmetricLiteralBesselJR_hasSum
    ((row.val + column.val + 1 : ℕ) : ℤ) parameter
  convert hl.add hr using 1
  ring

theorem rankSixEvenFormalGesselDet_hasSum (parameter : ℝ) :
    RealPowerSeriesHasSum rankSixEvenFormalGesselMatrixR.det parameter
      ((1 / Real.pi) ^ 3 * (rankSixEvenRealGesselMatrix parameter).det) := by
  rw [Matrix.det_fin_three]
  have h00 := rankSixEvenFormalGessel_entry_hasSum parameter 0 0
  have h11 := rankSixEvenFormalGessel_entry_hasSum parameter 1 1
  have h22 := rankSixEvenFormalGessel_entry_hasSum parameter 2 2
  have h01 := rankSixEvenFormalGessel_entry_hasSum parameter 0 1
  have h12 := rankSixEvenFormalGessel_entry_hasSum parameter 1 2
  have h20 := rankSixEvenFormalGessel_entry_hasSum parameter 2 0
  have h02 := rankSixEvenFormalGessel_entry_hasSum parameter 0 2
  have h10 := rankSixEvenFormalGessel_entry_hasSum parameter 1 0
  have h21 := rankSixEvenFormalGessel_entry_hasSum parameter 2 1
  have hdet := (((h00.mul h11).mul h22).sub ((h00.mul h12).mul h21)).sub
    ((h01.mul h10).mul h22) |>.add ((h01.mul h12).mul h20) |>.add
    ((h02.mul h10).mul h21) |>.sub ((h02.mul h11).mul h20)
  convert hdet using 1
  rw [Matrix.det_fin_three]
  ring

noncomputable def rankSixEvenMomentSeriesTerm
    (parameter : ℝ) (power : ℕ) (angles : Fin 3 → ℝ) : ℝ :=
  evenWeylAngleWeight 3 angles * cosineCubeScale angles ^ power /
    (power.factorial : ℝ) * parameter ^ power

theorem abs_cosineCubeScale_three_le (angles : Fin 3 → ℝ) :
    |cosineCubeScale angles| ≤ 6 := by
  unfold cosineCubeScale
  calc
    |2 * ∑ coordinate, Real.cos (angles coordinate)| =
        2 * |∑ coordinate, Real.cos (angles coordinate)| := by
      rw [abs_mul]
      norm_num
    _ ≤ 2 * ∑ _coordinate : Fin 3, (1 : ℝ) := by
      gcongr
      exact (Finset.abs_sum_le_sum_abs _ _).trans (by
        gcongr with coordinate
        exact Real.abs_cos_le_one _)
    _ = 6 := by norm_num

theorem integrable_norm_evenWeylAngleWeight_three :
    Integrable (fun angles : Fin 3 → ℝ => ‖evenWeylAngleWeight 3 angles‖)
      (cosineCubeProductMeasure 3) :=
  (integrable_continuous_cosineCube
    (continuous_evenWeylAngleWeight 3)).norm

theorem integrable_rankSixEvenMomentSeriesTerm
    (parameter : ℝ) (power : ℕ) :
    Integrable (rankSixEvenMomentSeriesTerm parameter power)
      (cosineCubeProductMeasure 3) := by
  apply integrable_continuous_cosineCube
  have hp : Continuous (fun angles : Fin 3 → ℝ =>
      cosineCubeScale angles ^ power) := (continuous_cosineCubeScale 3).pow power
  unfold rankSixEvenMomentSeriesTerm
  exact (((continuous_evenWeylAngleWeight 3).mul hp).div_const _).mul
    continuous_const

theorem norm_rankSixEvenMomentSeriesTerm_le
    (parameter : ℝ) (power : ℕ) (angles : Fin 3 → ℝ) :
    ‖rankSixEvenMomentSeriesTerm parameter power angles‖ ≤
      ‖evenWeylAngleWeight 3 angles‖ *
        (6 * |parameter|) ^ power / (power.factorial : ℝ) := by
  unfold rankSixEvenMomentSeriesTerm
  simp only [norm_mul, norm_div, Real.norm_eq_abs, norm_pow]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ power.factorial)]
  have hs := abs_cosineCubeScale_three_le angles
  calc
    _ ≤ |evenWeylAngleWeight 3 angles| * 6 ^ power /
          (power.factorial : ℝ) * |parameter| ^ power := by gcongr
    _ = _ := by rw [mul_pow]; ring

theorem summable_rankSixEvenMomentBound
    (parameter : ℝ) (angles : Fin 3 → ℝ) :
    Summable (fun power : ℕ => ‖evenWeylAngleWeight 3 angles‖ *
      (6 * |parameter|) ^ power / (power.factorial : ℝ)) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp
    (6 * |parameter|)).mul_left ‖evenWeylAngleWeight 3 angles‖
  rw [show (fun power : ℕ => ‖evenWeylAngleWeight 3 angles‖ *
      (6 * |parameter|) ^ power / (power.factorial : ℝ)) =
      fun power => ‖evenWeylAngleWeight 3 angles‖ *
        ((6 * |parameter|) ^ power / (power.factorial : ℝ)) by
    funext power
    ring]
  exact h.summable

theorem tsum_rankSixEvenMomentBound
    (parameter : ℝ) (angles : Fin 3 → ℝ) :
    (∑' power : ℕ, ‖evenWeylAngleWeight 3 angles‖ *
      (6 * |parameter|) ^ power / (power.factorial : ℝ)) =
      ‖evenWeylAngleWeight 3 angles‖ * Real.exp (6 * |parameter|) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp
    (6 * |parameter|)).mul_left ‖evenWeylAngleWeight 3 angles‖
  rw [show (fun power : ℕ => ‖evenWeylAngleWeight 3 angles‖ *
      (6 * |parameter|) ^ power / (power.factorial : ℝ)) =
      fun power => ‖evenWeylAngleWeight 3 angles‖ *
        ((6 * |parameter|) ^ power / (power.factorial : ℝ)) by
    funext power
    ring]
  simpa only [Real.exp_eq_exp_ℝ] using h.tsum_eq

theorem hasSum_rankSixEvenMomentSeriesTerm_pointwise
    (parameter : ℝ) (angles : Fin 3 → ℝ) :
    HasSum (fun power => rankSixEvenMomentSeriesTerm parameter power angles)
      (Real.exp (parameter * cosineCubeScale angles) *
        evenWeylAngleWeight 3 angles) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp
    (parameter * cosineCubeScale angles)).mul_right
      (evenWeylAngleWeight 3 angles)
  rw [show (fun power => rankSixEvenMomentSeriesTerm parameter power angles) =
      fun power => (parameter * cosineCubeScale angles) ^ power /
        (power.factorial : ℝ) * evenWeylAngleWeight 3 angles by
    funext power
    unfold rankSixEvenMomentSeriesTerm
    rw [mul_pow]
    ring]
  simpa only [Real.exp_eq_exp_ℝ, mul_comm] using h

theorem integral_rankSixEvenMomentSeriesTerm
    (parameter : ℝ) (power : ℕ) :
    (∫ angles : Fin 3 → ℝ,
      rankSixEvenMomentSeriesTerm parameter power angles
      ∂cosineCubeProductMeasure 3) =
      evenWeylGeometricMoment 3 power / (power.factorial : ℝ) *
        parameter ^ power := by
  unfold rankSixEvenMomentSeriesTerm evenWeylGeometricMoment
    weightedCosineCubeMoment weightedCosineCubePowerIntegrand
  rw [show (fun angles : Fin 3 → ℝ =>
      evenWeylAngleWeight 3 angles * cosineCubeScale angles ^ power /
        (power.factorial : ℝ) * parameter ^ power) =
      fun angles => (parameter ^ power / (power.factorial : ℝ)) *
        (cosineCubeScale angles ^ power * evenWeylAngleWeight 3 angles) by
    funext angles
    ring]
  rw [integral_const_mul]
  ring

theorem rankSixEvenWeylGeometricMoment_hasSum (parameter : ℝ) :
    HasSum (fun power => evenWeylGeometricMoment 3 power /
      (power.factorial : ℝ) * parameter ^ power)
      (rankSixEvenWeylExponentialIntegral parameter) := by
  have hsum := hasSum_integral_of_dominated_convergence
    (fun power : ℕ => fun angles : Fin 3 → ℝ =>
      ‖evenWeylAngleWeight 3 angles‖ *
        (6 * |parameter|) ^ power / (power.factorial : ℝ))
    (fun power =>
      (integrable_rankSixEvenMomentSeriesTerm parameter power).aestronglyMeasurable)
    (fun power => Filter.Eventually.of_forall fun angles =>
      norm_rankSixEvenMomentSeriesTerm_le parameter power angles)
    (Filter.Eventually.of_forall fun angles =>
      summable_rankSixEvenMomentBound parameter angles)
    (by
      rw [show (fun angles : Fin 3 → ℝ => ∑' power : ℕ,
          ‖evenWeylAngleWeight 3 angles‖ * (6 * |parameter|) ^ power /
            (power.factorial : ℝ)) =
        fun angles => ‖evenWeylAngleWeight 3 angles‖ *
          Real.exp (6 * |parameter|) by
        funext angles
        exact tsum_rankSixEvenMomentBound parameter angles]
      exact integrable_norm_evenWeylAngleWeight_three.mul_const _)
    (Filter.Eventually.of_forall fun angles =>
      hasSum_rankSixEvenMomentSeriesTerm_pointwise parameter angles)
  unfold rankSixEvenWeylExponentialIntegral
  rw [show (fun power => evenWeylGeometricMoment 3 power /
      (power.factorial : ℝ) * parameter ^ power) =
      fun power => ∫ angles : Fin 3 → ℝ,
        rankSixEvenMomentSeriesTerm parameter power angles
        ∂cosineCubeProductMeasure 3 by
    funext power
    exact (integral_rankSixEvenMomentSeriesTerm parameter power).symm]
  exact hsum

noncomputable def rankSixEvenWeylMomentSeriesR : ℝ⟦X⟧ :=
  PowerSeries.mk fun power =>
    evenWeylGeometricMoment 3 power / (power.factorial : ℝ)

noncomputable def rankSixEvenWeylSeriesR : ℝ⟦X⟧ :=
  PowerSeries.C (32 / (3 * Real.pi ^ 3)) * rankSixEvenWeylMomentSeriesR

theorem rankSixEvenWeylSeriesR_hasSum (parameter : ℝ) :
    RealPowerSeriesHasSum rankSixEvenWeylSeriesR parameter
      ((32 / (3 * Real.pi ^ 3)) *
        rankSixEvenWeylExponentialIntegral parameter) := by
  unfold rankSixEvenWeylSeriesR
  have hm : RealPowerSeriesHasSum rankSixEvenWeylMomentSeriesR parameter
      (rankSixEvenWeylExponentialIntegral parameter) := by
    unfold RealPowerSeriesHasSum realPowerSeriesTerm
      rankSixEvenWeylMomentSeriesR
    simpa using rankSixEvenWeylGeometricMoment_hasSum parameter
  exact (realPowerSeries_C_hasSum (32 / (3 * Real.pi ^ 3)) parameter).mul hm

theorem rankSixEvenGessel_value_eq_weyl (parameter : ℝ) :
    (1 / Real.pi) ^ 3 * (rankSixEvenRealGesselMatrix parameter).det =
      (32 / (3 * Real.pi ^ 3)) *
        rankSixEvenWeylExponentialIntegral parameter := by
  rw [rankSixEvenWeylExponential_eq_realGessel]
  field_simp [Real.pi_ne_zero]

theorem rankSixEvenFormalGesselDet_eq_weylSeries :
    rankSixEvenFormalGesselMatrixR.det = rankSixEvenWeylSeriesR := by
  have hgAt := realPowerSeriesFML_hasFPowerSeriesAt
    rankSixEvenFormalGesselMatrixR.det (rankSixEvenFormalGesselDet_hasSum 1)
  have hwAt := realPowerSeriesFML_hasFPowerSeriesAt rankSixEvenWeylSeriesR
    (rankSixEvenWeylSeriesR_hasSum 1)
  have hfunctions :
      (realPowerSeriesFML rankSixEvenFormalGesselMatrixR.det).sum =
        (realPowerSeriesFML rankSixEvenWeylSeriesR).sum := by
    funext parameter
    rw [realPowerSeriesFML_sum_eq, realPowerSeriesFML_sum_eq]
    have hg := rankSixEvenFormalGesselDet_hasSum parameter
    have hw := rankSixEvenWeylSeriesR_hasSum parameter
    change (∑' power : ℕ,
        realPowerSeriesTerm rankSixEvenFormalGesselMatrixR.det parameter power) =
      ∑' power : ℕ, realPowerSeriesTerm rankSixEvenWeylSeriesR parameter power
    rw [hg.tsum_eq, hw.tsum_eq, rankSixEvenGessel_value_eq_weyl]
  rw [hfunctions] at hgAt
  have hfml := hgAt.eq_formalMultilinearSeries hwAt
  ext power
  have hc := congrArg (fun series : FormalMultilinearSeries ℝ ℝ ℝ =>
    series power (fun _ : Fin power => (1 : ℝ))) hfml
  simpa [realPowerSeriesFML] using hc

theorem heightSixTableauCount_eq_normalized_evenWeylMoment (power : ℕ) :
    (heightSixTableauCount power : ℝ) =
      (32 / (3 * Real.pi ^ 3)) * evenWeylGeometricMoment 3 power := by
  have hseries := mapped_heightSix_factorialSeries_eq_rankSixEvenGessel
  rw [rankSixEvenFormalGesselDet_eq_weylSeries] at hseries
  have hc := congrArg (PowerSeries.coeff power) hseries
  unfold rankSixEvenWeylSeriesR rankSixEvenWeylMomentSeriesR at hc
  rw [PowerSeries.coeff_map, factorialSeries_coeff,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_mk] at hc
  have hcast : (Rat.castHom ℝ)
      ((heightSixTableauCount power : ℚ) / (power.factorial : ℚ)) =
      (heightSixTableauCount power : ℝ) / (power.factorial : ℝ) := by
    rw [map_div₀]
    norm_num
  rw [hcast] at hc
  have hf : (power.factorial : ℝ) ≠ 0 := by positivity
  field_simp at hc ⊢
  nlinarith

theorem heightSixRibbonCount_eq_normalized_evenWeylFibonacciMoment
    (power : ℕ) :
    (ribbonCount 5 power : ℝ) =
      (32 / (3 * Real.pi ^ 3)) * evenWeylFibonacciMoment 3 power := by
  symm
  apply evenWeylMoment_count_transfer 3 (by omega)
    (32 / (3 * Real.pi ^ 3))
  intro degree
  exact (heightSixTableauCount_eq_normalized_evenWeylMoment degree).symm

end FibonacciRibbonKernel
