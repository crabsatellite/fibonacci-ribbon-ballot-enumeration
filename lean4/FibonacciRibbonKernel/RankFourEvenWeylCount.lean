import FibonacciRibbonKernel.RankFourEvenWeylAndreief

namespace FibonacciRibbonKernel

open Filter MeasureTheory PowerSeries
open NormedSpace

noncomputable def rankFourEvenFormalGesselMatrixR :
    Matrix (Fin 2) (Fin 2) ℝ⟦X⟧ :=
  fun row column =>
    symmetricLiteralBesselJR ((row.val : ℤ) - column.val) +
      symmetricLiteralBesselJR
        ((row.val + column.val + 1 : ℕ) : ℤ)

theorem rankFourEvenFormalGesselDet_eq_mapped_heightFour :
    rankFourEvenFormalGesselMatrixR.det =
      PowerSeries.map (Rat.castHom ℝ) gesselHeightFourSeries := by
  rw [Matrix.det_fin_two]
  unfold rankFourEvenFormalGesselMatrixR
  simp only [Fin.val_zero, Fin.val_one]
  norm_num
  rw [symmetricLiteralBesselJR_neg 1]
  have hzero := symmetricLiteralBesselJR_intCast 0
  have hone := symmetricLiteralBesselJR_intCast 1
  have htwo := symmetricLiteralBesselJR_intCast 2
  have hthree := symmetricLiteralBesselJR_intCast 3
  norm_num at hzero hone htwo hthree
  rw [hzero, hone, htwo, hthree]
  have hq :
      (literalBesselJ 0 + literalBesselJ 1) *
          (literalBesselJ 0 + literalBesselJ 3) -
        (literalBesselJ 1 + literalBesselJ 2) *
          (literalBesselJ 1 + literalBesselJ 2) =
        gesselHeightFourSeries := by
    unfold gesselHeightFourSeries pairQ1 pairQ2 pairQ3
    ring
  rw [← hq]
  simp only [map_add, map_sub, map_mul]

theorem mapped_heightFour_factorialSeries_eq_rankFourEvenGessel :
    PowerSeries.map (Rat.castHom ℝ)
        (factorialSeries fun size => (heightFourTableauCount size : ℚ)) =
      rankFourEvenFormalGesselMatrixR.det := by
  rw [factorialSeries_heightFourTableauCount_eq_gessel,
    rankFourEvenFormalGesselDet_eq_mapped_heightFour]

theorem rankFourEvenFormalGessel_entry_hasSum
    (parameter : ℝ) (row column : Fin 2) :
    RealPowerSeriesHasSum
      (rankFourEvenFormalGesselMatrixR row column) parameter
      ((rankFourEvenRealGesselMatrix parameter row column) / Real.pi) := by
  unfold rankFourEvenFormalGesselMatrixR rankFourEvenRealGesselMatrix
  have hleft := symmetricLiteralBesselJR_hasSum
    ((row.val : ℤ) - column.val) parameter
  have hright := symmetricLiteralBesselJR_hasSum
    ((row.val + column.val + 1 : ℕ) : ℤ) parameter
  convert hleft.add hright using 1
  ring

theorem rankFourEvenFormalGesselDet_hasSum (parameter : ℝ) :
    RealPowerSeriesHasSum rankFourEvenFormalGesselMatrixR.det parameter
      ((1 / Real.pi) ^ 2 *
        (rankFourEvenRealGesselMatrix parameter).det) := by
  rw [Matrix.det_fin_two]
  have h00 := rankFourEvenFormalGessel_entry_hasSum parameter 0 0
  have h11 := rankFourEvenFormalGessel_entry_hasSum parameter 1 1
  have h01 := rankFourEvenFormalGessel_entry_hasSum parameter 0 1
  have h10 := rankFourEvenFormalGessel_entry_hasSum parameter 1 0
  have hdet := (h00.mul h11).sub (h01.mul h10)
  convert hdet using 1
  rw [Matrix.det_fin_two]
  ring

noncomputable def rankFourEvenMomentSeriesTerm
    (parameter : ℝ) (power : ℕ) (angles : Fin 2 → ℝ) : ℝ :=
  evenWeylAngleWeight 2 angles *
    cosineCubeScale angles ^ power / (power.factorial : ℝ) *
      parameter ^ power

theorem abs_cosineCubeScale_two_le (angles : Fin 2 → ℝ) :
    |cosineCubeScale angles| ≤ 4 := by
  unfold cosineCubeScale
  rw [show (∑ coordinate : Fin 2, Real.cos (angles coordinate)) =
      Real.cos (angles 0) + Real.cos (angles 1) by
    rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
    simp]
  calc
    |2 * (Real.cos (angles 0) + Real.cos (angles 1))| =
        2 * |Real.cos (angles 0) + Real.cos (angles 1)| := by
      rw [abs_mul]
      norm_num
    _ ≤ 2 * (|Real.cos (angles 0)| + |Real.cos (angles 1)|) := by
      gcongr
      exact abs_add_le _ _
    _ ≤ 4 := by
      have hzero := Real.abs_cos_le_one (angles 0)
      have hone := Real.abs_cos_le_one (angles 1)
      linarith

theorem integrable_norm_evenWeylAngleWeight_two :
    Integrable (fun angles : Fin 2 → ℝ =>
      ‖evenWeylAngleWeight 2 angles‖)
      (cosineCubeProductMeasure 2) :=
  (integrable_continuous_cosineCube
    (continuous_evenWeylAngleWeight 2)).norm

theorem integrable_rankFourEvenMomentSeriesTerm
    (parameter : ℝ) (power : ℕ) :
    Integrable (rankFourEvenMomentSeriesTerm parameter power)
      (cosineCubeProductMeasure 2) := by
  apply integrable_continuous_cosineCube
  have hpower : Continuous (fun angles : Fin 2 → ℝ =>
      cosineCubeScale angles ^ power) :=
    (continuous_cosineCubeScale 2).pow power
  unfold rankFourEvenMomentSeriesTerm
  exact (((continuous_evenWeylAngleWeight 2).mul
    hpower).div_const _).mul continuous_const

theorem norm_rankFourEvenMomentSeriesTerm_le
    (parameter : ℝ) (power : ℕ) (angles : Fin 2 → ℝ) :
    ‖rankFourEvenMomentSeriesTerm parameter power angles‖ ≤
      ‖evenWeylAngleWeight 2 angles‖ *
        (4 * |parameter|) ^ power / (power.factorial : ℝ) := by
  unfold rankFourEvenMomentSeriesTerm
  simp only [norm_mul, norm_div, Real.norm_eq_abs, norm_pow]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ power.factorial)]
  have hscale := abs_cosineCubeScale_two_le angles
  calc
    ‖evenWeylAngleWeight 2 angles‖ * |cosineCubeScale angles| ^ power /
          (power.factorial : ℝ) * |parameter| ^ power ≤
      ‖evenWeylAngleWeight 2 angles‖ * 4 ^ power /
          (power.factorial : ℝ) * |parameter| ^ power := by gcongr
    _ = _ := by
      rw [mul_pow, Real.norm_eq_abs]
      ring

theorem summable_rankFourEvenMomentBound
    (parameter : ℝ) (angles : Fin 2 → ℝ) :
    Summable (fun power : ℕ =>
      ‖evenWeylAngleWeight 2 angles‖ *
        (4 * |parameter|) ^ power / (power.factorial : ℝ)) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp
    (4 * |parameter|)).mul_left ‖evenWeylAngleWeight 2 angles‖
  rw [show (fun power : ℕ =>
      ‖evenWeylAngleWeight 2 angles‖ *
        (4 * |parameter|) ^ power / (power.factorial : ℝ)) =
      fun power => ‖evenWeylAngleWeight 2 angles‖ *
        ((4 * |parameter|) ^ power / (power.factorial : ℝ)) by
    funext power
    ring]
  exact h.summable

theorem tsum_rankFourEvenMomentBound
    (parameter : ℝ) (angles : Fin 2 → ℝ) :
    (∑' power : ℕ,
      ‖evenWeylAngleWeight 2 angles‖ *
        (4 * |parameter|) ^ power / (power.factorial : ℝ)) =
      ‖evenWeylAngleWeight 2 angles‖ * Real.exp (4 * |parameter|) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp
    (4 * |parameter|)).mul_left ‖evenWeylAngleWeight 2 angles‖
  rw [show (fun power : ℕ =>
      ‖evenWeylAngleWeight 2 angles‖ *
        (4 * |parameter|) ^ power / (power.factorial : ℝ)) =
      fun power => ‖evenWeylAngleWeight 2 angles‖ *
        ((4 * |parameter|) ^ power / (power.factorial : ℝ)) by
    funext power
    ring]
  simpa only [Real.exp_eq_exp_ℝ] using h.tsum_eq

theorem hasSum_rankFourEvenMomentSeriesTerm_pointwise
    (parameter : ℝ) (angles : Fin 2 → ℝ) :
    HasSum (fun power =>
      rankFourEvenMomentSeriesTerm parameter power angles)
      (Real.exp (parameter * cosineCubeScale angles) *
        evenWeylAngleWeight 2 angles) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp
    (parameter * cosineCubeScale angles)).mul_right
      (evenWeylAngleWeight 2 angles)
  rw [show (fun power =>
      rankFourEvenMomentSeriesTerm parameter power angles) =
      fun power =>
        (parameter * cosineCubeScale angles) ^ power /
          (power.factorial : ℝ) * evenWeylAngleWeight 2 angles by
    funext power
    unfold rankFourEvenMomentSeriesTerm
    rw [mul_pow]
    ring]
  simpa only [Real.exp_eq_exp_ℝ, mul_comm] using h

theorem integral_rankFourEvenMomentSeriesTerm
    (parameter : ℝ) (power : ℕ) :
    (∫ angles : Fin 2 → ℝ,
      rankFourEvenMomentSeriesTerm parameter power angles
      ∂cosineCubeProductMeasure 2) =
      evenWeylGeometricMoment 2 power / (power.factorial : ℝ) *
        parameter ^ power := by
  unfold rankFourEvenMomentSeriesTerm evenWeylGeometricMoment
    weightedCosineCubeMoment weightedCosineCubePowerIntegrand
  rw [show (fun angles : Fin 2 → ℝ =>
      evenWeylAngleWeight 2 angles * cosineCubeScale angles ^ power /
          (power.factorial : ℝ) * parameter ^ power) =
      fun angles => (parameter ^ power / (power.factorial : ℝ)) *
        (cosineCubeScale angles ^ power * evenWeylAngleWeight 2 angles) by
    funext angles
    ring]
  rw [integral_const_mul]
  ring

theorem rankFourEvenWeylGeometricMoment_hasSum (parameter : ℝ) :
    HasSum (fun power =>
      evenWeylGeometricMoment 2 power / (power.factorial : ℝ) *
        parameter ^ power)
      (rankFourEvenWeylExponentialIntegral parameter) := by
  have hsum := hasSum_integral_of_dominated_convergence
    (fun power : ℕ => fun angles : Fin 2 → ℝ =>
      ‖evenWeylAngleWeight 2 angles‖ *
        (4 * |parameter|) ^ power / (power.factorial : ℝ))
    (fun power =>
      (integrable_rankFourEvenMomentSeriesTerm parameter power).aestronglyMeasurable)
    (fun power => Filter.Eventually.of_forall fun angles =>
      norm_rankFourEvenMomentSeriesTerm_le parameter power angles)
    (Filter.Eventually.of_forall fun angles =>
      summable_rankFourEvenMomentBound parameter angles)
    (by
      rw [show (fun angles : Fin 2 → ℝ =>
          ∑' power : ℕ,
            ‖evenWeylAngleWeight 2 angles‖ *
              (4 * |parameter|) ^ power / (power.factorial : ℝ)) =
        fun angles => ‖evenWeylAngleWeight 2 angles‖ *
          Real.exp (4 * |parameter|) by
        funext angles
        exact tsum_rankFourEvenMomentBound parameter angles]
      exact integrable_norm_evenWeylAngleWeight_two.mul_const _)
    (Filter.Eventually.of_forall fun angles =>
      hasSum_rankFourEvenMomentSeriesTerm_pointwise parameter angles)
  unfold rankFourEvenWeylExponentialIntegral
  rw [show (fun power =>
      evenWeylGeometricMoment 2 power / (power.factorial : ℝ) *
        parameter ^ power) =
      fun power => ∫ angles : Fin 2 → ℝ,
        rankFourEvenMomentSeriesTerm parameter power angles
        ∂cosineCubeProductMeasure 2 by
    funext power
    exact (integral_rankFourEvenMomentSeriesTerm parameter power).symm]
  exact hsum

noncomputable def rankFourEvenWeylMomentSeriesR : ℝ⟦X⟧ :=
  PowerSeries.mk fun power =>
    evenWeylGeometricMoment 2 power / (power.factorial : ℝ)

noncomputable def rankFourEvenWeylSeriesR : ℝ⟦X⟧ :=
  PowerSeries.C (2 / Real.pi ^ 2) * rankFourEvenWeylMomentSeriesR

theorem rankFourEvenWeylSeriesR_hasSum (parameter : ℝ) :
    RealPowerSeriesHasSum rankFourEvenWeylSeriesR parameter
      ((2 / Real.pi ^ 2) *
        rankFourEvenWeylExponentialIntegral parameter) := by
  unfold rankFourEvenWeylSeriesR
  have hmoment : RealPowerSeriesHasSum rankFourEvenWeylMomentSeriesR
      parameter (rankFourEvenWeylExponentialIntegral parameter) := by
    unfold RealPowerSeriesHasSum realPowerSeriesTerm
      rankFourEvenWeylMomentSeriesR
    simpa using rankFourEvenWeylGeometricMoment_hasSum parameter
  exact (realPowerSeries_C_hasSum (2 / Real.pi ^ 2) parameter).mul hmoment

theorem rankFourEvenGessel_value_eq_weyl (parameter : ℝ) :
    (1 / Real.pi) ^ 2 *
        (rankFourEvenRealGesselMatrix parameter).det =
      (2 / Real.pi ^ 2) *
        rankFourEvenWeylExponentialIntegral parameter := by
  rw [← rankFourEvenWeylExponential_eq_realGessel]
  ring

theorem rankFourEvenFormalGesselDet_eq_weylSeries :
    rankFourEvenFormalGesselMatrixR.det = rankFourEvenWeylSeriesR := by
  have hgesselAt := realPowerSeriesFML_hasFPowerSeriesAt
    rankFourEvenFormalGesselMatrixR.det
    (rankFourEvenFormalGesselDet_hasSum 1)
  have hweylAt := realPowerSeriesFML_hasFPowerSeriesAt
    rankFourEvenWeylSeriesR (rankFourEvenWeylSeriesR_hasSum 1)
  have hfunctions :
      (realPowerSeriesFML rankFourEvenFormalGesselMatrixR.det).sum =
        (realPowerSeriesFML rankFourEvenWeylSeriesR).sum := by
    funext parameter
    rw [realPowerSeriesFML_sum_eq, realPowerSeriesFML_sum_eq]
    have hg := rankFourEvenFormalGesselDet_hasSum parameter
    have hw := rankFourEvenWeylSeriesR_hasSum parameter
    change (∑' power : ℕ,
        realPowerSeriesTerm rankFourEvenFormalGesselMatrixR.det
          parameter power) =
      ∑' power : ℕ,
        realPowerSeriesTerm rankFourEvenWeylSeriesR parameter power
    rw [hg.tsum_eq, hw.tsum_eq,
      rankFourEvenGessel_value_eq_weyl]
  rw [hfunctions] at hgesselAt
  have hfml := hgesselAt.eq_formalMultilinearSeries hweylAt
  ext power
  have hcoefficient := congrArg
    (fun series : FormalMultilinearSeries ℝ ℝ ℝ =>
      series power (fun _ : Fin power => (1 : ℝ))) hfml
  simpa [realPowerSeriesFML] using hcoefficient

theorem heightFourTableauCount_eq_normalized_evenWeylMoment
    (power : ℕ) :
    (heightFourTableauCount power : ℝ) =
      (2 / Real.pi ^ 2) * evenWeylGeometricMoment 2 power := by
  have hseries := mapped_heightFour_factorialSeries_eq_rankFourEvenGessel
  rw [rankFourEvenFormalGesselDet_eq_weylSeries] at hseries
  have hcoeff := congrArg (PowerSeries.coeff power) hseries
  unfold rankFourEvenWeylSeriesR rankFourEvenWeylMomentSeriesR at hcoeff
  rw [PowerSeries.coeff_map, factorialSeries_coeff,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_mk] at hcoeff
  have hcast :
      (Rat.castHom ℝ)
          ((heightFourTableauCount power : ℚ) /
            (power.factorial : ℚ)) =
        (heightFourTableauCount power : ℝ) /
          (power.factorial : ℝ) := by
    rw [map_div₀]
    norm_num
  rw [hcast] at hcoeff
  have hfactorial : (power.factorial : ℝ) ≠ 0 := by positivity
  field_simp at hcoeff ⊢
  nlinarith

theorem heightFourRibbonCount_eq_normalized_evenWeylFibonacciMoment
    (power : ℕ) :
    (ribbonCount 3 power : ℝ) =
      (2 / Real.pi ^ 2) * evenWeylFibonacciMoment 2 power := by
  symm
  apply evenWeylMoment_count_transfer 2 (by omega) (2 / Real.pi ^ 2)
  intro degree
  exact (heightFourTableauCount_eq_normalized_evenWeylMoment degree).symm

end FibonacciRibbonKernel
