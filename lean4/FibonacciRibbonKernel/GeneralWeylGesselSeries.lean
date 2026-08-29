import FibonacciRibbonKernel.EvenWeylGeneralAndreief

namespace FibonacciRibbonKernel

open Filter MeasureTheory PowerSeries
open scoped BigOperators

theorem RealPowerSeriesHasSum.finsetSum
    {ι : Type*} [DecidableEq ι] {indices : Finset ι}
    {series : ι → ℝ⟦X⟧} {parameter : ℝ} {values : ι → ℝ}
    (h : ∀ index ∈ indices,
      RealPowerSeriesHasSum (series index) parameter (values index)) :
    RealPowerSeriesHasSum (∑ index ∈ indices, series index) parameter
      (∑ index ∈ indices, values index) := by
  induction indices using Finset.induction_on with
  | empty =>
      simpa using (realPowerSeries_C_hasSum 0 parameter)
  | @insert index indices hindex ih =>
      rw [Finset.sum_insert hindex, Finset.sum_insert hindex]
      exact (h index (Finset.mem_insert_self index indices)).add
        (ih fun current hcurrent =>
          h current (Finset.mem_insert_of_mem hcurrent))

theorem RealPowerSeriesHasSum.finsetProd
    {ι : Type*} [DecidableEq ι] {indices : Finset ι}
    {series : ι → ℝ⟦X⟧} {parameter : ℝ} {values : ι → ℝ}
    (h : ∀ index ∈ indices,
      RealPowerSeriesHasSum (series index) parameter (values index)) :
    RealPowerSeriesHasSum (∏ index ∈ indices, series index) parameter
      (∏ index ∈ indices, values index) := by
  induction indices using Finset.induction_on with
  | empty =>
      simpa using (realPowerSeries_C_hasSum 1 parameter)
  | @insert index indices hindex ih =>
      rw [Finset.prod_insert hindex, Finset.prod_insert hindex]
      exact (h index (Finset.mem_insert_self index indices)).mul
        (ih fun current hcurrent =>
          h current (Finset.mem_insert_of_mem hcurrent))

theorem RealPowerSeriesHasSum.matrixDet
    {dimension : ℕ} {matrix : Matrix (Fin dimension) (Fin dimension) ℝ⟦X⟧}
    {parameter : ℝ} {values : Matrix (Fin dimension) (Fin dimension) ℝ}
    (h : ∀ row column,
      RealPowerSeriesHasSum (matrix row column) parameter (values row column)) :
    RealPowerSeriesHasSum matrix.det parameter values.det := by
  rw [Matrix.det_apply', Matrix.det_apply']
  apply RealPowerSeriesHasSum.finsetSum
  intro permutation _hpermutation
  have hp : RealPowerSeriesHasSum
      (∏ column, matrix (permutation column) column) parameter
      (∏ column, values (permutation column) column) := by
    exact RealPowerSeriesHasSum.finsetProd fun column _ =>
      h (permutation column) column
  have hs := realPowerSeries_C_hasSum
    ((Equiv.Perm.sign permutation : ℤ) : ℝ) parameter
  convert hs.mul hp using 1
  all_goals simp

noncomputable def evenFormalGesselMatrixR
    (dimension : ℕ) : Matrix (Fin dimension) (Fin dimension) ℝ⟦X⟧ :=
  fun row column =>
    symmetricLiteralBesselJR ((row.val : ℤ) - column.val) +
      symmetricLiteralBesselJR
        ((row.val + column.val + 1 : ℕ) : ℤ)

noncomputable def evenRealGesselMatrixDivPi
    (dimension : ℕ) (parameter : ℝ) :
    Matrix (Fin dimension) (Fin dimension) ℝ :=
  fun row column => evenRealGesselMatrix dimension parameter row column / Real.pi

noncomputable def oddRealGesselMatrixDivPi
    (dimension : ℕ) (parameter : ℝ) :
    Matrix (Fin dimension) (Fin dimension) ℝ :=
  fun row column => oddRealGesselMatrix dimension parameter row column / Real.pi

noncomputable def matrixDivPi
    {dimension : ℕ} (matrix : Matrix (Fin dimension) (Fin dimension) ℝ) :
    Matrix (Fin dimension) (Fin dimension) ℝ :=
  fun row column => matrix row column / Real.pi

theorem evenFormalGesselMatrixR_entry_hasSum
    (dimension : ℕ) (parameter : ℝ) (row column : Fin dimension) :
    RealPowerSeriesHasSum (evenFormalGesselMatrixR dimension row column)
      parameter (evenRealGesselMatrix dimension parameter row column / Real.pi) := by
  unfold evenFormalGesselMatrixR evenRealGesselMatrix
  have hl := symmetricLiteralBesselJR_hasSum
    ((row.val : ℤ) - column.val) parameter
  have hr := symmetricLiteralBesselJR_hasSum
    ((row.val + column.val + 1 : ℕ) : ℤ) parameter
  convert hl.add hr using 1
  ring

theorem evenFormalGesselDet_hasSum (dimension : ℕ) (parameter : ℝ) :
    RealPowerSeriesHasSum (evenFormalGesselMatrixR dimension).det parameter
      (evenRealGesselMatrixDivPi dimension parameter).det :=
  RealPowerSeriesHasSum.matrixDet fun row column =>
    evenFormalGesselMatrixR_entry_hasSum dimension parameter row column

theorem oddFormalGesselDet_hasSum
    (dimension : ℕ) (parameter : ℝ) :
    RealPowerSeriesHasSum (oddFormalGesselMatrixR dimension).det parameter
      (oddRealGesselMatrixDivPi dimension parameter).det :=
  RealPowerSeriesHasSum.matrixDet fun row column =>
    oddFormalGesselMatrixR_entry_hasSum dimension parameter row column

theorem matrixDivPi_det
    {dimension : ℕ} (matrix : Matrix (Fin dimension) (Fin dimension) ℝ) :
    (matrixDivPi matrix).det =
      (1 / Real.pi) ^ dimension * matrix.det := by
  have hm : matrixDivPi matrix =
      (1 / Real.pi : ℝ) • matrix := by
    ext row column
    simp [matrixDivPi, div_eq_mul_inv, mul_comm]
  rw [hm, Matrix.det_smul, Fintype.card_fin]

theorem evenRealGesselMatrixDivPi_det
    (dimension : ℕ) (parameter : ℝ) :
    (evenRealGesselMatrixDivPi dimension parameter).det =
      (1 / Real.pi) ^ dimension *
        (evenRealGesselMatrix dimension parameter).det := by
  change (matrixDivPi (evenRealGesselMatrix dimension parameter)).det = _
  exact matrixDivPi_det (evenRealGesselMatrix dimension parameter)

theorem oddRealGesselMatrixDivPi_det
    (dimension : ℕ) (parameter : ℝ) :
    (oddRealGesselMatrixDivPi dimension parameter).det =
      (1 / Real.pi) ^ dimension *
        (oddRealGesselMatrix dimension parameter).det := by
  change (matrixDivPi (oddRealGesselMatrix dimension parameter)).det = _
  exact matrixDivPi_det (oddRealGesselMatrix dimension parameter)

noncomputable def evenWeylMomentSeriesGeneralR (dimension : ℕ) : ℝ⟦X⟧ :=
  PowerSeries.mk fun power =>
    evenWeylGeometricMoment dimension power / (power.factorial : ℝ)

noncomputable def evenWeylNormalization (dimension : ℕ) : ℝ :=
  (2 : ℝ) ^ (dimension ^ 2 - dimension) /
    ((dimension.factorial : ℝ) * Real.pi ^ dimension)

noncomputable def evenWeylSeriesGeneralR (dimension : ℕ) : ℝ⟦X⟧ :=
  PowerSeries.C (evenWeylNormalization dimension) *
    evenWeylMomentSeriesGeneralR dimension

noncomputable def oddWeylNormalization (dimension : ℕ) : ℝ :=
  (2 : ℝ) ^ (dimension ^ 2) /
    ((dimension.factorial : ℝ) * Real.pi ^ dimension)

noncomputable def oddWeylSeriesGeneralR (dimension : ℕ) : ℝ⟦X⟧ :=
  PowerSeries.C (oddWeylNormalization dimension) * oddWeylMomentSeriesR dimension

theorem abs_cosineCubeScale_le (dimension : ℕ)
    (angles : Fin dimension → ℝ) :
    |cosineCubeScale angles| ≤ 2 * dimension := by
  unfold cosineCubeScale
  calc
    |2 * ∑ coordinate, Real.cos (angles coordinate)| =
        2 * |∑ coordinate, Real.cos (angles coordinate)| := by
      rw [abs_mul]
      norm_num
    _ ≤ 2 * ∑ _coordinate : Fin dimension, (1 : ℝ) := by
      gcongr
      exact (Finset.abs_sum_le_sum_abs _ _).trans (by
        gcongr with coordinate
        exact Real.abs_cos_le_one _)
    _ = 2 * dimension := by simp

noncomputable def evenWeylMomentSeriesTerm
    (dimension : ℕ) (parameter : ℝ) (power : ℕ)
    (angles : Fin dimension → ℝ) : ℝ :=
  evenWeylAngleWeight dimension angles * cosineCubeScale angles ^ power /
    (power.factorial : ℝ) * parameter ^ power

theorem evenWeylGeometricMoment_hasSum
    (dimension : ℕ) (parameter : ℝ) :
    HasSum (fun power => evenWeylGeometricMoment dimension power /
      (power.factorial : ℝ) * parameter ^ power)
      (evenWeylExponentialIntegral dimension parameter) := by
  have hterm : ∀ power,
      Integrable (evenWeylMomentSeriesTerm dimension parameter power)
        (cosineCubeProductMeasure dimension) := by
    intro power
    apply integrable_continuous_cosineCube
    have hp : Continuous (fun angles : Fin dimension → ℝ =>
        cosineCubeScale angles ^ power) :=
      (continuous_cosineCubeScale dimension).pow power
    unfold evenWeylMomentSeriesTerm
    exact (((continuous_evenWeylAngleWeight dimension).mul
      hp).div_const _).mul
        continuous_const
  have hbound : ∀ power (angles : Fin dimension → ℝ),
      ‖evenWeylMomentSeriesTerm dimension parameter power angles‖ ≤
        ‖evenWeylAngleWeight dimension angles‖ *
          ((2 * dimension : ℝ) * |parameter|) ^ power /
            (power.factorial : ℝ) := by
    intro power angles
    unfold evenWeylMomentSeriesTerm
    simp only [norm_mul, norm_div, Real.norm_eq_abs, norm_pow]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ power.factorial)]
    have hs := abs_cosineCubeScale_le dimension angles
    calc
      _ ≤ |evenWeylAngleWeight dimension angles| *
          (2 * dimension : ℝ) ^ power /
          (power.factorial : ℝ) * |parameter| ^ power := by gcongr
      _ = _ := by simp only [mul_pow]; ring
  have hsummable : ∀ angles : Fin dimension → ℝ,
      Summable (fun power : ℕ => ‖evenWeylAngleWeight dimension angles‖ *
        ((2 * dimension : ℝ) * |parameter|) ^ power /
          (power.factorial : ℝ)) := by
    intro angles
    have h := (NormedSpace.expSeries_div_hasSum_exp
      ((2 * dimension : ℝ) * |parameter|)).mul_left
        ‖evenWeylAngleWeight dimension angles‖
    rw [show (fun power : ℕ => ‖evenWeylAngleWeight dimension angles‖ *
        ((2 * dimension : ℝ) * |parameter|) ^ power /
          (power.factorial : ℝ)) =
        fun power => ‖evenWeylAngleWeight dimension angles‖ *
          (((2 * dimension : ℝ) * |parameter|) ^ power /
            (power.factorial : ℝ)) by
      funext power
      ring]
    exact h.summable
  have htsum : ∀ angles : Fin dimension → ℝ,
      (∑' power : ℕ, ‖evenWeylAngleWeight dimension angles‖ *
        ((2 * dimension : ℝ) * |parameter|) ^ power /
          (power.factorial : ℝ)) =
        ‖evenWeylAngleWeight dimension angles‖ *
          Real.exp ((2 * dimension : ℝ) * |parameter|) := by
    intro angles
    have h := (NormedSpace.expSeries_div_hasSum_exp
      ((2 * dimension : ℝ) * |parameter|)).mul_left
        ‖evenWeylAngleWeight dimension angles‖
    rw [show (fun power : ℕ => ‖evenWeylAngleWeight dimension angles‖ *
        ((2 * dimension : ℝ) * |parameter|) ^ power /
          (power.factorial : ℝ)) =
        fun power => ‖evenWeylAngleWeight dimension angles‖ *
          (((2 * dimension : ℝ) * |parameter|) ^ power /
            (power.factorial : ℝ)) by
      funext power
      ring]
    simpa only [Real.exp_eq_exp_ℝ] using h.tsum_eq
  have hpoint : ∀ angles : Fin dimension → ℝ,
      HasSum (fun power =>
        evenWeylMomentSeriesTerm dimension parameter power angles)
        (Real.exp (parameter * cosineCubeScale angles) *
          evenWeylAngleWeight dimension angles) := by
    intro angles
    have h := (NormedSpace.expSeries_div_hasSum_exp
      (parameter * cosineCubeScale angles)).mul_right
        (evenWeylAngleWeight dimension angles)
    rw [show (fun power =>
        evenWeylMomentSeriesTerm dimension parameter power angles) =
      fun power => (parameter * cosineCubeScale angles) ^ power /
        (power.factorial : ℝ) * evenWeylAngleWeight dimension angles by
      funext power
      unfold evenWeylMomentSeriesTerm
      rw [mul_pow]
      ring]
    simpa only [Real.exp_eq_exp_ℝ, mul_comm] using h
  have hsum := hasSum_integral_of_dominated_convergence
    (fun power : ℕ => fun angles : Fin dimension → ℝ =>
      ‖evenWeylAngleWeight dimension angles‖ *
        ((2 * dimension : ℝ) * |parameter|) ^ power /
          (power.factorial : ℝ))
    (fun power => (hterm power).aestronglyMeasurable)
    (fun power => Filter.Eventually.of_forall fun angles => hbound power angles)
    (Filter.Eventually.of_forall hsummable)
    (by
      rw [show (fun angles : Fin dimension → ℝ => ∑' power : ℕ,
          ‖evenWeylAngleWeight dimension angles‖ *
            ((2 * dimension : ℝ) * |parameter|) ^ power /
              (power.factorial : ℝ)) =
        fun angles => ‖evenWeylAngleWeight dimension angles‖ *
          Real.exp ((2 * dimension : ℝ) * |parameter|) by
        funext angles
        exact htsum angles]
      exact ((integrable_continuous_cosineCube
        (continuous_evenWeylAngleWeight dimension)).norm).mul_const _)
    (Filter.Eventually.of_forall hpoint)
  rw [show (fun power => evenWeylGeometricMoment dimension power /
      (power.factorial : ℝ) * parameter ^ power) =
      fun power => ∫ angles : Fin dimension → ℝ,
        evenWeylMomentSeriesTerm dimension parameter power angles
        ∂cosineCubeProductMeasure dimension by
    funext power
    unfold evenWeylMomentSeriesTerm evenWeylGeometricMoment
      weightedCosineCubeMoment weightedCosineCubePowerIntegrand
    rw [show (fun angles : Fin dimension → ℝ =>
        evenWeylAngleWeight dimension angles * cosineCubeScale angles ^ power /
          (power.factorial : ℝ) * parameter ^ power) =
      fun angles => (parameter ^ power / (power.factorial : ℝ)) *
        (cosineCubeScale angles ^ power *
          evenWeylAngleWeight dimension angles) by
      funext angles
      ring, integral_const_mul]
    ring]
  unfold evenWeylExponentialIntegral
  exact hsum

theorem evenWeylMomentSeriesGeneralR_hasSum
    (dimension : ℕ) (parameter : ℝ) :
    RealPowerSeriesHasSum (evenWeylMomentSeriesGeneralR dimension) parameter
      (evenWeylExponentialIntegral dimension parameter) := by
  unfold RealPowerSeriesHasSum realPowerSeriesTerm
    evenWeylMomentSeriesGeneralR
  simpa using evenWeylGeometricMoment_hasSum dimension parameter

theorem evenWeylSeriesGeneralR_hasSum
    (dimension : ℕ) (parameter : ℝ) :
    RealPowerSeriesHasSum (evenWeylSeriesGeneralR dimension) parameter
      (evenWeylNormalization dimension *
        evenWeylExponentialIntegral dimension parameter) :=
  (realPowerSeries_C_hasSum (evenWeylNormalization dimension) parameter).mul
    (evenWeylMomentSeriesGeneralR_hasSum dimension parameter)

theorem oddWeylSeriesGeneralR_hasSum
    (dimension : ℕ) (parameter : ℝ) :
    RealPowerSeriesHasSum (oddWeylSeriesGeneralR dimension) parameter
      (oddWeylNormalization dimension *
        oddWeylExponentialIntegral dimension parameter) :=
  (realPowerSeries_C_hasSum (oddWeylNormalization dimension) parameter).mul
    (oddWeylMomentSeriesR_hasSum dimension parameter)

theorem evenGessel_value_eq_weyl
    {dimension : ℕ} (hdimension : 1 ≤ dimension) (parameter : ℝ) :
    (evenRealGesselMatrixDivPi dimension parameter).det =
      evenWeylNormalization dimension *
        evenWeylExponentialIntegral dimension parameter := by
  rw [evenRealGesselMatrixDivPi_det,
    evenWeylNormalization]
  have h := evenWeylExponentialIntegral_eq_realGessel dimension parameter
  have hfac : (dimension.factorial : ℝ) ≠ 0 := by positivity
  have hpi : Real.pi ^ dimension ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hpowerNat : dimension ≤ dimension ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_left dimension hdimension
  have hpow : (2 : ℝ) ^ (dimension ^ 2) =
      (2 : ℝ) ^ (dimension ^ 2 - dimension) * 2 ^ dimension := by
    rw [← pow_add, Nat.sub_add_cancel hpowerNat]
  rw [hpow] at h
  have htwoNe : (2 : ℝ) ^ dimension ≠ 0 := by positivity
  have hcancel : (2 : ℝ) ^ (dimension ^ 2 - dimension) *
      evenWeylExponentialIntegral dimension parameter =
      (dimension.factorial : ℝ) *
        (evenRealGesselMatrix dimension parameter).det := by
    apply mul_left_cancel₀ htwoNe
    linear_combination h
  rw [one_div_pow]
  field_simp [hfac, hpi]
  linear_combination -hcancel

theorem oddGessel_value_eq_weyl
    {dimension : ℕ} (hdimension : 1 ≤ dimension) (parameter : ℝ) :
    Real.exp parameter *
        (oddRealGesselMatrixDivPi dimension parameter).det =
      oddWeylNormalization dimension *
        oddWeylExponentialIntegral dimension parameter := by
  rw [oddRealGesselMatrixDivPi_det,
    oddWeylNormalization]
  have h := oddWeylExponentialIntegral_eq_realGessel
    (dimension := dimension) hdimension parameter
  have hfac : (dimension.factorial : ℝ) ≠ 0 := by positivity
  have hpi : Real.pi ^ dimension ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hpow : (2 : ℝ) ^ (dimension * (dimension + 1)) =
      (2 : ℝ) ^ (dimension ^ 2) * 2 ^ dimension := by
    rw [← pow_add]
    congr 1
    rw [pow_two]
    ring
  rw [hpow] at h
  have htwoNe : (2 : ℝ) ^ dimension ≠ 0 := by positivity
  have hcancel : (2 : ℝ) ^ (dimension ^ 2) *
      oddWeylExponentialIntegral dimension parameter =
      (dimension.factorial : ℝ) * Real.exp parameter *
        (oddRealGesselMatrix dimension parameter).det := by
    apply mul_left_cancel₀ htwoNe
    linear_combination h
  rw [one_div_pow]
  field_simp [hfac, hpi]
  linear_combination -hcancel

theorem evenFormalGesselDet_eq_weylSeries
    {dimension : ℕ} (hdimension : 1 ≤ dimension) :
    (evenFormalGesselMatrixR dimension).det =
      evenWeylSeriesGeneralR dimension := by
  have hgAt := realPowerSeriesFML_hasFPowerSeriesAt
    (evenFormalGesselMatrixR dimension).det
    (evenFormalGesselDet_hasSum dimension 1)
  have hwAt := realPowerSeriesFML_hasFPowerSeriesAt
    (evenWeylSeriesGeneralR dimension)
    (evenWeylSeriesGeneralR_hasSum dimension 1)
  have hf :
      (realPowerSeriesFML (evenFormalGesselMatrixR dimension).det).sum =
        (realPowerSeriesFML (evenWeylSeriesGeneralR dimension)).sum := by
    funext parameter
    rw [realPowerSeriesFML_sum_eq, realPowerSeriesFML_sum_eq]
    have hg := evenFormalGesselDet_hasSum dimension parameter
    have hw := evenWeylSeriesGeneralR_hasSum dimension parameter
    change (∑' power : ℕ, realPowerSeriesTerm
        (evenFormalGesselMatrixR dimension).det parameter power) =
      ∑' power : ℕ, realPowerSeriesTerm
        (evenWeylSeriesGeneralR dimension) parameter power
    rw [hg.tsum_eq, hw.tsum_eq, evenGessel_value_eq_weyl hdimension]
  rw [hf] at hgAt
  have heq := hgAt.eq_formalMultilinearSeries hwAt
  ext power
  have hc := congrArg (fun series : FormalMultilinearSeries ℝ ℝ ℝ =>
    series power (fun _ : Fin power => (1 : ℝ))) heq
  simpa [realPowerSeriesFML] using hc

theorem oddFormalGesselSeries_eq_weylSeries
    {dimension : ℕ} (hdimension : 1 ≤ dimension) :
    oddFormalGesselSeriesR dimension = oddWeylSeriesGeneralR dimension := by
  have hg : RealPowerSeriesHasSum (oddFormalGesselSeriesR dimension) 1
      (Real.exp 1 *
        (oddRealGesselMatrixDivPi dimension 1).det) := by
    unfold oddFormalGesselSeriesR
    exact (realExponentialSeries_hasSum 1).mul
      (oddFormalGesselDet_hasSum dimension 1)
  have hw := oddWeylSeriesGeneralR_hasSum dimension 1
  have hgAt := realPowerSeriesFML_hasFPowerSeriesAt
    (oddFormalGesselSeriesR dimension) hg
  have hwAt := realPowerSeriesFML_hasFPowerSeriesAt
    (oddWeylSeriesGeneralR dimension) hw
  have hf :
      (realPowerSeriesFML (oddFormalGesselSeriesR dimension)).sum =
        (realPowerSeriesFML (oddWeylSeriesGeneralR dimension)).sum := by
    funext parameter
    rw [realPowerSeriesFML_sum_eq, realPowerSeriesFML_sum_eq]
    have hdet := oddFormalGesselDet_hasSum dimension parameter
    have hleft := (realExponentialSeries_hasSum parameter).mul hdet
    have hright := oddWeylSeriesGeneralR_hasSum dimension parameter
    change RealPowerSeriesHasSum (oddFormalGesselSeriesR dimension) parameter
      (Real.exp parameter *
        (oddRealGesselMatrixDivPi dimension parameter).det) at hleft
    change (∑' power : ℕ,
        realPowerSeriesTerm (oddFormalGesselSeriesR dimension) parameter power) =
      ∑' power : ℕ,
        realPowerSeriesTerm (oddWeylSeriesGeneralR dimension) parameter power
    rw [hleft.tsum_eq, hright.tsum_eq,
      oddGessel_value_eq_weyl hdimension]
  rw [hf] at hgAt
  have heq := hgAt.eq_formalMultilinearSeries hwAt
  ext power
  have hc := congrArg (fun series : FormalMultilinearSeries ℝ ℝ ℝ =>
    series power (fun _ : Fin power => (1 : ℝ))) heq
  simpa [realPowerSeriesFML] using hc

end FibonacciRibbonKernel
