import FibonacciRibbonKernel.OddMomentHasSum
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.OfScalars

namespace FibonacciRibbonKernel

open PowerSeries

noncomputable def oddWeylMomentSeriesR (dimension : ℕ) : ℝ⟦X⟧ :=
  PowerSeries.mk fun power =>
    oddWeylGeometricMoment dimension power / (power.factorial : ℝ)

@[simp] theorem oddWeylMomentSeriesR_coeff
    (dimension power : ℕ) :
    PowerSeries.coeff power (oddWeylMomentSeriesR dimension) =
      oddWeylGeometricMoment dimension power / (power.factorial : ℝ) := by
  simp [oddWeylMomentSeriesR]

theorem oddWeylMomentSeriesR_hasSum
    (dimension : ℕ) (parameter : ℝ) :
    RealPowerSeriesHasSum (oddWeylMomentSeriesR dimension) parameter
      (oddWeylExponentialIntegral dimension parameter) := by
  unfold RealPowerSeriesHasSum realPowerSeriesTerm
  simpa only [oddWeylMomentSeriesR_coeff] using
    oddWeylGeometricMoment_hasSum dimension parameter

theorem realPowerSeries_C_hasSum (constant parameter : ℝ) :
    RealPowerSeriesHasSum (PowerSeries.C constant) parameter constant := by
  unfold RealPowerSeriesHasSum realPowerSeriesTerm
  rw [show (fun power : ℕ =>
      PowerSeries.coeff power (PowerSeries.C constant) * parameter ^ power) =
      fun power => if power = 0 then constant else 0 by
    funext power
    by_cases hpower : power = 0
    · subst power
      simp
    · simp [PowerSeries.coeff_C, hpower]]
  exact hasSum_ite_eq 0 constant

noncomputable def realPowerSeriesFML (series : ℝ⟦X⟧) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ fun power =>
    PowerSeries.coeff power series

theorem realPowerSeriesFML_sum_eq (series : ℝ⟦X⟧) :
    (realPowerSeriesFML series).sum =
      fun parameter => ∑' power : ℕ,
        realPowerSeriesTerm series parameter power := by
  funext parameter
  unfold realPowerSeriesFML FormalMultilinearSeries.sum
  apply tsum_congr
  intro power
  simp [realPowerSeriesTerm, smul_eq_mul, mul_comm]

theorem realPowerSeriesFML_radius_pos
    (series : ℝ⟦X⟧) {value : ℝ}
    (hsum : RealPowerSeriesHasSum series 1 value) :
    0 < (realPowerSeriesFML series).radius := by
  have habsolute := hsum.norm_summable
  have hsummable : Summable (fun power : ℕ =>
      ‖realPowerSeriesFML series power‖ * (1 : ℝ) ^ power) := by
    apply habsolute.congr
    intro power
    unfold realPowerSeriesFML realPowerSeriesTerm
    rw [FormalMultilinearSeries.ofScalars_norm]
    simp
  have hradius : (1 : ENNReal) ≤ (realPowerSeriesFML series).radius :=
    (realPowerSeriesFML series).le_radius_of_summable_norm hsummable
  exact zero_lt_one.trans_le hradius

theorem realPowerSeriesFML_hasFPowerSeriesAt
    (series : ℝ⟦X⟧) {value : ℝ}
    (hsum : RealPowerSeriesHasSum series 1 value) :
    HasFPowerSeriesAt (realPowerSeriesFML series).sum
      (realPowerSeriesFML series) 0 :=
  ((realPowerSeriesFML series).hasFPowerSeriesOnBall
    (realPowerSeriesFML_radius_pos series hsum)).hasFPowerSeriesAt

noncomputable def rankFiveWeylSeriesR : ℝ⟦X⟧ :=
  PowerSeries.C (8 / Real.pi ^ 2) * oddWeylMomentSeriesR 2

theorem rankFiveWeylSeriesR_hasSum (parameter : ℝ) :
    RealPowerSeriesHasSum rankFiveWeylSeriesR parameter
      ((8 / Real.pi ^ 2) *
        oddWeylExponentialIntegral 2 parameter) := by
  unfold rankFiveWeylSeriesR
  exact (realPowerSeries_C_hasSum (8 / Real.pi ^ 2) parameter).mul
    (oddWeylMomentSeriesR_hasSum 2 parameter)

theorem rankFive_gessel_value_eq_weyl (parameter : ℝ) :
    Real.exp parameter * (1 / Real.pi) ^ 2 *
        (oddRealGesselMatrix 2 parameter).det =
      (8 / Real.pi ^ 2) *
        oddWeylExponentialIntegral 2 parameter := by
  have h := oddWeylExponentialIntegral_eq_realGessel
    (dimension := 2) (by omega) parameter
  norm_num at h
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  nlinarith

theorem rankFive_series_sum_functions_eq :
    (realPowerSeriesFML (oddFormalGesselSeriesR 2)).sum =
      (realPowerSeriesFML rankFiveWeylSeriesR).sum := by
  funext parameter
  rw [realPowerSeriesFML_sum_eq, realPowerSeriesFML_sum_eq]
  have hgessel := oddFormalGesselSeriesR_two_hasSum parameter
  have hweyl := rankFiveWeylSeriesR_hasSum parameter
  change (∑' power : ℕ,
      realPowerSeriesTerm (oddFormalGesselSeriesR 2) parameter power) =
    ∑' power : ℕ,
      realPowerSeriesTerm rankFiveWeylSeriesR parameter power
  rw [hgessel.tsum_eq, hweyl.tsum_eq,
    rankFive_gessel_value_eq_weyl]

theorem oddFormalGesselSeriesR_two_eq_rankFiveWeyl :
    oddFormalGesselSeriesR 2 = rankFiveWeylSeriesR := by
  have hgesselAt := realPowerSeriesFML_hasFPowerSeriesAt
    (oddFormalGesselSeriesR 2)
    (oddFormalGesselSeriesR_two_hasSum 1)
  have hweylAt := realPowerSeriesFML_hasFPowerSeriesAt
    rankFiveWeylSeriesR (rankFiveWeylSeriesR_hasSum 1)
  rw [rankFive_series_sum_functions_eq] at hgesselAt
  have hfml : realPowerSeriesFML (oddFormalGesselSeriesR 2) =
      realPowerSeriesFML rankFiveWeylSeriesR :=
    hgesselAt.eq_formalMultilinearSeries hweylAt
  ext power
  have hcoefficient := congrArg
    (fun series : FormalMultilinearSeries ℝ ℝ ℝ =>
      series power (fun _ : Fin power => (1 : ℝ))) hfml
  simpa [realPowerSeriesFML] using hcoefficient

theorem heightFiveTableauCount_eq_normalized_oddWeylMoment
    (power : ℕ) :
    (heightFiveTableauCount power : ℝ) =
      (8 / Real.pi ^ 2) * oddWeylGeometricMoment 2 power := by
  have hseries := mapped_heightFive_factorialSeries_eq_oddFormalGessel
  rw [oddFormalGesselSeriesR_two_eq_rankFiveWeyl] at hseries
  have hcoeff := congrArg (PowerSeries.coeff power) hseries
  unfold rankFiveWeylSeriesR at hcoeff
  rw [PowerSeries.coeff_map, factorialSeries_coeff,
    PowerSeries.coeff_C_mul, oddWeylMomentSeriesR_coeff] at hcoeff
  have hcast :
      (Rat.castHom ℝ)
          ((heightFiveTableauCount power : ℚ) /
            (power.factorial : ℚ)) =
          (heightFiveTableauCount power : ℝ) /
          (power.factorial : ℝ) := by
    rw [map_div₀]
    norm_num
  rw [hcast] at hcoeff
  have hfactorial : (power.factorial : ℝ) ≠ 0 := by positivity
  field_simp at hcoeff ⊢
  nlinarith

end FibonacciRibbonKernel
