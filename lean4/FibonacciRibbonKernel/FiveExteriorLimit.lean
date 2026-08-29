import FibonacciRibbonKernel.FiveExteriorCoefficient
import FibonacciRibbonKernel.FactorialDifferential

namespace FibonacciRibbonKernel

open PowerSeries

noncomputable def fiveExteriorLimitSeries : ℚ⟦X⟧ :=
  PowerSeries.mk fun degree =>
    if 10 ≤ degree then
      PowerSeries.coeff degree
        (fiveExteriorTruncation (degree + 1))
    else 0

theorem X_ten_mul_heightFive_factorialSeries_eq_exteriorLimit :
    X ^ 10 * factorialSeries (fun size => (heightFiveTableauCount size : ℚ)) =
      fiveExteriorLimitSeries := by
  ext degree
  rw [fiveExteriorLimitSeries, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow_mul']
  by_cases hdegree : 10 ≤ degree
  · rw [if_pos hdegree, if_pos hdegree]
    let size := degree - 10
    have hdegreeEq : degree = size + 10 := by
      dsimp only [size]
      omega
    rw [hdegreeEq, Nat.add_sub_cancel, factorialSeries_coeff]
    rw [fiveExteriorTruncation_coeff_eq_tableaux_of_bound size
      (size + 10 + 1) (by omega)]
  · rw [if_neg hdegree, if_neg hdegree]

noncomputable def fiveTruncatedPfaffian (bound : ℕ) : ℚ⟦X⟧ :=
  let rows := (List.range bound).reverse.map fiveFactorialPowerSeriesRow
  borderedPfaffianFive (fivePairSum rows) (fiveRowSum rows)

theorem fiveExteriorTruncation_eq_truncatedPfaffian (bound : ℕ) :
    fiveExteriorTruncation bound = fiveTruncatedPfaffian bound := by
  let rows := (List.range bound).reverse.map fiveFactorialPowerSeriesRow
  have hminor :=
    topFiveDeterminant_exteriorElementary_five_eq_borderedPfaffian
      (R := ℚ⟦X⟧) rows
  change 2 * fiveExteriorTruncation bound =
      2 * fiveTruncatedPfaffian bound at hminor
  have htwo : (2 : ℚ⟦X⟧) ≠ 0 := by
    intro hzero
    have hcast : (2 : ℚ⟦X⟧) = PowerSeries.C (2 : ℚ) := by
      exact (map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 2).symm
    rw [hcast] at hzero
    have hC : PowerSeries.C (2 : ℚ) = PowerSeries.C 0 :=
      hzero.trans (map_zero PowerSeries.C).symm
    have htwoZero := PowerSeries.C_injective hC
    norm_num at htwoZero
  exact mul_left_cancel₀ htwo hminor

noncomputable def fivePfaffianLimitSeries : ℚ⟦X⟧ :=
  PowerSeries.mk fun degree =>
    if 10 ≤ degree then
      PowerSeries.coeff degree
        (fiveTruncatedPfaffian (degree + 1))
    else 0

theorem fiveExteriorLimitSeries_eq_fivePfaffianLimitSeries :
    fiveExteriorLimitSeries = fivePfaffianLimitSeries := by
  ext degree
  rw [fiveExteriorLimitSeries, fivePfaffianLimitSeries,
    PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  by_cases hdegree : 10 ≤ degree
  · rw [if_pos hdegree, if_pos hdegree,
      fiveExteriorTruncation_eq_truncatedPfaffian]
  · rw [if_neg hdegree, if_neg hdegree]

theorem X_ten_mul_heightFive_factorialSeries_eq_pfaffianLimit :
    X ^ 10 * factorialSeries (fun size => (heightFiveTableauCount size : ℚ)) =
      fivePfaffianLimitSeries := by
  rw [X_ten_mul_heightFive_factorialSeries_eq_exteriorLimit,
    fiveExteriorLimitSeries_eq_fivePfaffianLimitSeries]

end FibonacciRibbonKernel
