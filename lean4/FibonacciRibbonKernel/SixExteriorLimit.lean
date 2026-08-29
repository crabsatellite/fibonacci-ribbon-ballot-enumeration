import FibonacciRibbonKernel.SixExteriorCoefficient
import FibonacciRibbonKernel.FactorialDifferential

namespace FibonacciRibbonKernel

open PowerSeries

noncomputable def sixExteriorLimitSeries : ℚ⟦X⟧ :=
  PowerSeries.mk fun degree =>
    if 15 ≤ degree then
      PowerSeries.coeff degree (sixExteriorTruncation (degree + 1))
    else 0

theorem X_fifteen_mul_heightSix_factorialSeries_eq_exteriorLimit :
    X ^ 15 * factorialSeries (fun size => (heightSixTableauCount size : ℚ)) =
      sixExteriorLimitSeries := by
  ext degree
  rw [sixExteriorLimitSeries, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow_mul']
  by_cases hdegree : 15 ≤ degree
  · rw [if_pos hdegree, if_pos hdegree]
    let size := degree - 15
    have hdegreeEq : degree = size + 15 := by
      dsimp only [size]
      omega
    rw [hdegreeEq, Nat.add_sub_cancel, factorialSeries_coeff]
    rw [sixExteriorTruncation_coeff_eq_tableaux_of_bound size
      (size + 15 + 1) (by omega)]
  · rw [if_neg hdegree, if_neg hdegree]

noncomputable def sixTruncatedCubic (bound : ℕ) : ℚ⟦X⟧ :=
  let rows := (List.range bound).reverse.map sixFactorialPowerSeriesRow
  topSixDeterminant (R := ℚ⟦X⟧) (exteriorElementary 2 rows ^ 3)

theorem sixTruncatedCubic_eq_six_mul_exterior (bound : ℕ) :
    sixTruncatedCubic bound = 6 * sixExteriorTruncation bound := by
  let rows := (List.range bound).reverse.map sixFactorialPowerSeriesRow
  have hminor := topSixDeterminant_exterior_minor_sum
    (R := ℚ⟦X⟧) rows
  change sixTruncatedCubic bound = 6 * sixExteriorTruncation bound at hminor
  exact hminor

noncomputable def sixCubicLimitSeries : ℚ⟦X⟧ :=
  PowerSeries.mk fun degree =>
    if 15 ≤ degree then
      PowerSeries.coeff degree (sixTruncatedCubic (degree + 1))
    else 0

theorem sixCubicLimitSeries_eq_six_mul_exteriorLimit :
    sixCubicLimitSeries = 6 * sixExteriorLimitSeries := by
  ext degree
  rw [sixCubicLimitSeries, sixExteriorLimitSeries,
    PowerSeries.coeff_mk]
  have hcast : (6 : ℚ⟦X⟧) = PowerSeries.C (6 : ℚ) := by
    exact (map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 6).symm
  rw [hcast, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
  by_cases hdegree : 15 ≤ degree
  · rw [if_pos hdegree, if_pos hdegree,
      sixTruncatedCubic_eq_six_mul_exterior]
    rw [hcast, PowerSeries.coeff_C_mul]
  · rw [if_neg hdegree, if_neg hdegree]
    simp

theorem six_mul_X_fifteen_heightSix_factorialSeries_eq_cubicLimit :
    6 * (X ^ 15 *
        factorialSeries (fun size => (heightSixTableauCount size : ℚ))) =
      sixCubicLimitSeries := by
  rw [X_fifteen_mul_heightSix_factorialSeries_eq_exteriorLimit,
    sixCubicLimitSeries_eq_six_mul_exteriorLimit]

end FibonacciRibbonKernel
