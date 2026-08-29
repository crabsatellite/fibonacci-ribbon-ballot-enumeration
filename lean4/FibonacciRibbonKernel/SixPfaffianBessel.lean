import FibonacciRibbonKernel.SixPairShift
import FibonacciRibbonKernel.SixPfaffianLimit

namespace FibonacciRibbonKernel

open PowerSeries

theorem sixClosedPair_four_five_explicit :
    sixClosedPair 4 5 = X * pairQ1 := by
  rw [show sixClosedPair (4 : Fin 6) 5 = fiveClosedPair 3 4 by
    simpa using sixClosedPair_succColumns_eq_five (3 : Fin 5) (4 : Fin 5)]
  exact fiveClosedPair_three_four_explicit

theorem sixClosedPair_three_five_explicit :
    sixClosedPair 3 5 = X ^ 2 * pairQ2 := by
  rw [show sixClosedPair (3 : Fin 6) 5 = fiveClosedPair 2 4 by
    simpa using sixClosedPair_succColumns_eq_five (2 : Fin 5) (4 : Fin 5)]
  exact fiveClosedPair_two_four_explicit

theorem sixClosedPair_two_five_explicit :
    sixClosedPair 2 5 = X ^ 3 * pairQ3 := by
  rw [show sixClosedPair (2 : Fin 6) 5 = fiveClosedPair 1 4 by
    simpa using sixClosedPair_succColumns_eq_five (1 : Fin 5) (4 : Fin 5)]
  exact fiveClosedPair_one_four_explicit

theorem sixClosedPair_one_five_explicit :
    sixClosedPair 1 5 = X ^ 4 * pairQ4 := by
  rw [show sixClosedPair (1 : Fin 6) 5 = fiveClosedPair 0 4 by
    simpa using sixClosedPair_succColumns_eq_five (0 : Fin 5) (4 : Fin 5)]
  exact fiveClosedPair_zero_four_explicit

theorem sixClosedPair_zero_five_explicit :
    sixClosedPair 0 5 = X ^ 5 * pairQ5 :=
  sixClosedPair_zero_five_eq_bessel

theorem sixClosedPair_three_four_explicit :
    sixClosedPair 3 4 = X ^ 3 * pairQ1 := by
  rw [show sixClosedPair (3 : Fin 6) 4 = fiveClosedPair 2 3 by
    simpa using sixClosedPair_succColumns_eq_five (2 : Fin 5) (3 : Fin 5)]
  exact fiveClosedPair_two_three_explicit

theorem sixClosedPair_two_three_explicit :
    sixClosedPair 2 3 = X ^ 5 * pairQ1 := by
  rw [show sixClosedPair (2 : Fin 6) 3 = fiveClosedPair 1 2 by
    simpa using sixClosedPair_succColumns_eq_five (1 : Fin 5) (2 : Fin 5)]
  exact fiveClosedPair_one_two_explicit

theorem sixClosedPair_one_two_explicit :
    sixClosedPair 1 2 = X ^ 7 * pairQ1 := by
  rw [show sixClosedPair (1 : Fin 6) 2 = fiveClosedPair 0 1 by
    simpa using sixClosedPair_succColumns_eq_five (0 : Fin 5) (1 : Fin 5)]
  exact fiveClosedPair_zero_one_explicit

theorem sixClosedPair_two_four_explicit :
    sixClosedPair 2 4 = X ^ 4 * pairQ2 := by
  rw [show sixClosedPair (2 : Fin 6) 4 = fiveClosedPair 1 3 by
    simpa using sixClosedPair_succColumns_eq_five (1 : Fin 5) (3 : Fin 5)]
  exact fiveClosedPair_one_three_explicit

theorem sixClosedPair_one_three_explicit :
    sixClosedPair 1 3 = X ^ 6 * pairQ2 := by
  rw [show sixClosedPair (1 : Fin 6) 3 = fiveClosedPair 0 2 by
    simpa using sixClosedPair_succColumns_eq_five (0 : Fin 5) (2 : Fin 5)]
  exact fiveClosedPair_zero_two_explicit

theorem sixClosedPair_one_four_explicit :
    sixClosedPair 1 4 = X ^ 5 * pairQ3 := by
  rw [show sixClosedPair (1 : Fin 6) 4 = fiveClosedPair 0 3 by
    simpa using sixClosedPair_succColumns_eq_five (0 : Fin 5) (3 : Fin 5)]
  exact fiveClosedPair_zero_three_explicit

theorem sixClosedPair_zero_one_explicit :
    sixClosedPair 0 1 = X ^ 9 * pairQ1 := by
  have hshift := sixClosedPair_shift 4 0 1 4 5 (by decide) (by decide)
  rw [hshift, sixClosedPair_four_five_explicit]
  norm_num
  ring

theorem sixClosedPair_zero_two_explicit :
    sixClosedPair 0 2 = X ^ 8 * pairQ2 := by
  have hshift := sixClosedPair_shift 3 0 2 3 5 (by decide) (by decide)
  rw [hshift, sixClosedPair_three_five_explicit]
  norm_num
  ring

theorem sixClosedPair_zero_three_explicit :
    sixClosedPair 0 3 = X ^ 7 * pairQ3 := by
  have hshift := sixClosedPair_shift 2 0 3 2 5 (by decide) (by decide)
  rw [hshift, sixClosedPair_two_five_explicit]
  norm_num
  ring

theorem sixClosedPair_zero_four_explicit :
    sixClosedPair 0 4 = X ^ 6 * pairQ4 := by
  have hshift := sixClosedPair_shift 1 0 4 1 5 (by decide) (by decide)
  rw [hshift, sixClosedPair_one_five_explicit]
  norm_num
  ring

theorem sixClosedPfaffian_eq_X_fifteen_gessel :
    sixClosedPfaffian = X ^ 15 * gesselHeightSixSeries := by
  unfold sixClosedPfaffian pfaffianSix
  rw [sixClosedPair_zero_one_explicit,
    sixClosedPair_zero_two_explicit,
    sixClosedPair_zero_three_explicit,
    sixClosedPair_zero_four_explicit,
    sixClosedPair_zero_five_explicit,
    sixClosedPair_one_two_explicit,
    sixClosedPair_one_three_explicit,
    sixClosedPair_one_four_explicit,
    sixClosedPair_one_five_explicit,
    sixClosedPair_two_three_explicit,
    sixClosedPair_two_four_explicit,
    sixClosedPair_two_five_explicit,
    sixClosedPair_three_four_explicit,
    sixClosedPair_three_five_explicit,
    sixClosedPair_four_five_explicit]
  unfold pairQ1 pairQ2 pairQ3 pairQ4 pairQ5
  unfold gesselHeightSixSeries
  ring

theorem sixClosedPfaffianLimitSeries_eq_X_fifteen_gessel :
    sixClosedPfaffianLimitSeries = X ^ 15 * gesselHeightSixSeries := by
  ext degree
  rw [sixClosedPfaffianLimitSeries, PowerSeries.coeff_mk]
  by_cases hdegree : 15 ≤ degree
  · rw [if_pos hdegree, sixClosedPfaffian_eq_X_fifteen_gessel]
  · rw [if_neg hdegree, PowerSeries.coeff_X_pow_mul', if_neg hdegree]

theorem factorialSeries_heightSixTableauCount_eq_gessel :
    factorialSeries (fun size => (heightSixTableauCount size : ℚ)) =
      gesselHeightSixSeries := by
  apply PowerSeries.X_pow_mul_cancel (k := 15)
  rw [X_fifteen_heightSix_factorialSeries_eq_closedPfaffianLimit,
    sixClosedPfaffianLimitSeries_eq_X_fifteen_gessel]

theorem factorialSeries_heightSixTableauCount_eq_bessel :
    factorialSeries (fun size => (heightSixTableauCount size : ℚ)) =
      heightSixBesselSeries := by
  rw [factorialSeries_heightSixTableauCount_eq_gessel,
    gesselHeightSixSeries_eq_besselSeries]

theorem heightSixTableauCount_eq_besselSequence (size : ℕ) :
    (heightSixTableauCount size : ℚ) = heightSixBesselSequence size := by
  have hcoeff := congrArg (PowerSeries.coeff size)
    factorialSeries_heightSixTableauCount_eq_bessel
  rw [factorialSeries_coeff] at hcoeff
  unfold heightSixBesselSequence
  have hfactorial : (size.factorial : ℚ) ≠ 0 := by positivity
  field_simp at hcoeff ⊢
  exact hcoeff

theorem heightSixTableauCount_initial :
    heightSixTableauCount 0 = 1 ∧ heightSixTableauCount 1 = 1 ∧
      heightSixTableauCount 2 = 2 ∧ heightSixTableauCount 3 = 4 := by
  unfold heightSixTableauCount
  constructor
  · rw [unrestrictedCount_eq_involutionNumber_of_stable_height 6 0 (by omega),
      involutionNumber_zero]
  constructor
  · rw [unrestrictedCount_eq_involutionNumber_of_stable_height 6 1 (by omega),
      involutionNumber_one]
  constructor
  · rw [unrestrictedCount_eq_involutionNumber_of_stable_height 6 2 (by omega),
      involutionNumber_two]
  · rw [unrestrictedCount_eq_involutionNumber_of_stable_height 6 3 (by omega),
      involutionNumber_three]

theorem heightSixTableauCount_recurrence
    (index : ℕ) (hindex : 4 ≤ index) :
    (index + 5 : ℚ) * (index + 8 : ℚ) * (index + 9 : ℚ) *
          heightSixTableauCount index -
        4 * (5 * index ^ 2 + 46 * index + 84 : ℚ) *
          heightSixTableauCount (index - 1) -
        4 * (index - 1 : ℚ) * (10 * index ^ 2 + 58 * index + 33 : ℚ) *
          heightSixTableauCount (index - 2) +
        144 * (index - 1 : ℚ) * (index - 2 : ℚ) *
          heightSixTableauCount (index - 3) +
        144 * (index - 1 : ℚ) * (index - 2 : ℚ) * (index - 3 : ℚ) *
          heightSixTableauCount (index - 4) = 0 := by
  rw [heightSixTableauCount_eq_besselSequence,
    heightSixTableauCount_eq_besselSequence,
    heightSixTableauCount_eq_besselSequence,
    heightSixTableauCount_eq_besselSequence,
    heightSixTableauCount_eq_besselSequence]
  exact heightSixBesselSequence_recurrence index hindex

end FibonacciRibbonKernel
