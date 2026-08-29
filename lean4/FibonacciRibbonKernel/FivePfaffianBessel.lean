import FibonacciRibbonKernel.FivePairShift
import FibonacciRibbonKernel.DensityLimits

namespace FibonacciRibbonKernel

open PowerSeries

noncomputable def pairQ1 : ℚ⟦X⟧ :=
  literalBesselJ 0 + literalBesselJ 1

noncomputable def pairQ2 : ℚ⟦X⟧ :=
  literalBesselJ 0 + 2 * literalBesselJ 1 + literalBesselJ 2

noncomputable def pairQ3 : ℚ⟦X⟧ :=
  literalBesselJ 0 + 2 * literalBesselJ 1 +
    2 * literalBesselJ 2 + literalBesselJ 3

noncomputable def pairQ4 : ℚ⟦X⟧ :=
  literalBesselJ 0 + 2 * literalBesselJ 1 +
    2 * literalBesselJ 2 + 2 * literalBesselJ 3 + literalBesselJ 4

theorem fiveClosedPair_three_four_explicit :
    fiveClosedPair 3 4 = X * pairQ1 := by
  exact fiveClosedPair_three_four_eq_bessel

theorem fiveClosedPair_two_four_explicit :
    fiveClosedPair 2 4 = X ^ 2 * pairQ2 := by
  exact fiveClosedPair_two_four_eq_bessel

theorem fiveClosedPair_one_four_explicit :
    fiveClosedPair 1 4 = X ^ 3 * pairQ3 := by
  exact fiveClosedPair_one_four_eq_bessel

theorem fiveClosedPair_zero_four_explicit :
    fiveClosedPair 0 4 = X ^ 4 * pairQ4 := by
  exact fiveClosedPair_zero_four_eq_bessel

theorem fiveClosedPair_two_three_explicit :
    fiveClosedPair 2 3 = X ^ 3 * pairQ1 := by
  have hshift := fiveClosedPair_shift 1 2 3 3 4 (by decide) (by decide)
  rw [hshift, fiveClosedPair_three_four_explicit]
  norm_num
  ring

theorem fiveClosedPair_one_two_explicit :
    fiveClosedPair 1 2 = X ^ 5 * pairQ1 := by
  have hshift := fiveClosedPair_shift 2 1 2 3 4 (by decide) (by decide)
  rw [hshift, fiveClosedPair_three_four_explicit]
  norm_num
  ring

theorem fiveClosedPair_zero_one_explicit :
    fiveClosedPair 0 1 = X ^ 7 * pairQ1 := by
  have hshift := fiveClosedPair_shift 3 0 1 3 4 (by decide) (by decide)
  rw [hshift, fiveClosedPair_three_four_explicit]
  norm_num
  ring

theorem fiveClosedPair_one_three_explicit :
    fiveClosedPair 1 3 = X ^ 4 * pairQ2 := by
  have hshift := fiveClosedPair_shift 1 1 3 2 4 (by decide) (by decide)
  rw [hshift, fiveClosedPair_two_four_explicit]
  norm_num
  ring

theorem fiveClosedPair_zero_two_explicit :
    fiveClosedPair 0 2 = X ^ 6 * pairQ2 := by
  have hshift := fiveClosedPair_shift 2 0 2 2 4 (by decide) (by decide)
  rw [hshift, fiveClosedPair_two_four_explicit]
  norm_num
  ring

theorem fiveClosedPair_zero_three_explicit :
    fiveClosedPair 0 3 = X ^ 5 * pairQ3 := by
  have hshift := fiveClosedPair_shift 1 0 3 1 4 (by decide) (by decide)
  rw [hshift, fiveClosedPair_one_four_explicit]
  norm_num
  ring

theorem fiveClosedPfaffian_eq_X_ten_gessel :
    fiveClosedPfaffian = X ^ 10 * gesselHeightFiveSeries := by
  unfold fiveClosedPfaffian borderedPfaffianFive
  rw [fiveClosedPair_zero_one_explicit,
    fiveClosedPair_zero_two_explicit,
    fiveClosedPair_zero_three_explicit,
    fiveClosedPair_zero_four_explicit,
    fiveClosedPair_one_two_explicit,
    fiveClosedPair_one_three_explicit,
    fiveClosedPair_one_four_explicit,
    fiveClosedPair_two_three_explicit,
    fiveClosedPair_two_four_explicit,
    fiveClosedPair_three_four_explicit]
  unfold fiveClosedSingle pairQ1 pairQ2 pairQ3 pairQ4
  unfold gesselHeightFiveSeries
  norm_num [Fin.rev]
  ring

theorem fiveClosedPfaffianLimitSeries_eq_X_ten_gessel :
    fiveClosedPfaffianLimitSeries = X ^ 10 * gesselHeightFiveSeries := by
  ext degree
  rw [fiveClosedPfaffianLimitSeries, PowerSeries.coeff_mk]
  by_cases hdegree : 10 ≤ degree
  · rw [if_pos hdegree, fiveClosedPfaffian_eq_X_ten_gessel]
  · rw [if_neg hdegree, PowerSeries.coeff_X_pow_mul', if_neg hdegree]

theorem factorialSeries_heightFiveTableauCount_eq_gessel :
    factorialSeries (fun size => (heightFiveTableauCount size : ℚ)) =
      gesselHeightFiveSeries := by
  apply PowerSeries.X_pow_mul_cancel (k := 10)
  rw [X_ten_mul_heightFive_factorialSeries_eq_pfaffianLimit,
    fivePfaffianLimitSeries_eq_closedPfaffianLimit,
    fiveClosedPfaffianLimitSeries_eq_X_ten_gessel]

theorem factorialSeries_heightFiveTableauCount_eq_bessel :
    factorialSeries (fun size => (heightFiveTableauCount size : ℚ)) =
      heightFiveBesselSeries := by
  rw [factorialSeries_heightFiveTableauCount_eq_gessel,
    gesselHeightFiveSeries_eq_besselSeries]

theorem heightFiveTableauCount_eq_besselSequence (size : ℕ) :
    (heightFiveTableauCount size : ℚ) = heightFiveBesselSequence size := by
  have hcoeff := congrArg (PowerSeries.coeff size)
    factorialSeries_heightFiveTableauCount_eq_bessel
  rw [factorialSeries_coeff] at hcoeff
  unfold heightFiveBesselSequence
  have hfactorial : (size.factorial : ℚ) ≠ 0 := by positivity
  field_simp at hcoeff ⊢
  exact hcoeff

theorem heightFiveTableauCount_initial :
    heightFiveTableauCount 0 = 1 ∧
      heightFiveTableauCount 1 = 1 ∧
      heightFiveTableauCount 2 = 2 := by
  unfold heightFiveTableauCount
  constructor
  · rw [unrestrictedCount_eq_involutionNumber_of_stable_height 5 0 (by omega),
      involutionNumber_zero]
  constructor
  · rw [unrestrictedCount_eq_involutionNumber_of_stable_height 5 1 (by omega),
      involutionNumber_one]
  · rw [unrestrictedCount_eq_involutionNumber_of_stable_height 5 2 (by omega),
      involutionNumber_two]

theorem heightFiveTableauCount_recurrence
    (index : ℕ) (hindex : 3 ≤ index) :
    (index + 4 : ℚ) * (index + 6 : ℚ) * heightFiveTableauCount index -
        (3 * index ^ 2 + 17 * index + 15 : ℚ) *
          heightFiveTableauCount (index - 1) -
        (index - 1 : ℚ) * (13 * index + 9 : ℚ) *
          heightFiveTableauCount (index - 2) +
        15 * (index - 1 : ℚ) * (index - 2 : ℚ) *
          heightFiveTableauCount (index - 3) = 0 := by
  rw [heightFiveTableauCount_eq_besselSequence,
    heightFiveTableauCount_eq_besselSequence,
    heightFiveTableauCount_eq_besselSequence,
    heightFiveTableauCount_eq_besselSequence]
  exact heightFiveBesselSequence_recurrence index hindex

end FibonacciRibbonKernel
