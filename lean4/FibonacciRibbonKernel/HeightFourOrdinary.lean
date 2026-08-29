import FibonacciRibbonKernel.FixedRankAsymptotic
import Mathlib.RingTheory.PowerSeries.Derivative

namespace FibonacciRibbonKernel

open PowerSeries

/-- Euler's operator `X d/dX` on ordinary formal power series. -/
noncomputable def ordinaryEuler (series : ℤ⟦X⟧) : ℤ⟦X⟧ :=
  X * PowerSeries.derivative ℤ series

@[simp] theorem ordinaryEuler_coeff (series : ℤ⟦X⟧) (index : ℕ) :
    PowerSeries.coeff index (ordinaryEuler series) =
      (index : ℤ) * PowerSeries.coeff index series := by
  unfold ordinaryEuler
  rw [show (X : ℤ⟦X⟧) = X ^ 1 by simp,
    PowerSeries.coeff_X_pow_mul']
  by_cases hzero : index = 0
  · subst index
    simp
  · simp only [if_pos (by omega : 1 ≤ index),
      PowerSeries.coeff_derivative]
    rw [show index - 1 + 1 = index by omega]
    rw [Nat.cast_sub (by omega : 1 ≤ index)]
    push_cast
    ring

@[simp] theorem ordinaryEuler_two_coeff (series : ℤ⟦X⟧) (index : ℕ) :
    PowerSeries.coeff index (ordinaryEuler (ordinaryEuler series)) =
      (index : ℤ) ^ 2 * PowerSeries.coeff index series := by
  simp [pow_two]
  ring

/-- The ordinary-series differential operator obtained directly from the
height-four tableau recurrence. -/
noncomputable def heightFourOrdinaryOperator (series : ℤ⟦X⟧) : ℤ⟦X⟧ :=
  ordinaryEuler (ordinaryEuler series) +
      PowerSeries.C 7 * ordinaryEuler series + PowerSeries.C 12 * series -
    X ^ 1 * (PowerSeries.C 8 * ordinaryEuler series +
      PowerSeries.C 20 * series) -
    X ^ 2 * (PowerSeries.C 16 *
      (ordinaryEuler (ordinaryEuler series) +
        PowerSeries.C 3 * ordinaryEuler series +
        PowerSeries.C 2 * series)) - PowerSeries.C 12

theorem unrestrictedGeneratingSeries_three_differential :
    heightFourOrdinaryOperator (unrestrictedGeneratingSeries 3) = 0 := by
  have hu0 : unrestrictedCount 3 0 = 1 := by
    rw [unrestrictedCount_eq_involutionNumber_of_stable_height 4 0 (by omega),
      involutionNumber_zero]
  have hu1 : unrestrictedCount 3 1 = 1 := by
    rw [unrestrictedCount_eq_involutionNumber_of_stable_height 4 1 (by omega),
      involutionNumber_one]
  ext index
  rcases index with _ | _ | index
  · simp only [heightFourOrdinaryOperator, map_add, map_sub,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_C, ordinaryEuler_coeff,
      unrestrictedGeneratingSeries_coeff]
    simp [hu0]
  · simp only [heightFourOrdinaryOperator, map_add, map_sub,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_C, ordinaryEuler_coeff,
      unrestrictedGeneratingSeries_coeff]
    simp [hu0, hu1]
  · have hindex : 2 ≤ index + 2 := by omega
    have hrecQ := heightFourTableauCount_recurrence (index + 2) hindex
    rw [show index + 2 - 1 = index + 1 by omega,
      show index + 2 - 2 = index by omega] at hrecQ
    have hrecQNormalized :
        ((index + 2 : ℚ) + 3) * ((index + 2 : ℚ) + 4) *
              heightFourTableauCount (index + 2) -
            (8 * (index + 2 : ℚ) + 12) *
              heightFourTableauCount (index + 1) -
            16 * (index + 2 : ℚ) * (index + 1 : ℚ) *
              heightFourTableauCount index = 0 := by
      push_cast at hrecQ ⊢
      linear_combination hrecQ
    have hrecZ :
        ((index + 2 : ℤ) + 3) * ((index + 2 : ℤ) + 4) *
              heightFourTableauCount (index + 2) -
            (8 * (index + 2 : ℤ) + 12) *
              heightFourTableauCount (index + 1) -
            16 * (index + 2 : ℤ) * (index + 1 : ℤ) *
              heightFourTableauCount index = 0 := by
      exact_mod_cast hrecQNormalized
    simp only [heightFourOrdinaryOperator, map_add, map_sub,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_C, ordinaryEuler_coeff,
      unrestrictedGeneratingSeries_coeff]
    simp only [if_pos (by omega : 1 ≤ index + 2),
      if_pos (by omega : 2 ≤ index + 2),
      if_neg (by omega : index + 2 ≠ 0)]
    rw [show index + 2 - 1 = index + 1 by omega,
      show index + 2 - 2 = index by omega]
    change _ = _ at hrecZ
    unfold heightFourTableauCount at hrecZ
    simp only [map_zero]
    push_cast at hrecZ ⊢
    linear_combination hrecZ

theorem ordinaryEuler_two_expanded (series : ℤ⟦X⟧) :
    ordinaryEuler (ordinaryEuler series) =
      X ^ 2 * PowerSeries.derivative ℤ (PowerSeries.derivative ℤ series) +
        X * PowerSeries.derivative ℤ series := by
  unfold ordinaryEuler
  change X * PowerSeries.derivativeFun
      (X * PowerSeries.derivativeFun series) = _
  rw [PowerSeries.derivativeFun_mul]
  have hX : PowerSeries.derivativeFun (X : ℤ⟦X⟧) = 1 :=
    PowerSeries.derivative_X
  rw [hX]
  simp only [smul_eq_mul, mul_one]
  change X * (X * series.derivativeFun.derivativeFun + series.derivativeFun) =
    X ^ 2 * series.derivativeFun.derivativeFun + X * series.derivativeFun
  ring

noncomputable def heightFourOrdinaryExpandedOperator
    (series : ℤ⟦X⟧) : ℤ⟦X⟧ :=
  (X ^ 2 - PowerSeries.C 16 * X ^ 4) *
      PowerSeries.derivative ℤ (PowerSeries.derivative ℤ series) +
    (PowerSeries.C 8 * X - PowerSeries.C 8 * X ^ 2 -
      PowerSeries.C 64 * X ^ 3) *
      PowerSeries.derivative ℤ series +
    (PowerSeries.C 12 - PowerSeries.C 20 * X -
      PowerSeries.C 32 * X ^ 2) * series - PowerSeries.C 12

theorem heightFourOrdinaryOperator_eq_expanded (series : ℤ⟦X⟧) :
    heightFourOrdinaryOperator series =
      heightFourOrdinaryExpandedOperator series := by
  rw [heightFourOrdinaryOperator, heightFourOrdinaryExpandedOperator,
    ordinaryEuler_two_expanded]
  unfold ordinaryEuler
  norm_num
  ring

theorem unrestrictedGeneratingSeries_three_expanded_differential :
    heightFourOrdinaryExpandedOperator (unrestrictedGeneratingSeries 3) = 0 := by
  rw [← heightFourOrdinaryOperator_eq_expanded]
  exact unrestrictedGeneratingSeries_three_differential

/-- A homogeneous third-order polynomial differential equation for the actual
four-letter unrestricted OGF.  This is an explicit D-finite certificate. -/
theorem unrestrictedGeneratingSeries_three_homogeneous_differential :
    let series := unrestrictedGeneratingSeries 3
    let derivativeOne := PowerSeries.derivative ℤ series
    let derivativeTwo := PowerSeries.derivative ℤ derivativeOne
    let derivativeThree := PowerSeries.derivative ℤ derivativeTwo
    (X ^ 2 - 16 * X ^ 4) * derivativeThree +
      (10 * X - 8 * X ^ 2 - 128 * X ^ 3) * derivativeTwo +
      (20 - 36 * X - 224 * X ^ 2) * derivativeOne +
      (-20 - 64 * X) * series = 0 := by
  let series := unrestrictedGeneratingSeries 3
  let derivativeOne := PowerSeries.derivative ℤ series
  let derivativeTwo := PowerSeries.derivative ℤ derivativeOne
  let derivativeThree := PowerSeries.derivative ℤ derivativeTwo
  have h := congrArg (PowerSeries.derivative ℤ)
    unrestrictedGeneratingSeries_three_expanded_differential
  simp only [heightFourOrdinaryExpandedOperator, map_zero, map_add, map_sub,
    Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_X,
    PowerSeries.derivative_pow, PowerSeries.derivative_C] at h
  dsimp only [series, derivativeOne, derivativeTwo, derivativeThree] at h ⊢
  norm_num at h
  linear_combination h

end FibonacciRibbonKernel
