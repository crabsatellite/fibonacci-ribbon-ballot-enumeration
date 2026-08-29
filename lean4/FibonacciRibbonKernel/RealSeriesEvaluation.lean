import FibonacciRibbonKernel.BesselIntegralHasSum
import Mathlib.Analysis.Normed.Ring.InfiniteSum

namespace FibonacciRibbonKernel

open PowerSeries

noncomputable def realPowerSeriesTerm
    (series : ℝ⟦X⟧) (parameter : ℝ) (power : ℕ) : ℝ :=
  PowerSeries.coeff power series * parameter ^ power

def RealPowerSeriesHasSum
    (series : ℝ⟦X⟧) (parameter value : ℝ) : Prop :=
  HasSum (realPowerSeriesTerm series parameter) value

theorem RealPowerSeriesHasSum.summable
    {series : ℝ⟦X⟧} {parameter value : ℝ}
    (h : RealPowerSeriesHasSum series parameter value) :
    Summable (realPowerSeriesTerm series parameter) :=
  HasSum.summable h

theorem RealPowerSeriesHasSum.norm_summable
    {series : ℝ⟦X⟧} {parameter value : ℝ}
    (h : RealPowerSeriesHasSum series parameter value) :
    Summable (fun power => ‖realPowerSeriesTerm series parameter power‖) :=
  (HasSum.summable h).norm

theorem realPowerSeriesTerm_add
    (left right : ℝ⟦X⟧) (parameter : ℝ) (power : ℕ) :
    realPowerSeriesTerm (left + right) parameter power =
      realPowerSeriesTerm left parameter power +
        realPowerSeriesTerm right parameter power := by
  unfold realPowerSeriesTerm
  rw [map_add]
  ring

theorem RealPowerSeriesHasSum.add
    {left right : ℝ⟦X⟧} {parameter leftValue rightValue : ℝ}
    (hleft : RealPowerSeriesHasSum left parameter leftValue)
    (hright : RealPowerSeriesHasSum right parameter rightValue) :
    RealPowerSeriesHasSum (left + right) parameter
      (leftValue + rightValue) := by
  unfold RealPowerSeriesHasSum at *
  rw [show realPowerSeriesTerm (left + right) parameter =
      fun power => realPowerSeriesTerm left parameter power +
        realPowerSeriesTerm right parameter power by
    funext power
    exact realPowerSeriesTerm_add left right parameter power]
  exact hleft.add hright

theorem RealPowerSeriesHasSum.neg
    {series : ℝ⟦X⟧} {parameter value : ℝ}
    (h : RealPowerSeriesHasSum series parameter value) :
    RealPowerSeriesHasSum (-series) parameter (-value) := by
  unfold RealPowerSeriesHasSum at *
  rw [show realPowerSeriesTerm (-series) parameter =
      fun power => -realPowerSeriesTerm series parameter power by
    funext power
    unfold realPowerSeriesTerm
    rw [map_neg]
    ring]
  exact h.neg

theorem RealPowerSeriesHasSum.sub
    {left right : ℝ⟦X⟧} {parameter leftValue rightValue : ℝ}
    (hleft : RealPowerSeriesHasSum left parameter leftValue)
    (hright : RealPowerSeriesHasSum right parameter rightValue) :
    RealPowerSeriesHasSum (left - right) parameter
      (leftValue - rightValue) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact hleft.add hright.neg

theorem realPowerSeriesTerm_mul_eq_cauchy
    (left right : ℝ⟦X⟧) (parameter : ℝ) (power : ℕ) :
    realPowerSeriesTerm (left * right) parameter power =
      ∑ index ∈ Finset.range (power + 1),
        realPowerSeriesTerm left parameter index *
          realPowerSeriesTerm right parameter (power - index) := by
  unfold realPowerSeriesTerm
  rw [PowerSeries.coeff_mul]
  rw [show (∑ pair ∈ Finset.HasAntidiagonal.antidiagonal power,
      PowerSeries.coeff pair.1 left * PowerSeries.coeff pair.2 right) =
    ∑ index ∈ Finset.range (power + 1),
      PowerSeries.coeff index left *
        PowerSeries.coeff (power - index) right by
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun leftIndex rightIndex =>
        PowerSeries.coeff leftIndex left *
          PowerSeries.coeff rightIndex right) power]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro index hindex
  have hle : index ≤ power := by
    rw [Finset.mem_range] at hindex
    omega
  have hpow : parameter ^ power =
      parameter ^ index * parameter ^ (power - index) := by
    rw [← pow_add, Nat.add_sub_of_le hle]
  rw [hpow]
  ring

theorem RealPowerSeriesHasSum.mul
    {left right : ℝ⟦X⟧} {parameter leftValue rightValue : ℝ}
    (hleft : RealPowerSeriesHasSum left parameter leftValue)
    (hright : RealPowerSeriesHasSum right parameter rightValue) :
    RealPowerSeriesHasSum (left * right) parameter
      (leftValue * rightValue) := by
  unfold RealPowerSeriesHasSum at *
  have hleftNorm := (HasSum.summable hleft).norm
  have hrightNorm := (HasSum.summable hright).norm
  have hcauchy := hasSum_sum_range_mul_of_summable_norm
    hleftNorm hrightNorm
  rw [show realPowerSeriesTerm (left * right) parameter =
      fun power => ∑ index ∈ Finset.range (power + 1),
        realPowerSeriesTerm left parameter index *
          realPowerSeriesTerm right parameter (power - index) by
    funext power
    exact realPowerSeriesTerm_mul_eq_cauchy left right parameter power]
  rw [hleft.tsum_eq, hright.tsum_eq] at hcauchy
  exact hcauchy

theorem RealPowerSeriesHasSum.pow
    {series : ℝ⟦X⟧} {parameter value : ℝ}
    (h : RealPowerSeriesHasSum series parameter value)
    (power : ℕ) :
    RealPowerSeriesHasSum (series ^ power) parameter (value ^ power) := by
  induction power with
  | zero =>
      rw [pow_zero, pow_zero]
      unfold RealPowerSeriesHasSum realPowerSeriesTerm
      rw [show (fun power : ℕ =>
          PowerSeries.coeff power (1 : ℝ⟦X⟧) * parameter ^ power) =
        fun power => if power = 0 then (1 : ℝ) else 0 by
          funext power
          by_cases hpower : power = 0
          · subst power
            simp
          · simp [PowerSeries.coeff_one, hpower]]
      exact hasSum_ite_eq 0 1
  | succ power inductionHypothesis =>
      rw [pow_succ, pow_succ]
      exact inductionHypothesis.mul h

end FibonacciRibbonKernel
