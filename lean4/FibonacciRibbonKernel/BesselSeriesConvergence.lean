import FibonacciRibbonKernel.BesselCoefficientBounds
import Mathlib.Analysis.SpecificLimits.Normed

namespace FibonacciRibbonKernel

open Filter

noncomputable def besselOrdinaryEval
    (degree : ℕ) (index : Fin (degree + 1)) (x : ℝ) : ℝ :=
  ∑' coefficient : ℕ,
    (besselFactorialCoeff degree coefficient index : ℝ) * x ^ coefficient

noncomputable def oddBesselOrdinaryEval
    (degree : ℕ) (index : Fin (degree + 1)) (x : ℝ) : ℝ :=
  ∑' coefficient : ℕ,
    (oddBesselFactorialCoeff degree coefficient index : ℝ) * x ^ coefficient

theorem besselOrdinaryEval_summable_abs
    (degree : ℕ) (index : Fin (degree + 1)) (x : ℝ)
    (hx : (2 * degree : ℝ) * |x| < 1) :
    Summable (fun coefficient : ℕ =>
      |(besselFactorialCoeff degree coefficient index : ℝ) * x ^ coefficient|) := by
  have hgeometric : Summable (fun coefficient : ℕ =>
      ((2 * degree : ℝ) * |x|) ^ coefficient) :=
    summable_geometric_of_lt_one (mul_nonneg (by positivity) (abs_nonneg x)) hx
  refine Summable.of_nonneg_of_le (fun coefficient => abs_nonneg _) ?_ hgeometric
  intro coefficient
  have hcoefficientNonneg :
      (0 : ℝ) ≤ besselFactorialCoeff degree coefficient index := by
    exact_mod_cast besselFactorialCoeff_nonneg degree coefficient index
  have hcoefficientBound :
      (besselFactorialCoeff degree coefficient index : ℝ) ≤
        (2 * degree : ℝ) ^ coefficient := by
    exact_mod_cast besselFactorialCoeff_le_scale_pow degree coefficient index
  calc
    |(besselFactorialCoeff degree coefficient index : ℝ) * x ^ coefficient| =
        (besselFactorialCoeff degree coefficient index : ℝ) *
          |x| ^ coefficient := by
      rw [abs_mul, abs_pow, abs_of_nonneg hcoefficientNonneg]
    _ ≤ (2 * degree : ℝ) ^ coefficient * |x| ^ coefficient :=
      mul_le_mul_of_nonneg_right hcoefficientBound (by positivity)
    _ = ((2 * degree : ℝ) * |x|) ^ coefficient := by
      simp only [mul_pow]

theorem besselOrdinaryEval_summable
    (degree : ℕ) (index : Fin (degree + 1)) (x : ℝ)
    (hx : (2 * degree : ℝ) * |x| < 1) :
    Summable (fun coefficient : ℕ =>
      (besselFactorialCoeff degree coefficient index : ℝ) * x ^ coefficient) := by
  apply Summable.of_norm
  simpa only [Real.norm_eq_abs] using
    besselOrdinaryEval_summable_abs degree index x hx

theorem besselOrdinaryEval_hasSum
    (degree : ℕ) (index : Fin (degree + 1)) (x : ℝ)
    (hx : (2 * degree : ℝ) * |x| < 1) :
    HasSum (fun coefficient : ℕ =>
      (besselFactorialCoeff degree coefficient index : ℝ) * x ^ coefficient)
      (besselOrdinaryEval degree index x) :=
  (besselOrdinaryEval_summable degree index x hx).hasSum

theorem oddBesselOrdinaryEval_summable_abs
    (degree : ℕ) (index : Fin (degree + 1)) (x : ℝ)
    (hx : (2 * degree + 1 : ℝ) * |x| < 1) :
    Summable (fun coefficient : ℕ =>
      |(oddBesselFactorialCoeff degree coefficient index : ℝ) *
        x ^ coefficient|) := by
  have hgeometric : Summable (fun coefficient : ℕ =>
      ((2 * degree + 1 : ℝ) * |x|) ^ coefficient) :=
    summable_geometric_of_lt_one (mul_nonneg (by positivity) (abs_nonneg x)) hx
  refine Summable.of_nonneg_of_le (fun coefficient => abs_nonneg _) ?_ hgeometric
  intro coefficient
  have hcoefficientNonneg :
      (0 : ℝ) ≤ oddBesselFactorialCoeff degree coefficient index := by
    exact_mod_cast oddBesselFactorialCoeff_nonneg degree coefficient index
  have hcoefficientBound :
      (oddBesselFactorialCoeff degree coefficient index : ℝ) ≤
        (2 * degree + 1 : ℝ) ^ coefficient := by
    exact_mod_cast oddBesselFactorialCoeff_le_scale_pow degree coefficient index
  calc
    |(oddBesselFactorialCoeff degree coefficient index : ℝ) * x ^ coefficient| =
        (oddBesselFactorialCoeff degree coefficient index : ℝ) *
          |x| ^ coefficient := by
      rw [abs_mul, abs_pow, abs_of_nonneg hcoefficientNonneg]
    _ ≤ (2 * degree + 1 : ℝ) ^ coefficient * |x| ^ coefficient :=
      mul_le_mul_of_nonneg_right hcoefficientBound (by positivity)
    _ = ((2 * degree + 1 : ℝ) * |x|) ^ coefficient := by
      simp only [mul_pow]

theorem oddBesselOrdinaryEval_summable
    (degree : ℕ) (index : Fin (degree + 1)) (x : ℝ)
    (hx : (2 * degree + 1 : ℝ) * |x| < 1) :
    Summable (fun coefficient : ℕ =>
      (oddBesselFactorialCoeff degree coefficient index : ℝ) * x ^ coefficient) := by
  apply Summable.of_norm
  simpa only [Real.norm_eq_abs] using
    oddBesselOrdinaryEval_summable_abs degree index x hx

theorem oddBesselOrdinaryEval_hasSum
    (degree : ℕ) (index : Fin (degree + 1)) (x : ℝ)
    (hx : (2 * degree + 1 : ℝ) * |x| < 1) :
    HasSum (fun coefficient : ℕ =>
      (oddBesselFactorialCoeff degree coefficient index : ℝ) * x ^ coefficient)
      (oddBesselOrdinaryEval degree index x) :=
  (oddBesselOrdinaryEval_summable degree index x hx).hasSum

end FibonacciRibbonKernel
