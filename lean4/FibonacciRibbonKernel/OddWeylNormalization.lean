import FibonacciRibbonKernel.AndreiefIdentity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

namespace FibonacciRibbonKernel

open MeasureTheory
open scoped BigOperators

noncomputable def oddAndreiefBasis
    {dimension : ℕ} (index : Fin dimension) (angle : ℝ) : ℝ :=
  2 * Real.sin ((index.val + 1 : ℕ) * angle)

theorem continuous_oddAndreiefBasis
    {dimension : ℕ} (index : Fin dimension) :
    Continuous (oddAndreiefBasis index) := by
  unfold oddAndreiefBasis
  fun_prop

theorem andreiefEvaluationMatrix_oddBasis
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    andreiefEvaluationMatrix oddAndreiefBasis angles =
      oddTrigEvaluationMatrix dimension angles := by
  rfl

theorem integral_cos_nat_mul
    (frequency : ℕ) :
    (∫ angle in (0 : ℝ)..Real.pi,
      Real.cos ((frequency : ℝ) * angle)) =
      if frequency = 0 then Real.pi else 0 := by
  by_cases hzero : frequency = 0
  · subst frequency
    simp
  · rw [if_neg hzero]
    have h :=
      Polynomial.Chebyshev.integral_eval_T_real_measureT_of_ne_zero
        (n := (frequency : ℤ)) (by exact_mod_cast hzero)
    rw [Polynomial.Chebyshev.integral_measureT_eq_integral_cos] at h
    simp_rw [Polynomial.Chebyshev.T_real_cos] at h
    convert h using 1
    norm_num

theorem two_mul_sin_mul_sin
    (left right angle : ℝ) :
    2 * Real.sin (left * angle) * Real.sin (right * angle) =
      Real.cos ((left - right) * angle) -
        Real.cos ((left + right) * angle) := by
  rw [Real.two_mul_sin_mul_sin]
  ring

theorem integral_sin_nat_mul_sin_nat_mul
    (left right : ℕ) (hleft : 0 < left) (hright : 0 < right) :
    (∫ angle in (0 : ℝ)..Real.pi,
      Real.sin ((left : ℝ) * angle) *
        Real.sin ((right : ℝ) * angle)) =
      if left = right then Real.pi / 2 else 0 := by
  have hproduct :
      (fun angle : ℝ =>
        2 * Real.sin ((left : ℝ) * angle) *
          Real.sin ((right : ℝ) * angle)) =
      fun angle =>
        Real.cos (((left : ℝ) - right) * angle) -
          Real.cos (((left : ℝ) + right) * angle) := by
    funext angle
    exact two_mul_sin_mul_sin left right angle
  have hscale :
      (∫ angle in (0 : ℝ)..Real.pi,
        2 * Real.sin ((left : ℝ) * angle) *
          Real.sin ((right : ℝ) * angle)) =
      2 * (∫ angle in (0 : ℝ)..Real.pi,
        Real.sin ((left : ℝ) * angle) *
          Real.sin ((right : ℝ) * angle)) := by
    rw [show (fun angle : ℝ =>
        2 * Real.sin ((left : ℝ) * angle) *
          Real.sin ((right : ℝ) * angle)) =
      fun angle => 2 *
        (Real.sin ((left : ℝ) * angle) *
          Real.sin ((right : ℝ) * angle)) by
      funext angle
      ring]
    rw [intervalIntegral.integral_const_mul]
  by_cases heq : left = right
  · subst right
    rw [if_pos rfl]
    have hsum : left + left ≠ 0 := by omega
    have hcos := integral_cos_nat_mul (left + left)
    rw [if_neg hsum] at hcos
    have hrewrite :
        (fun angle : ℝ =>
          Real.cos (((left : ℝ) - left) * angle) -
            Real.cos (((left : ℝ) + left) * angle)) =
        fun angle => 1 - Real.cos (((left + left : ℕ) : ℝ) * angle) := by
      funext angle
      push_cast
      simp
    have hdouble := congrArg (fun value : ℝ => value / 2)
      (show (∫ angle in (0 : ℝ)..Real.pi,
          2 * Real.sin ((left : ℝ) * angle) *
            Real.sin ((left : ℝ) * angle)) = Real.pi by
        rw [hproduct, hrewrite, intervalIntegral.integral_sub]
        · rw [hcos]
          simp
        · exact Continuous.intervalIntegrable (μ := volume)
            (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))
            0 Real.pi
        · exact Continuous.intervalIntegrable (μ := volume)
            (by fun_prop : Continuous (fun angle : ℝ =>
              Real.cos (((left + left : ℕ) : ℝ) * angle)))
            0 Real.pi)
    rw [hscale] at hdouble
    linarith
  · rw [if_neg heq]
    have hdiff : Int.natAbs ((left : ℤ) - right) ≠ 0 := by
      rw [Int.natAbs_ne_zero]
      exact sub_ne_zero.mpr (by exact_mod_cast heq)
    have hsum : left + right ≠ 0 := by omega
    have hcosDiff := integral_cos_nat_mul
      (Int.natAbs ((left : ℤ) - right))
    rw [if_neg hdiff] at hcosDiff
    have hcosSum := integral_cos_nat_mul (left + right)
    rw [if_neg hsum] at hcosSum
    have hdiffIntegral :
        (∫ angle in (0 : ℝ)..Real.pi,
          Real.cos (((left : ℝ) - right) * angle)) = 0 := by
      calc
        (∫ angle in (0 : ℝ)..Real.pi,
            Real.cos (((left : ℝ) - right) * angle)) =
          ∫ angle in (0 : ℝ)..Real.pi,
            Real.cos (((Int.natAbs ((left : ℤ) - right) : ℕ) : ℝ) * angle) := by
              apply intervalIntegral.integral_congr
              intro angle _hangle
              rcases le_total left right with hle | hle
              · rw [Int.natAbs_natCast_sub_natCast_of_le hle]
                have harg : ((left : ℝ) - right) * angle =
                    -(((right - left : ℕ) : ℝ) * angle) := by
                  rw [Nat.cast_sub hle]
                  ring
                change Real.cos (((left : ℝ) - right) * angle) =
                  Real.cos (((right - left : ℕ) : ℝ) * angle)
                rw [harg, Real.cos_neg]
              · rw [Int.natAbs_natCast_sub_natCast_of_ge hle,
                  Nat.cast_sub hle]
        _ = 0 := hcosDiff
    have hsumIntegral :
        (∫ angle in (0 : ℝ)..Real.pi,
          Real.cos (((left : ℝ) + right) * angle)) = 0 := by
      simpa only [Nat.cast_add] using hcosSum
    have hdouble := congrArg (fun value : ℝ => value / 2)
      (show (∫ angle in (0 : ℝ)..Real.pi,
          2 * Real.sin ((left : ℝ) * angle) *
            Real.sin ((right : ℝ) * angle)) = 0 by
        rw [hproduct, intervalIntegral.integral_sub]
        · rw [hdiffIntegral, hsumIntegral, sub_zero]
        · exact Continuous.intervalIntegrable (μ := volume)
            (by fun_prop : Continuous (fun angle : ℝ =>
              Real.cos (((left : ℝ) - right) * angle))) 0 Real.pi
        · exact Continuous.intervalIntegrable (μ := volume)
            (by fun_prop : Continuous (fun angle : ℝ =>
              Real.cos (((left : ℝ) + right) * angle))) 0 Real.pi)
    rw [hscale] at hdouble
    linarith

theorem andreiefMomentMatrix_oddBasis
    {dimension : ℕ} (row column : Fin dimension) :
    andreiefMomentMatrix oddAndreiefBasis row column =
      if row = column then 2 * Real.pi else 0 := by
  unfold andreiefMomentMatrix oddAndreiefBasis
  rw [integral_cosineIntervalMeasure_eq_interval]
  have h := integral_sin_nat_mul_sin_nat_mul
    (row.val + 1) (column.val + 1) (by omega) (by omega)
  by_cases heq : row = column
  · subst column
    rw [if_pos rfl] at h
    rw [if_pos rfl]
    rw [show (fun angle : ℝ =>
        2 * Real.sin ((row.val + 1 : ℕ) * angle) *
          (2 * Real.sin ((row.val + 1 : ℕ) * angle))) =
      fun angle => 4 *
        (Real.sin ((row.val + 1 : ℕ) * angle) *
          Real.sin ((row.val + 1 : ℕ) * angle)) by
      funext angle
      ring]
    rw [intervalIntegral.integral_const_mul, h]
    ring
  · have hval : row.val + 1 ≠ column.val + 1 := by
      intro hval
      apply heq
      exact Fin.ext (by omega)
    rw [if_neg hval] at h
    rw [if_neg heq]
    rw [show (fun angle : ℝ =>
        2 * Real.sin ((row.val + 1 : ℕ) * angle) *
          (2 * Real.sin ((column.val + 1 : ℕ) * angle))) =
      fun angle => 4 *
        (Real.sin ((row.val + 1 : ℕ) * angle) *
          Real.sin ((column.val + 1 : ℕ) * angle)) by
      funext angle
      ring]
    rw [intervalIntegral.integral_const_mul, h, mul_zero]

theorem det_andreiefMomentMatrix_oddBasis (dimension : ℕ) :
    (andreiefMomentMatrix
      (oddAndreiefBasis (dimension := dimension))).det =
      (2 * Real.pi) ^ dimension := by
  have hmatrix : andreiefMomentMatrix
      (oddAndreiefBasis (dimension := dimension)) =
      Matrix.diagonal fun _ : Fin dimension => 2 * Real.pi := by
    ext row column
    rw [andreiefMomentMatrix_oddBasis]
    by_cases heq : row = column
    · subst column
      simp
    · simp [heq]
  rw [hmatrix, Matrix.det_diagonal]
  simp

theorem integral_oddWeylAngleWeight
    (dimension : ℕ) :
    (∫ angles : Fin dimension → ℝ,
      oddWeylAngleWeight dimension angles
      ∂cosineCubeProductMeasure dimension) =
      (dimension.factorial : ℝ) * (2 * Real.pi) ^ dimension /
        (2 : ℝ) ^ (dimension * (dimension + 1)) := by
  have handreief := andreief_identity
    (oddAndreiefBasis (dimension := dimension))
    (fun index => continuous_oddAndreiefBasis index)
  rw [show (fun angles : Fin dimension → ℝ =>
      (andreiefEvaluationMatrix oddAndreiefBasis angles).det ^ 2) =
      fun angles =>
        (2 : ℝ) ^ (dimension * (dimension + 1)) *
          oddWeylAngleWeight dimension angles by
    funext angles
    rw [andreiefEvaluationMatrix_oddBasis,
      det_oddTrigEvaluationMatrix_sq,
      oddWeylAngleWeightIoi_eq]] at handreief
  rw [integral_const_mul,
    det_andreiefMomentMatrix_oddBasis] at handreief
  have htwo : (2 : ℝ) ^ (dimension * (dimension + 1)) ≠ 0 := by positivity
  field_simp
  nlinarith

end FibonacciRibbonKernel
