import FibonacciRibbonKernel.SelbergAndersonFubini

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped Classical BigOperators

theorem selbergAndersonCoefficient_div_half
    (rank : ℕ) {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) :
    selbergAndersonCoefficient rank alpha beta /
        expectedDixonAndersonHalfIntegral (rank + 1) =
      Real.Gamma alpha * Real.Gamma beta *
        selbergHalfGammaStep (rank + 1) /
          (((rank + 2 : ℕ) : ℝ) *
            Real.Gamma (alpha + beta + ((rank + 1 : ℕ) : ℝ) / 2) *
            selbergHalfGammaStep 0) := by
  have hrank : 0 < (((rank + 2 : ℕ) : ℝ) / 2) := by positivity
  have hstep : selbergHalfGammaStep (rank + 1) =
      (((rank + 2 : ℕ) : ℝ) / 2) *
        Real.Gamma (((rank + 2 : ℕ) : ℝ) / 2) := by
    unfold selbergHalfGammaStep
    have hargument :
        1 + ((((rank + 1) + 1 : ℕ) : ℝ)) / 2 =
          (((rank + 2 : ℕ) : ℝ) / 2) + 1 := by
      push_cast
      ring
    rw [hargument, Real.Gamma_add_one hrank.ne']
  have hstepZero : selbergHalfGammaStep 0 =
      (1 / 2 : ℝ) * Real.Gamma (1 / 2) := by
    unfold selbergHalfGammaStep
    norm_num
    rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 by ring]
    rw [Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  have hgammaHalf : Real.Gamma (1 / 2 : ℝ) ≠ 0 := by positivity
  have hgammaRank :
      Real.Gamma (((rank + 2 : ℕ) : ℝ) / 2) ≠ 0 := by positivity
  have hgammaSum :
      Real.Gamma (alpha + beta + ((rank + 1 : ℕ) : ℝ) / 2) ≠ 0 := by
    positivity
  unfold selbergAndersonCoefficient
  unfold expectedDixonAndersonHalfIntegral
  rw [hstep, hstepZero]
  field_simp [hgammaHalf, hgammaRank, hgammaSum]
  ring

theorem orderedSelbergHalfEvaluation_all
    (dimension : ℕ) {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) :
    OrderedSelbergHalfEvaluation dimension alpha beta := by
  induction dimension generalizing alpha beta with
  | zero => exact orderedSelbergHalfEvaluation_zero alpha beta
  | succ dimension ih =>
      cases dimension with
      | zero => exact orderedSelbergHalfEvaluation_one halpha hbeta
      | succ rank =>
          have hshift := ih
            (alpha := alpha + 1 / 2) (beta := beta + 1 / 2)
            (by positivity) (by positivity)
          unfold OrderedSelbergHalfEvaluation at hshift ⊢
          have hintegrable := integrableOn_selbergHalfIntegrand_all
            (rank + 1) (alpha := alpha + 1 / 2)
              (beta := beta + 1 / 2) (by positivity) (by positivity)
          rw [orderedSelbergHalfIntegral_succ_recurrence
            rank halpha hbeta hintegrable]
          rw [selbergAndersonCoefficient_div_half rank halpha hbeta]
          rw [hshift]
          exact (expectedOrderedSelbergHalfIntegral_succ
            (rank + 1) halpha hbeta).symm

end FibonacciRibbonKernel
