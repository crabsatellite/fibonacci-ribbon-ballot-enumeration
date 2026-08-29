import FibonacciRibbonKernel.RegevMehtaJacobianIntegral

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped Classical

noncomputable def expectedStandardMehtaChamberIntegral (rank : ℕ) : ℝ :=
  Real.sqrt (2 * Real.pi) ^ (rank + 1) *
    mehtaGammaProduct (rank + 1) /
      ((rank + 1).factorial : ℝ)

def StandardMehtaChamberEvaluation (rank : ℕ) : Prop :=
  standardMehtaChamberIntegral (rank + 1) =
    expectedStandardMehtaChamberIntegral rank

theorem standardMehtaChamberIntegral_eq_centered (rank : ℕ) :
    standardMehtaChamberIntegral (rank + 1) =
      (((rank + 1 : ℕ) : ℝ)) * centeredMehtaChamberIntegral rank := by
  rw [← standardMehtaBlockChamberIntegral_eq]
  have hjacobian := mehtaBlockInputChamberIntegral_eq_standard rank
  rw [mehtaBlockInputChamberIntegral_eq_centered] at hjacobian
  rw [hjacobian]
  have hdimension : (((rank + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp

theorem standardMehtaChamberIntegral_eq_traceless (rank : ℕ) :
    standardMehtaChamberIntegral (rank + 1) =
      (((rank + 1 : ℕ) : ℝ)) *
        Real.sqrt (2 * Real.pi / ((rank + 1 : ℕ) : ℝ)) *
          tracelessMehtaChamberIntegral rank := by
  rw [standardMehtaChamberIntegral_eq_centered,
    centeredMehtaChamberIntegral_eq]
  ring

theorem expected_standard_center_factor (rank : ℕ) :
    (((rank + 1 : ℕ) : ℝ)) *
        Real.sqrt (2 * Real.pi / ((rank + 1 : ℕ) : ℝ)) *
          (Real.sqrt (2 * Real.pi) ^ (rank + 1) *
            expectedRegevChamberIntegral rank) =
      expectedStandardMehtaChamberIntegral rank := by
  rw [expectedRegevChamberIntegral_formula]
  unfold expectedStandardMehtaChamberIntegral
  rw [← Real.sqrt_eq_rpow]
  rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  have hdimension : (0 : ℝ) < ((rank + 1 : ℕ) : ℝ) := by positivity
  have hsqrtDimension : Real.sqrt (((rank + 1 : ℕ) : ℝ)) ≠ 0 := by
    positivity
  have hsqrtGaussian : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have hfactorial : ((rank + 1).factorial : ℝ) ≠ 0 := by positivity
  have hsquare : Real.sqrt (((rank + 1 : ℕ) : ℝ)) ^ 2 =
      ((rank + 1 : ℕ) : ℝ) := by
    rw [Real.sq_sqrt hdimension.le]
  field_simp [hsqrtDimension, hsqrtGaussian, hfactorial]
  rw [hsquare]

theorem RegevMehtaChamberEvaluation_iff_standard (rank : ℕ) :
    RegevMehtaChamberEvaluation rank ↔
      StandardMehtaChamberEvaluation rank := by
  rw [RegevMehtaChamberEvaluation_iff]
  unfold StandardMehtaChamberEvaluation
  rw [standardMehtaChamberIntegral_eq_traceless]
  let factor := (((rank + 1 : ℕ) : ℝ)) *
    Real.sqrt (2 * Real.pi / ((rank + 1 : ℕ) : ℝ))
  have hfactor : 0 < factor := by
    dsimp only [factor]
    positivity
  have hexpected := expected_standard_center_factor rank
  constructor <;> intro h
  · rw [h]
    exact hexpected
  · rw [← hexpected] at h
    exact mul_left_cancel₀ hfactor.ne' h

end FibonacciRibbonKernel
