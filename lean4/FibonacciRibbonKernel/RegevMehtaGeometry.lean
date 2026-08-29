import FibonacciRibbonKernel.RegevMehtaTarget

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped Classical

noncomputable def mehtaGammaProduct (dimension : ℕ) : ℝ :=
  ∏ j ∈ Finset.range dimension,
    Real.Gamma (1 + ((j + 1 : ℕ) : ℝ) / 2) /
      Real.Gamma (3 / 2)

theorem expectedRegevChamberIntegral_formula (rank : ℕ) :
    expectedRegevChamberIntegral rank =
      mehtaGammaProduct (rank + 1) /
        (((rank + 1).factorial : ℝ) * Real.sqrt (2 * Real.pi) *
          (((rank + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ))) := by
  unfold expectedRegevChamberIntegral regevIntegralScaleConstant
  unfold regevConstant
  change ((((rank + 1 : ℕ) : ℝ) ^ fixedRankExponent (rank + 1) /
      ((rank + 1).factorial : ℝ) * mehtaGammaProduct (rank + 1)) /
        (Real.sqrt (2 * Real.pi) *
          ((rank + 1 : ℕ) : ℝ) ^
            (fixedRankExponent (rank + 1) + 1 / 2))) =
    mehtaGammaProduct (rank + 1) /
      (((rank + 1).factorial : ℝ) * Real.sqrt (2 * Real.pi) *
        (((rank + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)))
  have hdimensionPos : (0 : ℝ) < rank + 1 := by positivity
  have hdimensionPower :
      ((rank : ℝ) + 1) ^ fixedRankExponent (rank + 1) /
          ((rank : ℝ) + 1) ^
            (fixedRankExponent (rank + 1) + 1 / 2) =
        (((rank : ℝ) + 1) ^ (1 / 2 : ℝ))⁻¹ := by
    rw [← Real.rpow_sub hdimensionPos]
    rw [show fixedRankExponent (rank + 1) -
        (fixedRankExponent (rank + 1) + 1 / 2) = -(1 / 2 : ℝ) by ring]
    rw [Real.rpow_neg hdimensionPos.le]
  push_cast
  rw [show (((rank : ℝ) + 1) ^ fixedRankExponent (rank + 1) /
        ((rank + 1).factorial : ℝ) * mehtaGammaProduct (rank + 1)) /
      (Real.sqrt (2 * Real.pi) *
        ((rank : ℝ) + 1) ^
          (fixedRankExponent (rank + 1) + 1 / 2)) =
    (mehtaGammaProduct (rank + 1) /
      ((rank + 1).factorial : ℝ) /
      Real.sqrt (2 * Real.pi)) *
      (((rank : ℝ) + 1) ^ fixedRankExponent (rank + 1) /
        ((rank : ℝ) + 1) ^
          (fixedRankExponent (rank + 1) + 1 / 2)) by ring]
  rw [hdimensionPower]
  have hfactorial : ((rank + 1).factorial : ℝ) ≠ 0 := by positivity
  have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have hdimensionHalf :
      (((rank : ℝ) + 1) ^ (1 / 2 : ℝ)) ≠ 0 :=
    (Real.rpow_pos_of_pos hdimensionPos _).ne'
  field_simp

noncomputable def tracelessMehtaChamberIntegral (rank : ℕ) : ℝ :=
  ∫ coordinates in regevChamber rank,
    regevGaussianKernel rank coordinates *
      regevVandermonde rank coordinates

theorem regevFullChamberIntegral_eq_prefactor_mul_mehta (rank : ℕ) :
    regevFullChamberIntegral rank =
      (1 / Real.sqrt (2 * Real.pi)) ^ (rank + 1) *
        tracelessMehtaChamberIntegral rank := by
  unfold regevFullChamberIntegral tracelessMehtaChamberIntegral
  unfold regevLocalIntegrand
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_congr_fun
    (regevChamber_isClosed rank).measurableSet
  intro coordinates hcoordinates
  ring

theorem RegevMehtaChamberEvaluation_iff (rank : ℕ) :
    RegevMehtaChamberEvaluation rank ↔
      tracelessMehtaChamberIntegral rank =
        (Real.sqrt (2 * Real.pi) ^ (rank + 1)) *
          expectedRegevChamberIntegral rank := by
  unfold RegevMehtaChamberEvaluation
  rw [regevFullChamberIntegral_eq_prefactor_mul_mehta]
  have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  rw [one_div, inv_pow]
  constructor <;> intro h
  · field_simp [pow_ne_zero (rank + 1) hsqrt] at h
    nlinarith
  · field_simp [pow_ne_zero (rank + 1) hsqrt]
    nlinarith

end FibonacciRibbonKernel
