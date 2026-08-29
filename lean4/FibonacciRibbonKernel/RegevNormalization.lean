import FibonacciRibbonKernel.RegevHookProduct
import FibonacciRibbonKernel.FixedRankAsymptotic

namespace FibonacciRibbonKernel

noncomputable def matsumotoBetaOneConstant
    (dimension : ℕ) (integral : ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(dimension - 1 : ℝ) / 2) *
    (dimension : ℝ) ^ ((dimension : ℝ) ^ 2 / 2) * integral

noncomputable def matsumotoBetaOneLeadingTerm
    (dimension index : ℕ) (integral : ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(dimension - 1 : ℝ) / 2) *
    (dimension : ℝ) ^ ((index : ℝ) + (dimension : ℝ) ^ 2 / 2) *
    (index : ℝ) ^
      (-((dimension - 1 : ℝ) * (dimension + 2 : ℝ)) / 4) *
    (index : ℝ) ^ ((dimension - 1 : ℝ) / 2) * integral

theorem matsumotoBetaOneLeadingTerm_eq_regev_shape
    (dimension index : ℕ) (integral : ℝ)
    (hdimension : 1 ≤ dimension) (hindex : 1 ≤ index) :
    matsumotoBetaOneLeadingTerm dimension index integral =
      matsumotoBetaOneConstant dimension integral *
        (dimension : ℝ) ^ index *
        (index : ℝ) ^ (-fixedRankExponent dimension) := by
  have hdimensionPos : (0 : ℝ) < dimension := by positivity
  have hindexPos : (0 : ℝ) < index := by positivity
  have hdimensionSub : ((dimension - 1 : ℕ) : ℝ) =
      (dimension : ℝ) - 1 := by
    exact_mod_cast Nat.cast_sub hdimension (R := ℝ)
  have hindexPower :
      (index : ℝ) ^
            (-((dimension - 1 : ℝ) * (dimension + 2 : ℝ)) / 4) *
          (index : ℝ) ^ ((dimension - 1 : ℝ) / 2) =
        (index : ℝ) ^ (-fixedRankExponent dimension) := by
    rw [← Real.rpow_add hindexPos]
    unfold fixedRankExponent
    rw [hdimensionSub]
    congr 1
    ring
  unfold matsumotoBetaOneLeadingTerm matsumotoBetaOneConstant
  rw [Real.rpow_add hdimensionPos]
  rw [Real.rpow_natCast]
  calc
    (2 * Real.pi) ^ (-(dimension - 1 : ℝ) / 2) *
          ((dimension : ℝ) ^ index *
            (dimension : ℝ) ^ ((dimension : ℝ) ^ 2 / 2)) *
          (index : ℝ) ^
            (-((dimension - 1 : ℝ) * (dimension + 2 : ℝ)) / 4) *
          (index : ℝ) ^ ((dimension - 1 : ℝ) / 2) * integral =
        (2 * Real.pi) ^ (-(dimension - 1 : ℝ) / 2) *
          (dimension : ℝ) ^ ((dimension : ℝ) ^ 2 / 2) * integral *
          (dimension : ℝ) ^ index *
          ((index : ℝ) ^
              (-((dimension - 1 : ℝ) * (dimension + 2 : ℝ)) / 4) *
            (index : ℝ) ^ ((dimension - 1 : ℝ) / 2)) := by ring
    _ = _ := by rw [hindexPower]

end FibonacciRibbonKernel
