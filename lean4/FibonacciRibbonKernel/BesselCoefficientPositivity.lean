import FibonacciRibbonKernel.BesselCoefficientStep

namespace FibonacciRibbonKernel

theorem besselM0CoeffAction_nonneg
    (degree : ℕ) (vector : Fin (degree + 1) → ℚ)
    (hvector : ∀ index, 0 ≤ vector index) (index : Fin (degree + 1)) :
    0 ≤ besselM0CoeffAction degree vector index := by
  unfold besselM0CoeffAction
  split_ifs with hpositive hbelow
  · have hindex : (index.val : ℚ) ≤ degree := by
      exact_mod_cast (Nat.le_of_lt_succ index.isLt)
    exact add_nonneg
      (mul_nonneg (by positivity) (hvector ⟨index.val - 1, by omega⟩))
      (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hindex))
        (hvector ⟨index.val + 1, by omega⟩))
  · simpa only [add_zero] using
      (mul_nonneg (by positivity)
        (hvector ⟨index.val - 1, by omega⟩))
  · have hindex : (index.val : ℚ) ≤ degree := by
      exact_mod_cast (Nat.le_of_lt_succ index.isLt)
    simpa only [zero_add] using
      (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hindex))
        (hvector ⟨index.val + 1, by omega⟩))
  · simp

theorem oddBesselM0CoeffAction_nonneg
    (degree : ℕ) (vector : Fin (degree + 1) → ℚ)
    (hvector : ∀ index, 0 ≤ vector index) (index : Fin (degree + 1)) :
    0 ≤ oddBesselM0CoeffAction degree vector index := by
  unfold oddBesselM0CoeffAction
  exact add_nonneg (hvector index)
    (besselM0CoeffAction_nonneg degree vector hvector index)

theorem besselFactorialCoeff_zero_eq_indicator
    (degree : ℕ) (index : Fin (degree + 1)) :
    besselFactorialCoeff degree 0 index =
      if index.val = degree then 1 else 0 := by
  by_cases htop : index.val = degree
  · simp [htop, besselFactorialCoeff, besselBasisVector, besselMonomial,
      besselJ0, besselJ1]
  · have hbelow : index.val < degree := by omega
    have hsub : degree - index.val ≠ 0 := by omega
    simp [htop, hsub, besselFactorialCoeff, besselBasisVector, besselMonomial,
      besselJ0, besselJ1]

theorem oddBesselFactorialCoeff_zero_eq_indicator
    (degree : ℕ) (index : Fin (degree + 1)) :
    oddBesselFactorialCoeff degree 0 index =
      if index.val = degree then 1 else 0 := by
  rw [oddBesselFactorialCoeff]
  simp only [Nat.factorial_zero, Nat.cast_one, one_mul]
  unfold oddBesselBasisVector
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
    PowerSeries.constantCoeff_exp, one_mul,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simpa [besselFactorialCoeff] using
    besselFactorialCoeff_zero_eq_indicator degree index

theorem besselFactorialCoeff_nonneg
    (degree coefficient : ℕ) (index : Fin (degree + 1)) :
    0 ≤ besselFactorialCoeff degree coefficient index := by
  induction coefficient generalizing index with
  | zero =>
      rw [besselFactorialCoeff_zero_eq_indicator]
      split_ifs <;> positivity
  | succ coefficient inductionHypothesis =>
      rw [besselFactorialCoeff_succ_step]
      exact mul_nonneg (besselCoefficientStepRatio_pos degree coefficient index).le
        (besselM0CoeffAction_nonneg degree
          (besselFactorialCoeff degree coefficient)
          inductionHypothesis index)

theorem oddBesselFactorialCoeff_nonneg
    (degree coefficient : ℕ) (index : Fin (degree + 1)) :
    0 ≤ oddBesselFactorialCoeff degree coefficient index := by
  induction coefficient generalizing index with
  | zero =>
      rw [oddBesselFactorialCoeff_zero_eq_indicator]
      split_ifs <;> positivity
  | succ coefficient inductionHypothesis =>
      rw [oddBesselFactorialCoeff_succ_step]
      exact mul_nonneg (besselCoefficientStepRatio_pos degree coefficient index).le
        (oddBesselM0CoeffAction_nonneg degree
          (oddBesselFactorialCoeff degree coefficient)
          inductionHypothesis index)

end FibonacciRibbonKernel
