import FibonacciRibbonKernel.BesselCoefficientPositivity

namespace FibonacciRibbonKernel

theorem besselM0CoeffAction_le_uniform
    (degree : ℕ) (vector : Fin (degree + 1) → ℚ) (bound : ℚ)
    (hboundNonneg : 0 ≤ bound) (hbound : ∀ index, vector index ≤ bound)
    (index : Fin (degree + 1)) :
    besselM0CoeffAction degree vector index ≤ (2 * degree : ℚ) * bound := by
  unfold besselM0CoeffAction
  split_ifs with hpositive hbelow
  · have hindex : (index.val : ℚ) ≤ degree := by
      exact_mod_cast (Nat.le_of_lt_succ index.isLt)
    have hleftWeight : (0 : ℚ) ≤ 2 * index.val := by positivity
    have hrightWeight : (0 : ℚ) ≤ 2 * ((degree : ℚ) - index.val) :=
      mul_nonneg (by norm_num) (sub_nonneg.mpr hindex)
    calc
      (2 * index.val : ℚ) * vector ⟨index.val - 1, by omega⟩ +
          2 * ((degree : ℚ) - index.val) *
            vector ⟨index.val + 1, by omega⟩ ≤
        (2 * index.val : ℚ) * bound +
          2 * ((degree : ℚ) - index.val) * bound :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hbound _) hleftWeight)
          (mul_le_mul_of_nonneg_left (hbound _) hrightWeight)
      _ = (2 * degree : ℚ) * bound := by ring
  · have hindex : (index.val : ℚ) ≤ degree := by
      exact_mod_cast (Nat.le_of_lt_succ index.isLt)
    have hweight : (2 * index.val : ℚ) ≤ 2 * degree := by linarith
    simpa only [add_zero] using
      (mul_le_mul_of_nonneg_left (hbound ⟨index.val - 1, by omega⟩)
          (by positivity)).trans
        (mul_le_mul_of_nonneg_right hweight hboundNonneg)
  · have hindex : (index.val : ℚ) ≤ degree := by
      exact_mod_cast (Nat.le_of_lt_succ index.isLt)
    have hweightNonneg : (0 : ℚ) ≤ 2 * ((degree : ℚ) - index.val) :=
      mul_nonneg (by norm_num) (sub_nonneg.mpr hindex)
    have hweight :
        (2 * ((degree : ℚ) - index.val) : ℚ) ≤ 2 * degree := by
      have hindexNonneg : (0 : ℚ) ≤ index.val := by positivity
      linarith
    simpa only [zero_add] using
      (mul_le_mul_of_nonneg_left (hbound ⟨index.val + 1, by omega⟩)
          hweightNonneg).trans
        (mul_le_mul_of_nonneg_right hweight hboundNonneg)
  · have hright : (0 : ℚ) ≤ (2 * degree : ℚ) * bound :=
      mul_nonneg (by positivity) hboundNonneg
    simpa only [zero_add] using hright

theorem oddBesselM0CoeffAction_le_uniform
    (degree : ℕ) (vector : Fin (degree + 1) → ℚ) (bound : ℚ)
    (hboundNonneg : 0 ≤ bound) (hbound : ∀ index, vector index ≤ bound)
    (index : Fin (degree + 1)) :
    oddBesselM0CoeffAction degree vector index ≤
      (2 * degree + 1 : ℚ) * bound := by
  unfold oddBesselM0CoeffAction
  calc
    vector index + besselM0CoeffAction degree vector index ≤
        bound + (2 * degree : ℚ) * bound :=
      add_le_add (hbound index)
        (besselM0CoeffAction_le_uniform degree vector bound
          hboundNonneg hbound index)
    _ = (2 * degree + 1 : ℚ) * bound := by ring

theorem besselFactorialCoeff_le_scale_pow
    (degree coefficient : ℕ) (index : Fin (degree + 1)) :
    besselFactorialCoeff degree coefficient index ≤
      (2 * degree : ℚ) ^ coefficient := by
  induction coefficient generalizing index with
  | zero =>
      rw [besselFactorialCoeff_zero_eq_indicator]
      split_ifs <;> simp
  | succ coefficient inductionHypothesis =>
      rw [besselFactorialCoeff_succ_step]
      have hactionNonneg := besselM0CoeffAction_nonneg degree
        (besselFactorialCoeff degree coefficient)
        (besselFactorialCoeff_nonneg degree coefficient) index
      calc
        besselCoefficientStepRatio degree coefficient index *
            besselM0CoeffAction degree
              (besselFactorialCoeff degree coefficient) index ≤
          besselM0CoeffAction degree
              (besselFactorialCoeff degree coefficient) index := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right
                (besselCoefficientStepRatio_le_one degree coefficient index)
                hactionNonneg
        _ ≤ (2 * degree : ℚ) * (2 * degree : ℚ) ^ coefficient :=
          besselM0CoeffAction_le_uniform degree
            (besselFactorialCoeff degree coefficient)
            ((2 * degree : ℚ) ^ coefficient) (by positivity)
            inductionHypothesis index
        _ = (2 * degree : ℚ) ^ (coefficient + 1) := by
          rw [pow_succ']

theorem oddBesselFactorialCoeff_le_scale_pow
    (degree coefficient : ℕ) (index : Fin (degree + 1)) :
    oddBesselFactorialCoeff degree coefficient index ≤
      (2 * degree + 1 : ℚ) ^ coefficient := by
  induction coefficient generalizing index with
  | zero =>
      rw [oddBesselFactorialCoeff_zero_eq_indicator]
      split_ifs <;> simp
  | succ coefficient inductionHypothesis =>
      rw [oddBesselFactorialCoeff_succ_step]
      have hactionNonneg := oddBesselM0CoeffAction_nonneg degree
        (oddBesselFactorialCoeff degree coefficient)
        (oddBesselFactorialCoeff_nonneg degree coefficient) index
      calc
        besselCoefficientStepRatio degree coefficient index *
            oddBesselM0CoeffAction degree
              (oddBesselFactorialCoeff degree coefficient) index ≤
          oddBesselM0CoeffAction degree
              (oddBesselFactorialCoeff degree coefficient) index := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right
                (besselCoefficientStepRatio_le_one degree coefficient index)
                hactionNonneg
        _ ≤ (2 * degree + 1 : ℚ) *
            (2 * degree + 1 : ℚ) ^ coefficient :=
          oddBesselM0CoeffAction_le_uniform degree
            (oddBesselFactorialCoeff degree coefficient)
            ((2 * degree + 1 : ℚ) ^ coefficient) (by positivity)
            inductionHypothesis index
        _ = (2 * degree + 1 : ℚ) ^ (coefficient + 1) := by
          rw [pow_succ']

end FibonacciRibbonKernel
