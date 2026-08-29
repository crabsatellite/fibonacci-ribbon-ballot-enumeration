import FibonacciRibbonKernel.OddKernelDomination

namespace FibonacciRibbonKernel

open scoped BigOperators

theorem scaled_one_sub_cos_le_sq_div_two
    (index : ℕ) (value : ℝ) :
    (index + 1 : ℝ) *
        (1 - Real.cos (value / Real.sqrt (index + 1 : ℝ))) ≤
      value ^ 2 / 2 := by
  have hcos := Real.one_sub_sq_div_two_le_cos
    (x := value / Real.sqrt (index + 1 : ℝ))
  have hnonneg : (0 : ℝ) ≤ index + 1 := by positivity
  have hmul := mul_le_mul_of_nonneg_left
    (show 1 - Real.cos (value / Real.sqrt (index + 1 : ℝ)) ≤
      (value / Real.sqrt (index + 1 : ℝ)) ^ 2 / 2 by linarith)
    hnonneg
  have hsqrt : Real.sqrt (index + 1 : ℝ) ^ 2 = index + 1 :=
    Real.sq_sqrt (by positivity)
  field_simp [show Real.sqrt (index + 1 : ℝ) ≠ 0 by positivity] at hmul ⊢
  nlinarith

theorem scaled_oddCoordinateWeight_le_sq
    (index : ℕ) (value : ℝ) :
    ((index + 1 : ℝ) *
        (1 - Real.cos (value / Real.sqrt (index + 1 : ℝ)))) *
      (1 + Real.cos (value / Real.sqrt (index + 1 : ℝ))) ≤
        value ^ 2 := by
  have hminus := scaled_one_sub_cos_le_sq_div_two index value
  have hminusNonneg : 0 ≤ (index + 1 : ℝ) *
      (1 - Real.cos (value / Real.sqrt (index + 1 : ℝ))) := by
    exact mul_nonneg (by positivity) (sub_nonneg.2 (Real.cos_le_one _))
  have hplusNonneg : 0 ≤
      1 + Real.cos (value / Real.sqrt (index + 1 : ℝ)) := by
    linarith [Real.neg_one_le_cos
      (value / Real.sqrt (index + 1 : ℝ))]
  have hplusLe : 1 + Real.cos
      (value / Real.sqrt (index + 1 : ℝ)) ≤ 2 := by
    linarith [Real.cos_le_one
      (value / Real.sqrt (index + 1 : ℝ))]
  nlinarith

theorem abs_scaled_cosine_difference_le
    (index : ℕ) (left right : ℝ) :
    |(index + 1 : ℝ) *
      (Real.cos (left / Real.sqrt (index + 1 : ℝ)) -
        Real.cos (right / Real.sqrt (index + 1 : ℝ)))| ≤
      (left ^ 2 + right ^ 2) / 2 := by
  have hleft := scaled_one_sub_cos_le_sq_div_two index left
  have hright := scaled_one_sub_cos_le_sq_div_two index right
  have hleftNonneg : 0 ≤ (index + 1 : ℝ) *
      (1 - Real.cos (left / Real.sqrt (index + 1 : ℝ))) := by
    exact mul_nonneg (by positivity) (sub_nonneg.2 (Real.cos_le_one _))
  have hrightNonneg : 0 ≤ (index + 1 : ℝ) *
      (1 - Real.cos (right / Real.sqrt (index + 1 : ℝ))) := by
    exact mul_nonneg (by positivity) (sub_nonneg.2 (Real.cos_le_one _))
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < index + 1)]
  calc
    (index + 1 : ℝ) *
        |Real.cos (left / Real.sqrt (index + 1 : ℝ)) -
          Real.cos (right / Real.sqrt (index + 1 : ℝ))| ≤
      (index + 1 : ℝ) *
        ((1 - Real.cos (left / Real.sqrt (index + 1 : ℝ))) +
          (1 - Real.cos (right / Real.sqrt (index + 1 : ℝ)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [show Real.cos (left / Real.sqrt (index + 1 : ℝ)) -
            Real.cos (right / Real.sqrt (index + 1 : ℝ)) =
          (Real.cos (left / Real.sqrt (index + 1 : ℝ)) - 1) -
            (Real.cos (right / Real.sqrt (index + 1 : ℝ)) - 1) by ring]
        calc
          |_ - _| ≤ |Real.cos (left / Real.sqrt (index + 1 : ℝ)) - 1| +
              |Real.cos (right / Real.sqrt (index + 1 : ℝ)) - 1| :=
            abs_sub _ _
          _ = _ := by
            rw [abs_of_nonpos (sub_nonpos.2 (Real.cos_le_one _)),
              abs_of_nonpos (sub_nonpos.2 (Real.cos_le_one _))]
            ring
    _ ≤ (left ^ 2 + right ^ 2) / 2 := by
      calc
        (index + 1 : ℝ) *
            ((1 - Real.cos (left / Real.sqrt (index + 1 : ℝ))) +
              (1 - Real.cos (right / Real.sqrt (index + 1 : ℝ)))) =
          (index + 1 : ℝ) *
              (1 - Real.cos (left / Real.sqrt (index + 1 : ℝ))) +
            (index + 1 : ℝ) *
              (1 - Real.cos (right / Real.sqrt (index + 1 : ℝ))) := by ring
        _ ≤ left ^ 2 / 2 + right ^ 2 / 2 := add_le_add hleft hright
        _ = _ := by ring

noncomputable def rankFiveWeylPolynomial
    (coordinates : Fin 2 → ℝ) : ℝ :=
  ((coordinates 0 ^ 2 + coordinates 1 ^ 2) / 2) ^ 2 *
    coordinates 0 ^ 2 * coordinates 1 ^ 2

theorem scaledCosineVandermondeWeight_two
    (index : ℕ) (coordinates : Fin 2 → ℝ) :
    scaledCosineVandermondeWeight 2 index coordinates =
      ((index + 1 : ℝ) *
        (Real.cos (coordinates 1 / Real.sqrt (index + 1 : ℝ)) -
          Real.cos (coordinates 0 / Real.sqrt (index + 1 : ℝ)))) ^ 2 := by
  unfold scaledCosineVandermondeWeight
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
  rw [Finset.prod_insert (by decide : (0 : Fin 2) ∉ ({1} : Finset (Fin 2))),
    Finset.prod_singleton]
  have hzero : Finset.Iio (0 : Fin 2) = ∅ := by decide
  have hone : Finset.Iio (1 : Fin 2) = {0} := by decide
  rw [hzero, hone]
  simp

set_option maxHeartbeats 500000 in
theorem oddScaledWeylWeight_two_le_polynomial
    (index : ℕ) (coordinates : Fin 2 → ℝ) :
    oddScaledWeylWeight 2 index coordinates ≤
      rankFiveWeylPolynomial coordinates := by
  unfold oddScaledWeylWeight rankFiveWeylPolynomial
  rw [scaledCosineVandermondeWeight_two]
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
  rw [Finset.prod_insert (by decide : (0 : Fin 2) ∉ ({1} : Finset (Fin 2))),
    Finset.prod_singleton]
  have hdiff := abs_scaled_cosine_difference_le index
    (coordinates 1) (coordinates 0)
  have hdiffSq := sq_le_sq₀ (abs_nonneg _) (by positivity) |>.2 hdiff
  rw [sq_abs] at hdiffSq
  have hzero := scaled_oddCoordinateWeight_le_sq index (coordinates 0)
  have hone := scaled_oddCoordinateWeight_le_sq index (coordinates 1)
  have hzeroNonneg : 0 ≤ ((index + 1 : ℝ) *
        (1 - Real.cos (coordinates 0 / Real.sqrt (index + 1 : ℝ)))) *
      (1 + Real.cos (coordinates 0 / Real.sqrt (index + 1 : ℝ))) := by
    have hplus : 0 ≤ 1 + Real.cos
        (coordinates 0 / Real.sqrt (index + 1 : ℝ)) := by
      have hlower := Real.neg_one_le_cos
        (coordinates 0 / Real.sqrt (index + 1 : ℝ))
      linarith
    exact mul_nonneg
      (mul_nonneg (by positivity) (sub_nonneg.2 (Real.cos_le_one _)))
      hplus
  have honeNonneg : 0 ≤ ((index + 1 : ℝ) *
        (1 - Real.cos (coordinates 1 / Real.sqrt (index + 1 : ℝ)))) *
      (1 + Real.cos (coordinates 1 / Real.sqrt (index + 1 : ℝ))) := by
    have hplus : 0 ≤ 1 + Real.cos
        (coordinates 1 / Real.sqrt (index + 1 : ℝ)) := by
      have hlower := Real.neg_one_le_cos
        (coordinates 1 / Real.sqrt (index + 1 : ℝ))
      linarith
    exact mul_nonneg
      (mul_nonneg (by positivity) (sub_nonneg.2 (Real.cos_le_one _)))
      hplus
  have hpolyNonneg : 0 ≤
      ((coordinates 1 ^ 2 + coordinates 0 ^ 2) / 2) ^ 2 := by positivity
  have hcoordinateProduct := mul_le_mul hzero hone honeNonneg
    (sq_nonneg (coordinates 0))
  have hcombined := mul_le_mul hdiffSq hcoordinateProduct
    (mul_nonneg hzeroNonneg honeNonneg) hpolyNonneg
  have hsumEq :
      ((coordinates 1 ^ 2 + coordinates 0 ^ 2) / 2) ^ 2 =
        ((coordinates 0 ^ 2 + coordinates 1 ^ 2) / 2) ^ 2 := by ring
  rw [hsumEq] at hcombined
  simpa [mul_assoc, mul_comm, mul_left_comm] using hcombined

theorem rankFiveWeylPolynomial_nonneg (coordinates : Fin 2 → ℝ) :
    0 ≤ rankFiveWeylPolynomial coordinates := by
  unfold rankFiveWeylPolynomial
  positivity

end FibonacciRibbonKernel
