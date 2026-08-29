import FibonacciRibbonKernel.SelbergHalfBase

namespace FibonacciRibbonKernel

open scoped Classical

noncomputable def selbergHalfGammaStep (index : ℕ) : ℝ :=
  Real.Gamma (1 + ((index + 1 : ℕ) : ℝ) / 2)

theorem selbergHalfGammaStep_ne_zero (index : ℕ) :
    selbergHalfGammaStep index ≠ 0 := by
  unfold selbergHalfGammaStep
  positivity

theorem selbergHalfGammaStep_telescope (dimension : ℕ) :
    (∏ j ∈ Finset.range dimension,
      selbergHalfGammaStep (j + 1) / selbergHalfGammaStep j) =
        selbergHalfGammaStep dimension / selbergHalfGammaStep 0 := by
  induction dimension with
  | zero => simp [selbergHalfGammaStep_ne_zero]
  | succ dimension ih =>
      rw [Finset.prod_range_succ, ih]
      field_simp [selbergHalfGammaStep_ne_zero]

theorem selbergHalfGammaProduct_succ
    (dimension : ℕ) {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) :
    selbergHalfGammaProduct (dimension + 1) alpha beta =
      (Real.Gamma alpha * Real.Gamma beta /
        Real.Gamma (alpha + beta + (dimension : ℝ) / 2)) *
      (selbergHalfGammaStep dimension / selbergHalfGammaStep 0) *
      selbergHalfGammaProduct dimension
        (alpha + 1 / 2) (beta + 1 / 2) := by
  let shiftedTerm : ℕ → ℝ := fun j =>
    (Real.Gamma ((alpha + 1 / 2) + (j : ℝ) / 2) *
      Real.Gamma ((beta + 1 / 2) + (j : ℝ) / 2) *
      selbergHalfGammaStep j) /
        (Real.Gamma
          ((alpha + 1 / 2) + (beta + 1 / 2) +
            ((dimension + j - 1 : ℕ) : ℝ) / 2) *
          Real.Gamma (3 / 2))
  let originalTailTerm : ℕ → ℝ := fun j =>
    (Real.Gamma (alpha + ((j + 1 : ℕ) : ℝ) / 2) *
      Real.Gamma (beta + ((j + 1 : ℕ) : ℝ) / 2) *
      selbergHalfGammaStep (j + 1)) /
        (Real.Gamma
          (alpha + beta +
            (((dimension + 1) + (j + 1) - 1 : ℕ) : ℝ) / 2) *
          Real.Gamma (3 / 2))
  have hterm (j : ℕ) (hj : j ∈ Finset.range dimension) :
      originalTailTerm j =
        (selbergHalfGammaStep (j + 1) / selbergHalfGammaStep j) *
          shiftedTerm j := by
    unfold originalTailTerm shiftedTerm
    have hargumentsAlpha :
        alpha + (((j + 1 : ℕ) : ℝ)) / 2 =
          (alpha + 1 / 2) + (j : ℝ) / 2 := by
      push_cast
      ring
    have hargumentsBeta :
        beta + (((j + 1 : ℕ) : ℝ)) / 2 =
          (beta + 1 / 2) + (j : ℝ) / 2 := by
      push_cast
      ring
    have hargumentsDenominator :
        alpha + beta +
            (((dimension + 1) + (j + 1) - 1 : ℕ) : ℝ) / 2 =
          (alpha + 1 / 2) + (beta + 1 / 2) +
            ((dimension + j - 1 : ℕ) : ℝ) / 2 := by
      have hjlt : j < dimension := Finset.mem_range.mp hj
      rw [show dimension + 1 + (j + 1) - 1 = dimension + j + 1 by omega]
      have hnat : dimension + j - 1 + 2 = dimension + j + 1 := by omega
      have hnatReal :
          (((dimension + j - 1 : ℕ) : ℝ)) + 2 =
            ((dimension + j + 1 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      linarith
    rw [hargumentsAlpha, hargumentsBeta, hargumentsDenominator]
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    field_simp [selbergHalfGammaStep_ne_zero j]
  have htail :
      (∏ j ∈ Finset.range dimension, originalTailTerm j) =
        (selbergHalfGammaStep dimension / selbergHalfGammaStep 0) *
          ∏ j ∈ Finset.range dimension, shiftedTerm j := by
    calc
      (∏ j ∈ Finset.range dimension, originalTailTerm j) =
          ∏ j ∈ Finset.range dimension,
            ((selbergHalfGammaStep (j + 1) / selbergHalfGammaStep j) *
              shiftedTerm j) := by
        apply Finset.prod_congr rfl
        intro j hj
        exact hterm j hj
      _ = (∏ j ∈ Finset.range dimension,
            selbergHalfGammaStep (j + 1) / selbergHalfGammaStep j) *
          ∏ j ∈ Finset.range dimension, shiftedTerm j := by
        rw [Finset.prod_mul_distrib]
      _ = _ := by
        rw [selbergHalfGammaStep_telescope]
  unfold selbergHalfGammaProduct
  rw [Finset.prod_range_succ']
  have horiginalTail :
      (∏ k ∈ Finset.range dimension,
        (Real.Gamma (alpha + ((k + 1 : ℕ) : ℝ) / 2) *
          Real.Gamma (beta + ((k + 1 : ℕ) : ℝ) / 2) *
          Real.Gamma (1 + (((k + 1) + 1 : ℕ) : ℝ) / 2)) /
            (Real.Gamma
              (alpha + beta +
                (((dimension + 1) + (k + 1) - 1 : ℕ) : ℝ) / 2) *
              Real.Gamma (3 / 2))) =
        ∏ k ∈ Finset.range dimension, originalTailTerm k := by
    apply Finset.prod_congr rfl
    intro k hk
    rfl
  have hfirst :
      (Real.Gamma (alpha + ((0 : ℕ) : ℝ) / 2) *
          Real.Gamma (beta + ((0 : ℕ) : ℝ) / 2) *
          Real.Gamma (1 + ((0 + 1 : ℕ) : ℝ) / 2)) /
            (Real.Gamma
              (alpha + beta +
                (((dimension + 1) + 0 - 1 : ℕ) : ℝ) / 2) *
              Real.Gamma (3 / 2)) =
        (Real.Gamma alpha * Real.Gamma beta * selbergHalfGammaStep 0) /
          (Real.Gamma (alpha + beta + (dimension : ℝ) / 2) *
            Real.Gamma (3 / 2)) := by
    norm_num [selbergHalfGammaStep]
  have hshifted :
      (∏ j ∈ Finset.range dimension,
        (Real.Gamma ((alpha + 1 / 2) + (j : ℝ) / 2) *
          Real.Gamma ((beta + 1 / 2) + (j : ℝ) / 2) *
          Real.Gamma (1 + ((j + 1 : ℕ) : ℝ) / 2)) /
            (Real.Gamma
              ((alpha + 1 / 2) + (beta + 1 / 2) +
                ((dimension + j - 1 : ℕ) : ℝ) / 2) *
              Real.Gamma (3 / 2))) =
        ∏ j ∈ Finset.range dimension, shiftedTerm j := by
    apply Finset.prod_congr rfl
    intro j hj
    rfl
  rw [horiginalTail, hfirst, hshifted, htail]
  have hstepZero : selbergHalfGammaStep 0 = Real.Gamma (3 / 2) := by
    norm_num [selbergHalfGammaStep]
  rw [hstepZero]
  have hgammaThree : Real.Gamma (3 / 2 : ℝ) ≠ 0 := by positivity
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  field_simp [hgammaThree]

theorem expectedOrderedSelbergHalfIntegral_succ
    (dimension : ℕ) {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) :
    expectedOrderedSelbergHalfIntegral (dimension + 1) alpha beta =
      (Real.Gamma alpha * Real.Gamma beta *
        selbergHalfGammaStep dimension /
        (((dimension + 1 : ℕ) : ℝ) *
          Real.Gamma (alpha + beta + (dimension : ℝ) / 2) *
          selbergHalfGammaStep 0)) *
      expectedOrderedSelbergHalfIntegral dimension
        (alpha + 1 / 2) (beta + 1 / 2) := by
  unfold expectedOrderedSelbergHalfIntegral
  rw [selbergHalfGammaProduct_succ dimension halpha hbeta,
    Nat.factorial_succ]
  push_cast
  have hdimension : (((dimension + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hstepZero := selbergHalfGammaStep_ne_zero 0
  field_simp [hdimension, hstepZero]

end FibonacciRibbonKernel
