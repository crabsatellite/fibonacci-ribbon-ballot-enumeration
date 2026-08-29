import FibonacciRibbonKernel.SelbergHalfEvaluation
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped Classical Matrix BigOperators

noncomputable def mehtaLeibnizTerm (dimension : ℕ) (decay : ℝ)
    (permutation : Equiv.Perm (Fin dimension))
    (coordinates : Fin dimension → ℝ) : ℝ :=
  ∏ index : Fin dimension,
    |coordinates index| ^ (permutation.symm index).val *
      Real.exp (-decay * coordinates index ^ 2)

noncomputable def mehtaLeibnizDominating (dimension : ℕ)
    (coordinates : Fin dimension → ℝ) : ℝ :=
  ∑ permutation : Equiv.Perm (Fin dimension),
    mehtaLeibnizTerm dimension (1 / 4) permutation coordinates

theorem integrable_abs_pow_mul_exp_neg_mul_sq
    (power : ℕ) {decay : ℝ} (hdecay : 0 < decay) :
    Integrable (fun value : ℝ =>
      |value| ^ power * Real.exp (-decay * value ^ 2)) := by
  have hpower : (-1 : ℝ) < (power : ℝ) :=
    lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg power)
  have hbase : Integrable (fun value : ℝ =>
      value ^ (power : ℝ) * Real.exp (-decay * value ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq hdecay hpower
  have hnorm : Integrable (fun value : ℝ =>
      ‖value ^ (power : ℝ) * Real.exp (-decay * value ^ 2)‖) :=
    hbase.norm
  apply hnorm.congr
  exact Filter.Eventually.of_forall fun value => by
    change ‖value ^ (power : ℝ) * Real.exp (-decay * value ^ 2)‖ =
      |value| ^ power * Real.exp (-decay * value ^ 2)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [Real.rpow_natCast, abs_pow]

theorem integrable_mehtaLeibnizTerm
    (dimension : ℕ) {decay : ℝ} (hdecay : 0 < decay)
    (permutation : Equiv.Perm (Fin dimension)) :
    Integrable (mehtaLeibnizTerm dimension decay permutation) := by
  unfold mehtaLeibnizTerm
  exact Integrable.fintype_prod fun index =>
    integrable_abs_pow_mul_exp_neg_mul_sq
      (permutation.symm index).val hdecay

theorem integrable_mehtaLeibnizDominating (dimension : ℕ) :
    Integrable (mehtaLeibnizDominating dimension) := by
  unfold mehtaLeibnizDominating
  apply integrable_finsetSum
  intro permutation hpermutation
  exact integrable_mehtaLeibnizTerm dimension (by norm_num) permutation

theorem mehtaLeibnizTerm_eq_gaussian_mul_monomial
    (dimension : ℕ) (decay : ℝ)
    (permutation : Equiv.Perm (Fin dimension))
    (coordinates : Fin dimension → ℝ) :
    mehtaLeibnizTerm dimension decay permutation coordinates =
      Real.exp (-decay * ∑ index, coordinates index ^ 2) *
        ∏ index, |coordinates (permutation index)| ^ index.val := by
  unfold mehtaLeibnizTerm
  rw [← Equiv.prod_comp permutation]
  simp only [Equiv.symm_apply_apply]
  rw [Finset.prod_mul_distrib]
  have hexponential :
      (∏ index : Fin dimension,
        Real.exp (-decay * coordinates (permutation index) ^ 2)) =
      Real.exp (-decay * ∑ index, coordinates index ^ 2) := by
    rw [← Real.exp_sum]
    congr 1
    rw [Equiv.sum_comp permutation
      (fun index => -decay * coordinates index ^ 2)]
    rw [← Finset.mul_sum]
  rw [hexponential]
  ring

theorem abs_det_vandermonde_le_sum_monomials
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) :
    |(Matrix.vandermonde coordinates).det| ≤
      ∑ permutation : Equiv.Perm (Fin dimension),
        ∏ index, |coordinates (permutation index)| ^ index.val := by
  rw [Matrix.det_apply']
  calc
    |∑ permutation : Equiv.Perm (Fin dimension),
        (((Equiv.Perm.sign permutation : ℤ) : ℝ) *
          ∏ index, Matrix.vandermonde coordinates
            (permutation index) index)| ≤
      ∑ permutation : Equiv.Perm (Fin dimension),
        |(((Equiv.Perm.sign permutation : ℤ) : ℝ) *
          ∏ index, Matrix.vandermonde coordinates
            (permutation index) index)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ permutation : Equiv.Perm (Fin dimension),
        ∏ index, |coordinates (permutation index)| ^ index.val := by
      apply Finset.sum_congr rfl
      intro permutation hpermutation
      rw [abs_mul]
      have hsign :
          |((Equiv.Perm.sign permutation : ℤ) : ℝ)| = 1 := by
        exact_mod_cast Equiv.Perm.sign_abs permutation
      rw [hsign, one_mul, Finset.abs_prod]
      apply Finset.prod_congr rfl
      intro index hindex
      rw [Matrix.vandermonde_apply, abs_pow]

theorem norm_standardMehtaIntegrand_le_dominating
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) :
    ‖standardMehtaIntegrand dimension coordinates‖ ≤
      mehtaLeibnizDominating dimension coordinates := by
  have hsquares : 0 ≤ ∑ index, coordinates index ^ 2 :=
    Finset.sum_nonneg fun index hindex => sq_nonneg _
  have hdet := abs_det_vandermonde_le_sum_monomials
    dimension coordinates
  have hexponential :
      Real.exp (-(∑ index, coordinates index ^ 2) / 2) ≤
        Real.exp (-(1 / 4 : ℝ) * ∑ index, coordinates index ^ 2) := by
    apply Real.exp_le_exp.mpr
    linarith
  unfold standardMehtaIntegrand standardMehtaGaussian
  rw [standardMehtaVandermonde_eq_abs_det]
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _), abs_of_nonneg (abs_nonneg _)]
  calc
    Real.exp (-(∑ row, coordinates row ^ 2 / 2)) *
        |(Matrix.vandermonde coordinates).det| ≤
      Real.exp (-(∑ row, coordinates row ^ 2 / 2)) *
        (∑ permutation : Equiv.Perm (Fin dimension),
          ∏ index, |coordinates (permutation index)| ^ index.val) := by
      exact mul_le_mul_of_nonneg_left hdet (Real.exp_pos _).le
    _ ≤ Real.exp (-(1 / 4 : ℝ) *
          ∑ row, coordinates row ^ 2) *
        (∑ permutation : Equiv.Perm (Fin dimension),
          ∏ index, |coordinates (permutation index)| ^ index.val) := by
      apply mul_le_mul_of_nonneg_right
      · convert hexponential using 1
        congr 1
        rw [← Finset.sum_div]
        ring
      · exact Finset.sum_nonneg fun permutation hpermutation =>
          Finset.prod_nonneg fun index hindex => pow_nonneg (abs_nonneg _) _
    _ = mehtaLeibnizDominating dimension coordinates := by
      unfold mehtaLeibnizDominating
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro permutation hpermutation
      rw [mehtaLeibnizTerm_eq_gaussian_mul_monomial]

theorem quarterGaussianVandermonde_le_dominating
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) :
    Real.exp (-(1 / 4 : ℝ) * ∑ index, coordinates index ^ 2) *
        standardMehtaVandermonde dimension coordinates ≤
      mehtaLeibnizDominating dimension coordinates := by
  rw [standardMehtaVandermonde_eq_abs_det]
  calc
    Real.exp (-(1 / 4 : ℝ) * ∑ index, coordinates index ^ 2) *
        |(Matrix.vandermonde coordinates).det| ≤
      Real.exp (-(1 / 4 : ℝ) * ∑ index, coordinates index ^ 2) *
        (∑ permutation : Equiv.Perm (Fin dimension),
          ∏ index, |coordinates (permutation index)| ^ index.val) := by
      exact mul_le_mul_of_nonneg_left
        (abs_det_vandermonde_le_sum_monomials dimension coordinates)
        (Real.exp_pos _).le
    _ = mehtaLeibnizDominating dimension coordinates := by
      unfold mehtaLeibnizDominating
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro permutation hpermutation
      rw [mehtaLeibnizTerm_eq_gaussian_mul_monomial]

end FibonacciRibbonKernel
