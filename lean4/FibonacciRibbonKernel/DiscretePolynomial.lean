import Mathlib.NumberTheory.BernoulliPolynomials

namespace FibonacciRibbonKernel

open scoped Classical

noncomputable def polynomialDiscreteIntegral
    (polynomial : Polynomial ℚ) : Polynomial ℚ :=
  ∑ degree ∈ polynomial.support,
    Polynomial.C (polynomial.coeff degree / (degree + 1 : ℚ)) *
      Polynomial.bernoulli (degree + 1)

theorem polynomialDiscreteIntegral_difference (polynomial : Polynomial ℚ) :
    (polynomialDiscreteIntegral polynomial).comp (1 + Polynomial.X) -
      polynomialDiscreteIntegral polynomial = polynomial := by
  unfold polynomialDiscreteIntegral
  rw [Polynomial.sum_comp, ← Finset.sum_sub_distrib]
  calc
    (∑ degree ∈ polynomial.support,
        ((Polynomial.C (polynomial.coeff degree / (degree + 1 : ℚ)) *
            Polynomial.bernoulli (degree + 1)).comp (1 + Polynomial.X) -
          Polynomial.C (polynomial.coeff degree / (degree + 1 : ℚ)) *
            Polynomial.bernoulli (degree + 1))) =
      ∑ degree ∈ polynomial.support,
        Polynomial.C (polynomial.coeff degree) * Polynomial.X ^ degree := by
      apply Finset.sum_congr rfl
      intro degree hdegree
      rw [Polynomial.mul_comp, Polynomial.C_comp,
        Polynomial.bernoulli_comp_one_add_X]
      simp only [Nat.add_sub_cancel, mul_add, add_sub_cancel_left]
      have hnonzero : (degree + 1 : ℚ) ≠ 0 := by positivity
      rw [← Nat.cast_smul_eq_nsmul ℚ,
        Polynomial.smul_eq_C_mul, ← mul_assoc, ← Polynomial.C_mul]
      congr 2
      field_simp
      norm_num
    _ = polynomial := by
      change polynomial.sum (fun degree coefficient =>
        Polynomial.C coefficient * Polynomial.X ^ degree) = polynomial
      exact Polynomial.sum_C_mul_X_pow_eq polynomial

theorem polynomialDiscreteIntegral_eval_succ_sub
    (polynomial : Polynomial ℚ) (value : ℕ) :
    (polynomialDiscreteIntegral polynomial).eval (value + 1 : ℚ) -
      (polynomialDiscreteIntegral polynomial).eval (value : ℚ) =
        polynomial.eval (value : ℚ) := by
  have h := congrArg (Polynomial.eval (value : ℚ))
    (polynomialDiscreteIntegral_difference polynomial)
  simp only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_X] at h
  simpa [add_comm] using h

theorem polynomialDiscreteIntegral_natDegree_le
    (polynomial : Polynomial ℚ) (degree : ℕ)
    (hdegree : polynomial.natDegree ≤ degree) :
    (polynomialDiscreteIntegral polynomial).natDegree ≤ degree + 1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro exponent hexponent
  unfold polynomialDiscreteIntegral
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro index hindex
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_bernoulli]
  have hindexDegree : index ≤ degree := by
    exact (Polynomial.le_natDegree_of_mem_supp index hindex).trans hdegree
  rw [if_neg (by omega)]
  ring

theorem polynomialDiscreteIntegral_coeff_succ
    (polynomial : Polynomial ℚ) (degree : ℕ)
    (hdegree : polynomial.natDegree ≤ degree) :
    (polynomialDiscreteIntegral polynomial).coeff (degree + 1) =
      polynomial.coeff degree / (degree + 1 : ℚ) := by
  unfold polynomialDiscreteIntegral
  rw [Polynomial.finsetSum_coeff]
  by_cases hmem : degree ∈ polynomial.support
  · rw [Finset.sum_eq_single degree]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_bernoulli, if_pos (by omega)]
      simp
    · intro index hindex hne
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_bernoulli]
      have hindexDegree : index ≤ degree :=
        (Polynomial.le_natDegree_of_mem_supp index hindex).trans hdegree
      rw [if_neg (by omega)]
      ring
    · intro hnot
      exact (hnot hmem).elim
  · have hcoeff : polynomial.coeff degree = 0 := by
      simpa [Polynomial.mem_support_iff] using hmem
    rw [hcoeff, zero_div]
    apply Finset.sum_eq_zero
    intro index hindex
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_bernoulli]
    have hindexDegree : index ≤ degree :=
      (Polynomial.le_natDegree_of_mem_supp index hindex).trans hdegree
    have hne : index ≠ degree := by
      intro heq
      exact hmem (heq ▸ hindex)
    rw [if_neg (by omega)]
    ring

end FibonacciRibbonKernel
