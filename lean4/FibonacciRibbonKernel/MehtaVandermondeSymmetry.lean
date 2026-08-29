import FibonacciRibbonKernel.RegevMehtaStandardTarget
import Mathlib.LinearAlgebra.Vandermonde

namespace FibonacciRibbonKernel

open scoped Classical Matrix

theorem standardMehtaVandermonde_eq_abs_det
    (dimension : ℕ) (coordinates : Fin dimension → ℝ) :
    standardMehtaVandermonde dimension coordinates =
      |(Matrix.vandermonde coordinates).det| := by
  unfold standardMehtaVandermonde
  rw [Matrix.det_vandermonde, Finset.abs_prod]
  apply Finset.prod_congr rfl
  intro row hrow
  rw [Finset.abs_prod]
  apply Finset.prod_congr rfl
  intro next hnext
  rw [abs_sub_comm]

theorem standardMehtaGaussian_perm
    (dimension : ℕ) (coordinates : Fin dimension → ℝ)
    (permutation : Equiv.Perm (Fin dimension)) :
    standardMehtaGaussian dimension (coordinates ∘ permutation) =
      standardMehtaGaussian dimension coordinates := by
  unfold standardMehtaGaussian
  congr 2
  exact Equiv.sum_comp permutation
    (fun row => coordinates row ^ 2 / 2)

theorem vandermonde_perm_abs_det
    (dimension : ℕ) (coordinates : Fin dimension → ℝ)
    (permutation : Equiv.Perm (Fin dimension)) :
    |(Matrix.vandermonde (coordinates ∘ permutation)).det| =
      |(Matrix.vandermonde coordinates).det| := by
  have hmatrix : Matrix.vandermonde (coordinates ∘ permutation) =
      (Matrix.vandermonde coordinates).submatrix permutation id := by
    ext row column
    rfl
  rw [hmatrix, Matrix.det_permute]
  rw [abs_mul]
  have hsignInt := Equiv.Perm.sign_abs permutation
  have hsignReal :
      |((Equiv.Perm.sign permutation : ℤ) : ℝ)| = 1 := by
    exact_mod_cast hsignInt
  rw [hsignReal, one_mul]

theorem standardMehtaVandermonde_perm
    (dimension : ℕ) (coordinates : Fin dimension → ℝ)
    (permutation : Equiv.Perm (Fin dimension)) :
    standardMehtaVandermonde dimension (coordinates ∘ permutation) =
      standardMehtaVandermonde dimension coordinates := by
  rw [standardMehtaVandermonde_eq_abs_det,
    standardMehtaVandermonde_eq_abs_det,
    vandermonde_perm_abs_det]

theorem standardMehtaIntegrand_perm
    (dimension : ℕ) (coordinates : Fin dimension → ℝ)
    (permutation : Equiv.Perm (Fin dimension)) :
    standardMehtaIntegrand dimension (coordinates ∘ permutation) =
      standardMehtaIntegrand dimension coordinates := by
  unfold standardMehtaIntegrand
  rw [standardMehtaGaussian_perm,
    standardMehtaVandermonde_perm]

end FibonacciRibbonKernel
