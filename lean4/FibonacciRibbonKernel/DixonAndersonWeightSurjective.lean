import FibonacciRibbonKernel.DixonAndersonInverseRoots
import Mathlib.Algebra.Polynomial.Div

namespace FibonacciRibbonKernel

open scoped Classical

theorem andersonRootFromSimplex_strictAnti {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (coordinates : Fin dimension → ℝ)
    (hanchors : StrictAnti anchors)
    (hcoordinates : coordinates ∈ dirichletOpenSimplex dimension) :
    StrictAnti
      (andersonRootFromSimplex anchors coordinates hanchors hcoordinates) :=
  roots_strictAnti_of_interlacing hanchors
    (andersonRootFromSimplex_interlaces anchors coordinates hanchors hcoordinates)

theorem andersonRootPolynomial_dvd_inversePolynomial {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (coordinates : Fin dimension → ℝ)
    (hanchors : StrictAnti anchors)
    (hcoordinates : coordinates ∈ dirichletOpenSimplex dimension) :
    andersonRootPolynomial
        (andersonRootFromSimplex anchors coordinates hanchors hcoordinates) ∣
      andersonPolynomialFromSimplex anchors coordinates := by
  unfold andersonRootPolynomial
  let roots := andersonRootFromSimplex anchors coordinates hanchors hcoordinates
  have hrootInjective : Function.Injective roots :=
    (andersonRootFromSimplex_strictAnti
      anchors coordinates hanchors hcoordinates).injective
  apply Finset.prod_dvd_of_coprime
  · intro first hfirst second hsecond hne
    exact Polynomial.pairwise_coprime_X_sub_C hrootInjective hne
  · intro index hindex
    rw [Polynomial.dvd_iff_isRoot]
    exact (andersonRootFromSimplex_spec
      anchors coordinates hanchors hcoordinates index).2.2

theorem andersonRootPolynomial_inverse_eq {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (coordinates : Fin dimension → ℝ)
    (hanchors : StrictAnti anchors)
    (hcoordinates : coordinates ∈ dirichletOpenSimplex dimension) :
    andersonRootPolynomial
        (andersonRootFromSimplex anchors coordinates hanchors hcoordinates) =
      andersonPolynomialFromSimplex anchors coordinates := by
  let roots := andersonRootFromSimplex anchors coordinates hanchors hcoordinates
  have hdvd := andersonRootPolynomial_dvd_inversePolynomial
    anchors coordinates hanchors hcoordinates
  have hdegree :
      (andersonPolynomialFromSimplex anchors coordinates).natDegree ≤
        (andersonRootPolynomial roots).natDegree := by
    rw [andersonPolynomialFromSimplex_natDegree,
      andersonRootPolynomial_natDegree]
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (andersonRootPolynomial_monic roots)
    (andersonPolynomialFromSimplex_monic anchors coordinates)
    hdvd hdegree).symm

theorem andersonDenominator_ne_zero {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (hanchors : Function.Injective anchors)
    (anchor : Fin (dimension + 1)) :
    (∏ other ∈ Finset.univ.erase anchor,
      (anchors anchor - anchors other)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro other hother
  have hne : other ≠ anchor := Finset.ne_of_mem_erase hother
  exact sub_ne_zero.mpr (hanchors.ne hne.symm)

theorem andersonWeight_inverse_eq_simplexExtend {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (coordinates : Fin dimension → ℝ)
    (hanchors : StrictAnti anchors)
    (hcoordinates : coordinates ∈ dirichletOpenSimplex dimension)
    (anchor : Fin (dimension + 1)) :
    andersonWeight anchors
        (andersonRootFromSimplex anchors coordinates hanchors hcoordinates)
        anchor =
      simplexExtend coordinates anchor := by
  let roots := andersonRootFromSimplex anchors coordinates hanchors hcoordinates
  have hpoly := andersonRootPolynomial_inverse_eq
    anchors coordinates hanchors hcoordinates
  have heval := congrArg
    (fun polynomial : Polynomial ℝ => polynomial.eval (anchors anchor)) hpoly
  rw [andersonPolynomialFromSimplex_eval_anchor] at heval
  unfold andersonWeight
  change (andersonRootPolynomial roots).eval (anchors anchor) / _ = _
  rw [heval]
  rw [mul_div_cancel_right₀]
  exact andersonDenominator_ne_zero anchors hanchors.injective anchor

theorem andersonWeightChart_inverse_eq {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (coordinates : Fin dimension → ℝ)
    (hanchors : StrictAnti anchors)
    (hcoordinates : coordinates ∈ dirichletOpenSimplex dimension) :
    andersonWeightChart anchors
        (andersonRootFromSimplex anchors coordinates hanchors hcoordinates) =
      coordinates := by
  funext index
  unfold andersonWeightChart
  rw [andersonWeight_inverse_eq_simplexExtend
    anchors coordinates hanchors hcoordinates index.castSucc,
    simplexExtend_castSucc]

theorem andersonWeightChart_surjective_on_interlacing {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (hanchors : StrictAnti anchors) :
    Set.SurjOn (andersonWeightChart anchors)
      (dixonAndersonDomain dimension anchors)
      (dirichletOpenSimplex dimension) := by
  intro coordinates hcoordinates
  refine ⟨andersonRootFromSimplex anchors coordinates hanchors hcoordinates,
    andersonRootFromSimplex_interlaces anchors coordinates hanchors hcoordinates,
    andersonWeightChart_inverse_eq anchors coordinates hanchors hcoordinates⟩

end FibonacciRibbonKernel
