import FibonacciRibbonKernel.DixonAndersonWeightInjective

namespace FibonacciRibbonKernel

open scoped Classical

noncomputable def andersonAnchorBasis {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (anchor : Fin (dimension + 1)) : Polynomial ℝ :=
  ∏ other ∈ Finset.univ.erase anchor,
    (Polynomial.X - Polynomial.C (anchors other))

noncomputable def andersonPolynomialFromSimplex {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (coordinates : Fin dimension → ℝ) : Polynomial ℝ :=
  ∑ anchor : Fin (dimension + 1),
    Polynomial.C (simplexExtend coordinates anchor) *
      andersonAnchorBasis anchors anchor

theorem andersonAnchorBasis_monic {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (anchor : Fin (dimension + 1)) :
    (andersonAnchorBasis anchors anchor).Monic := by
  unfold andersonAnchorBasis
  exact Polynomial.monic_prod_X_sub_C anchors (Finset.univ.erase anchor)

theorem andersonAnchorBasis_natDegree {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (anchor : Fin (dimension + 1)) :
    (andersonAnchorBasis anchors anchor).natDegree = dimension := by
  unfold andersonAnchorBasis
  rw [Polynomial.natDegree_prod_of_monic]
  · simp
  · intro other hother
    exact Polynomial.monic_X_sub_C (anchors other)

theorem andersonAnchorBasis_coeff_dimension {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (anchor : Fin (dimension + 1)) :
    (andersonAnchorBasis anchors anchor).coeff dimension = 1 := by
  have hleading := (andersonAnchorBasis_monic anchors anchor).coeff_natDegree
  simpa only [andersonAnchorBasis_natDegree] using hleading

theorem andersonAnchorBasis_eval_self {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (anchor : Fin (dimension + 1)) :
    (andersonAnchorBasis anchors anchor).eval (anchors anchor) =
      ∏ other ∈ Finset.univ.erase anchor,
        (anchors anchor - anchors other) := by
  unfold andersonAnchorBasis
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro other hother
  simp

theorem andersonAnchorBasis_eval_other {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    {anchor other : Fin (dimension + 1)} (hne : other ≠ anchor) :
    (andersonAnchorBasis anchors other).eval (anchors anchor) = 0 := by
  unfold andersonAnchorBasis
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (i := anchor)
  · simp [hne.symm]
  · simp

theorem andersonPolynomialFromSimplex_eval_anchor {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (coordinates : Fin dimension → ℝ)
    (anchor : Fin (dimension + 1)) :
    (andersonPolynomialFromSimplex anchors coordinates).eval
        (anchors anchor) =
      simplexExtend coordinates anchor *
        ∏ other ∈ Finset.univ.erase anchor,
          (anchors anchor - anchors other) := by
  unfold andersonPolynomialFromSimplex
  rw [Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_single anchor]
  · rw [Polynomial.eval_mul, Polynomial.eval_C,
      andersonAnchorBasis_eval_self]
  · intro other hother hne
    rw [Polynomial.eval_mul, andersonAnchorBasis_eval_other anchors hne,
      mul_zero]
  · intro hnot
    exact (hnot (Finset.mem_univ anchor)).elim

theorem andersonPolynomialFromSimplex_coeff_dimension {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (coordinates : Fin dimension → ℝ) :
    (andersonPolynomialFromSimplex anchors coordinates).coeff dimension = 1 := by
  unfold andersonPolynomialFromSimplex
  rw [Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul,
    andersonAnchorBasis_coeff_dimension, mul_one]
  exact simplexExtend_sum coordinates

theorem andersonPolynomialFromSimplex_natDegree_le {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (coordinates : Fin dimension → ℝ) :
    (andersonPolynomialFromSimplex anchors coordinates).natDegree ≤ dimension := by
  unfold andersonPolynomialFromSimplex
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro anchor hanchor
  exact (Polynomial.natDegree_C_mul_le _ _).trans_eq
    (andersonAnchorBasis_natDegree anchors anchor)

theorem andersonPolynomialFromSimplex_monic {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (coordinates : Fin dimension → ℝ) :
    (andersonPolynomialFromSimplex anchors coordinates).Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one dimension
    (andersonPolynomialFromSimplex_natDegree_le anchors coordinates)
    (andersonPolynomialFromSimplex_coeff_dimension anchors coordinates)

theorem andersonPolynomialFromSimplex_natDegree {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (coordinates : Fin dimension → ℝ) :
    (andersonPolynomialFromSimplex anchors coordinates).natDegree = dimension := by
  apply le_antisymm
  · exact andersonPolynomialFromSimplex_natDegree_le anchors coordinates
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [andersonPolynomialFromSimplex_coeff_dimension]
    norm_num

end FibonacciRibbonKernel
