import FibonacciRibbonKernel.DixonAndersonHalfTarget

namespace FibonacciRibbonKernel

open scoped Classical

noncomputable def andersonRootPolynomial {dimension : ℕ}
    (roots : Fin dimension → ℝ) : Polynomial ℝ :=
  ∏ index, (Polynomial.X - Polynomial.C (roots index))

noncomputable def andersonWeight {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ) (anchor : Fin (dimension + 1)) : ℝ :=
  (andersonRootPolynomial roots).eval (anchors anchor) /
    ∏ other ∈ Finset.univ.erase anchor,
      (anchors anchor - anchors other)

theorem andersonRootPolynomial_monic {dimension : ℕ}
    (roots : Fin dimension → ℝ) :
    (andersonRootPolynomial roots).Monic := by
  unfold andersonRootPolynomial
  exact Polynomial.monic_prod_X_sub_C roots Finset.univ

theorem andersonRootPolynomial_natDegree {dimension : ℕ}
    (roots : Fin dimension → ℝ) :
    (andersonRootPolynomial roots).natDegree = dimension := by
  unfold andersonRootPolynomial
  rw [Polynomial.natDegree_prod_of_monic]
  · simp
  · intro index hindex
    exact Polynomial.monic_X_sub_C (roots index)

theorem andersonRootPolynomial_coeff_dimension {dimension : ℕ}
    (roots : Fin dimension → ℝ) :
    (andersonRootPolynomial roots).coeff dimension = 1 := by
  have hdegree := andersonRootPolynomial_natDegree roots
  have hleading := (andersonRootPolynomial_monic roots).coeff_natDegree
  simpa only [hdegree] using hleading

theorem andersonRootPolynomial_degree_lt {dimension : ℕ}
    (roots : Fin dimension → ℝ) :
    (andersonRootPolynomial roots).degree <
      (Finset.univ : Finset (Fin (dimension + 1))).card := by
  have hnonzero := (andersonRootPolynomial_monic roots).ne_zero
  rw [show (Finset.univ : Finset (Fin (dimension + 1))).card =
      dimension + 1 by simp]
  rw [← Polynomial.natDegree_lt_iff_degree_lt hnonzero]
  rw [andersonRootPolynomial_natDegree]
  omega

theorem sum_andersonWeight_eq_one {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ) (hanchors : Function.Injective anchors) :
    ∑ anchor, andersonWeight anchors roots anchor = 1 := by
  have hinterpolation := Lagrange.coeff_eq_sum
    (s := (Finset.univ : Finset (Fin (dimension + 1))))
    (v := anchors) hanchors.injOn
    (andersonRootPolynomial_degree_lt roots)
  simp only [Finset.card_univ, Fintype.card_fin,
    Nat.add_sub_cancel] at hinterpolation
  rw [andersonRootPolynomial_coeff_dimension] at hinterpolation
  unfold andersonWeight
  exact hinterpolation.symm

theorem andersonRootPolynomial_interpolation {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ) (hanchors : Function.Injective anchors) :
    andersonRootPolynomial roots =
      ∑ anchor : Fin (dimension + 1),
        Polynomial.C (andersonWeight anchors roots anchor) *
          ∏ other ∈ Finset.univ.erase anchor,
            (Polynomial.X - Polynomial.C (anchors other)) := by
  have hinterpolation := Lagrange.eq_interpolate
    (s := (Finset.univ : Finset (Fin (dimension + 1))))
    (v := anchors) hanchors.injOn
    (andersonRootPolynomial_degree_lt roots)
  rw [hinterpolation]
  rw [Lagrange.interpolate_eq_sum]
  unfold andersonWeight
  rfl

theorem andersonRootPolynomial_eval_root {dimension : ℕ}
    (roots : Fin dimension → ℝ) (index : Fin dimension) :
    (andersonRootPolynomial roots).eval (roots index) = 0 := by
  unfold andersonRootPolynomial
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (i := index)
  · simp
  · simp

theorem andersonWeight_root_relation {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ) (hanchors : Function.Injective anchors)
    (index : Fin dimension) :
    ∑ anchor : Fin (dimension + 1),
      andersonWeight anchors roots anchor *
        ∏ other ∈ Finset.univ.erase anchor,
          (roots index - anchors other) = 0 := by
  have hpoly := congrArg
    (fun polynomial : Polynomial ℝ => polynomial.eval (roots index))
    (andersonRootPolynomial_interpolation anchors roots hanchors)
  rw [andersonRootPolynomial_eval_root] at hpoly
  simpa [Polynomial.eval_finsetSum, Polynomial.eval_prod] using hpoly.symm

end FibonacciRibbonKernel
