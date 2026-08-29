import FibonacciRibbonKernel.DixonAndersonWeightChart
import Mathlib.Data.List.Sort

namespace FibonacciRibbonKernel

open scoped Classical

theorem roots_andersonRootPolynomial {dimension : ℕ}
    (roots : Fin dimension → ℝ) :
    (andersonRootPolynomial roots).roots = List.ofFn roots := by
  unfold andersonRootPolynomial
  rw [Polynomial.roots_prod]
  · simp_rw [Polynomial.roots_X_sub_C]
    rw [Multiset.bind_singleton, Fin.univ_val_map]
  · exact (andersonRootPolynomial_monic roots).ne_zero

theorem roots_eq_of_rootPolynomial_eq {dimension : ℕ}
    {left right : Fin dimension → ℝ}
    (hleft : StrictAnti left) (hright : StrictAnti right)
    (hpolynomial : andersonRootPolynomial left =
      andersonRootPolynomial right) :
    left = right := by
  have hroots := congrArg Polynomial.roots hpolynomial
  rw [roots_andersonRootPolynomial,
    roots_andersonRootPolynomial] at hroots
  have hperm : List.Perm (List.ofFn left) (List.ofFn right) :=
    Multiset.coe_eq_coe.mp hroots
  have hleftSorted : (List.ofFn left).SortedGE :=
    hleft.antitone.sortedGE_ofFn
  have hrightSorted : (List.ofFn right).SortedGE :=
    hright.antitone.sortedGE_ofFn
  exact List.ofFn_injective
    (List.Perm.eq_of_sortedGE hleftSorted hrightSorted hperm)

theorem andersonWeightChart_injective_on_interlacing {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (hanchors : StrictAnti anchors) :
    Set.InjOn (andersonWeightChart anchors)
      (dixonAndersonDomain dimension anchors) := by
  intro left hleft right hright hchart
  have hfull : andersonWeight anchors left =
      andersonWeight anchors right := by
    rw [← simplexExtend_andersonWeightChart anchors left hanchors.injective,
      ← simplexExtend_andersonWeightChart anchors right hanchors.injective,
      hchart]
  have hleftPoly := andersonRootPolynomial_interpolation
    anchors left hanchors.injective
  have hrightPoly := andersonRootPolynomial_interpolation
    anchors right hanchors.injective
  rw [hfull] at hleftPoly
  have hpoly : andersonRootPolynomial left =
      andersonRootPolynomial right := hleftPoly.trans hrightPoly.symm
  exact roots_eq_of_rootPolynomial_eq
    (roots_strictAnti_of_interlacing hanchors hleft)
    (roots_strictAnti_of_interlacing hanchors hright)
    hpoly

end FibonacciRibbonKernel
