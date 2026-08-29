import FibonacciRibbonKernel.RegevCoordinateAbsorption
import Mathlib.Analysis.Normed.Ring.InfiniteSum

namespace FibonacciRibbonKernel

open scoped Classical

noncomputable def regevPiProduct
    {index : Type*} (term : index → ℝ) (rank : ℕ)
    (point : Fin rank → index) : ℝ :=
  ∏ row, term (point row)

theorem regevPiProduct_nonneg
    {index : Type*} {term : index → ℝ}
    (hterm : ∀ value, 0 ≤ term value) (rank : ℕ)
    (point : Fin rank → index) :
    0 ≤ regevPiProduct term rank point := by
  unfold regevPiProduct
  exact Finset.prod_nonneg fun row hrow => hterm _

@[simp] theorem regevPiProduct_cons
    {index : Type*} (term : index → ℝ) (rank : ℕ)
    (head : index) (tail : Fin rank → index) :
    regevPiProduct term (rank + 1) (Fin.cons head tail) =
      term head * regevPiProduct term rank tail := by
  unfold regevPiProduct
  rw [Fin.prod_univ_succ]
  simp

theorem summable_regevPiProduct
    {index : Type*} {term : index → ℝ}
    (hterm : ∀ value, 0 ≤ term value) (hsum : Summable term) :
    ∀ rank : ℕ, Summable (regevPiProduct term rank) := by
  intro rank
  induction rank with
  | zero =>
      letI : Unique (Fin 0 → index) := {
        default := fun row => Fin.elim0 row
        uniq point := by
          funext row
          exact Fin.elim0 row
      }
      letI : Fintype (Fin 0 → index) := {
        elems := {default}
        complete point := by
          simpa only [Finset.mem_singleton] using
            (Subsingleton.elim point default)
      }
      exact Summable.of_finite
  | succ rank ih =>
      let equivalence := Fin.consEquiv
        (fun _ : Fin (rank + 1) => index)
      have hproduct : Summable (fun pair : index × (Fin rank → index) =>
          term pair.1 * regevPiProduct term rank pair.2) :=
        hsum.mul_of_nonneg ih hterm
          (regevPiProduct_nonneg hterm rank)
      refine equivalence.summable_iff.mp ?_
      refine hproduct.congr (fun pair => ?_)
      change term pair.1 * regevPiProduct term rank pair.2 =
        regevPiProduct term (rank + 1) (equivalence pair)
      rw [show equivalence pair = Fin.cons pair.1 pair.2 by rfl]
      rw [regevPiProduct_cons]

end FibonacciRibbonKernel
