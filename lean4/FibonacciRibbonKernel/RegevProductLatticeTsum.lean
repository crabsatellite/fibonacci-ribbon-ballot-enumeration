import FibonacciRibbonKernel.RegevProductLattice

namespace FibonacciRibbonKernel

open scoped Classical

theorem tsum_regevPiProduct
    {index : Type*} {term : index → ℝ}
    (hterm : ∀ value, 0 ≤ term value) (hsum : Summable term) :
    ∀ rank : ℕ,
      (∑' point : Fin rank → index, regevPiProduct term rank point) =
        (∑' value : index, term value) ^ rank := by
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
      simp [regevPiProduct]
  | succ rank ih =>
      let equivalence := Fin.consEquiv
        (fun _ : Fin (rank + 1) => index)
      have htail := summable_regevPiProduct hterm hsum rank
      have hproduct : Summable (fun pair : index × (Fin rank → index) =>
          term pair.1 * regevPiProduct term rank pair.2) :=
        hsum.mul_of_nonneg htail hterm
          (regevPiProduct_nonneg hterm rank)
      calc
        (∑' point : Fin (rank + 1) → index,
            regevPiProduct term (rank + 1) point) =
          ∑' pair : index × (Fin rank → index),
            term pair.1 * regevPiProduct term rank pair.2 := by
          rw [← equivalence.tsum_eq]
          apply tsum_congr
          intro pair
          rw [show equivalence pair = Fin.cons pair.1 pair.2 by rfl]
          rw [regevPiProduct_cons]
        _ = (∑' value : index, term value) *
            ∑' point : Fin rank → index,
              regevPiProduct term rank point :=
          (hsum.tsum_mul_tsum htail hproduct).symm
        _ = (∑' value : index, term value) ^ (rank + 1) := by
          rw [ih]
          rw [pow_succ']

end FibonacciRibbonKernel
