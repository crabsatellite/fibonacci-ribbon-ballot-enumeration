import FibonacciRibbonKernel.ExteriorMinorSum
import Mathlib.Data.List.Sublists

namespace FibonacciRibbonKernel

open ExteriorAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

noncomputable def exteriorListProduct : List M → ExteriorAlgebra R M
  | [] => 1
  | head :: tail => ExteriorAlgebra.ι R head * exteriorListProduct tail

@[simp] theorem exteriorListProduct_nil :
    exteriorListProduct (R := R) ([] : List M) = 1 := rfl

@[simp] theorem exteriorListProduct_cons (head : M) (tail : List M) :
    exteriorListProduct (R := R) (head :: tail) =
      ExteriorAlgebra.ι R head * exteriorListProduct tail := rfl

/-- The recursive elementary exterior sum is literally the sum over
fixed-length sublists, with the source order retained in each wedge. -/
theorem exteriorElementary_eq_sum_sublistsLen
    (degree : ℕ) (vectors : List M) :
    exteriorElementary (R := R) degree vectors =
      List.sum (List.map
        (exteriorListProduct (R := R))
        (vectors.sublistsLen degree)) := by
  induction vectors generalizing degree with
  | nil =>
      cases degree with
      | zero => rw [List.sublistsLen_zero]; simp
      | succ degree => rw [List.sublistsLen_succ_nil]; simp
  | cons head tail ih =>
      cases degree with
      | zero => rw [List.sublistsLen_zero]; simp
      | succ degree =>
          rw [exteriorElementary_cons_succ,
            List.sublistsLen_succ_cons, List.map_append,
            List.sum_append, List.map_map]
          rw [ih (degree + 1), ih degree]
          have hmap :
              (List.map (exteriorListProduct (R := R) ∘ List.cons head)
                  (List.sublistsLen degree tail)).sum =
                ExteriorAlgebra.ι R head *
                  (List.map (exteriorListProduct (R := R))
                    (List.sublistsLen degree tail)).sum := by
            change
              (List.map (fun selected => ExteriorAlgebra.ι R head *
                  exteriorListProduct (R := R) selected)
                (List.sublistsLen degree tail)).sum = _
            exact List.sum_map_mul_left
              (List.sublistsLen degree tail)
              (exteriorListProduct (R := R))
              (ExteriorAlgebra.ι R head)
          rw [hmap]
          ac_rfl

theorem topFiveDeterminant_exteriorElementary_eq_sum_sublists
    (rows : List (FiveRow R)) :
    topFiveDeterminant (R := R) (exteriorElementary 5 rows) =
      ((rows.sublistsLen 5).map fun selected =>
        topFiveDeterminant (R := R)
          (exteriorListProduct (R := R) selected)).sum := by
  rw [exteriorElementary_eq_sum_sublistsLen]
  simp only [map_list_sum]
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro selected hselected
  rfl

omit [CommRing R] [AddCommGroup M] [Module R M] in
theorem sublistsLen_map (function : M → R) (degree : ℕ) (values : List M) :
    (values.map function).sublistsLen degree =
      (values.sublistsLen degree).map (List.map function) := by
  induction values generalizing degree with
  | nil =>
      cases degree with
      | zero => simp [List.sublistsLen_zero]
      | succ degree => simp [List.sublistsLen_succ_nil]
  | cons head tail ih =>
      cases degree with
      | zero => simp [List.sublistsLen_zero]
      | succ degree =>
          rw [List.map_cons, List.sublistsLen_succ_cons,
            List.sublistsLen_succ_cons, ih (degree + 1), ih degree,
            List.map_append, List.map_map, List.map_map]
          congr 2

end FibonacciRibbonKernel
