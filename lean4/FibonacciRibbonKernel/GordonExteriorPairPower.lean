import FibonacciRibbonKernel.GordonPfaffianDeterminant
import FibonacciRibbonKernel.ExteriorDividedPowers

namespace FibonacciRibbonKernel

open ExteriorAlgebra

theorem list_prod_mul_eq_zero_of_mem_square_zero
    {A : Type*} [Ring A] (values : List A) (value : A)
    (hvalue : value ∈ values)
    (hsquare : value * value = 0)
    (hcommute : ∀ other ∈ values, Commute other value) :
    values.prod * value = 0 := by
  induction values generalizing value with
  | nil => simp at hvalue
  | cons head tail ih =>
      rw [List.prod_cons]
      rcases List.mem_cons.mp hvalue with hhead | htail
      · subst head
        have htailCommute : Commute tail.prod value :=
          Commute.list_prod_left tail value (fun other hother =>
            hcommute other (List.mem_cons_of_mem value hother))
        calc
          (value * tail.prod) * value =
              value * (tail.prod * value) := by rw [mul_assoc]
          _ = value * (value * tail.prod) := by rw [htailCommute.eq]
          _ = 0 := by rw [← mul_assoc, hsquare, zero_mul]
      · rw [mul_assoc]
        rw [ih value htail hsquare (fun other hother =>
          hcommute other (List.mem_cons_of_mem head hother))]
        rw [mul_zero]

theorem mul_list_sum_eq_zero
    {A : Type*} [Ring A] (constant : A) (values : List A)
    (hzero : ∀ value ∈ values, constant * value = 0) :
    constant * values.sum = 0 := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      rw [List.sum_cons, mul_add,
        hzero head List.mem_cons_self,
        ih (fun value hvalue =>
          hzero value (List.mem_cons_of_mem head hvalue)), zero_add]

theorem list_prod_mul_sum_eq_zero_of_square_zero
    {A : Type*} [Ring A] (values : List A)
    (hsquare : ∀ value ∈ values, value * value = 0)
    (hcommute : ∀ left ∈ values, ∀ right ∈ values, Commute left right) :
    values.prod * values.sum = 0 := by
  apply mul_list_sum_eq_zero values.prod values
  intro value hvalue
  exact list_prod_mul_eq_zero_of_mem_square_zero values value hvalue
    (hsquare value hvalue)
    (fun other hother => hcommute other hother value hvalue)

/-- The top nonzero power of a finite sum of pairwise commuting square-zero
elements is the factorial times their ordered product. -/
theorem commuting_squareZero_list_sum_pow
    {A : Type*} [Ring A] (values : List A)
    (hsquare : ∀ value ∈ values, value * value = 0)
    (hcommute : ∀ left ∈ values, ∀ right ∈ values, Commute left right) :
    values.sum ^ values.length = values.length.factorial • values.prod := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      have hheadSquare : head * head = 0 :=
        hsquare head List.mem_cons_self
      have hheadCommute : Commute head tail.sum :=
        Commute.list_sum_right head tail (fun value hvalue =>
          hcommute head List.mem_cons_self value
            (List.mem_cons_of_mem head hvalue))
      have htailInduction :
          tail.sum ^ tail.length = tail.length.factorial • tail.prod :=
        ih
          (fun value hvalue =>
            hsquare value (List.mem_cons_of_mem head hvalue))
          (fun left hleft right hright =>
            hcommute left (List.mem_cons_of_mem head hleft)
              right (List.mem_cons_of_mem head hright))
      have htailNext : tail.sum ^ (tail.length + 1) = 0 := by
        rw [pow_succ, htailInduction]
        simp only [nsmul_eq_mul, mul_assoc]
        rw [list_prod_mul_sum_eq_zero_of_square_zero tail
          (fun value hvalue =>
            hsquare value (List.mem_cons_of_mem head hvalue))
          (fun left hleft right hright =>
            hcommute left (List.mem_cons_of_mem head hleft)
              right (List.mem_cons_of_mem head hright)), mul_zero]
      rw [List.sum_cons, List.length_cons]
      rw [add_pow_of_commute_sq_zero head tail.sum hheadCommute
        hheadSquare (tail.length + 1)]
      rw [htailNext, show tail.length + 1 - 1 = tail.length by omega,
        htailInduction, zero_add]
      simp only [List.prod_cons]
      simp only [nsmul_eq_mul]
      rw [Nat.factorial_succ]
      push_cast
      rw [mul_assoc]
      apply congrArg (fun term : A =>
        ((tail.length : A) + 1) * term)
      calc
        head * ((tail.length.factorial : A) * tail.prod) =
            (head * (tail.length.factorial : A)) *
              tail.prod := by rw [mul_assoc]
        _ = ((tail.length.factorial : A) * head) *
              tail.prod := by
                rw [(Nat.cast_commute tail.length.factorial head).eq]
        _ = (tail.length.factorial : A) *
            (head * tail.prod) := by rw [mul_assoc]

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem exterior_iota_pair_sq_zero (left right : M) :
    (ExteriorAlgebra.ι R left * ExteriorAlgebra.ι R right) *
        (ExteriorAlgebra.ι R left * ExteriorAlgebra.ι R right) = 0 := by
  simpa [exteriorElementary] using
    exterior_cross_sq_zero (R := R) left [right]

theorem exterior_iota_pairs_commute
    (leftOne rightOne leftTwo rightTwo : M) :
    Commute
      (ExteriorAlgebra.ι R leftOne * ExteriorAlgebra.ι R rightOne)
      (ExteriorAlgebra.ι R leftTwo * ExteriorAlgebra.ι R rightTwo) := by
  apply Commute.eq
  have hleft :
      ExteriorAlgebra.ι R leftOne *
          (ExteriorAlgebra.ι R leftTwo * ExteriorAlgebra.ι R rightTwo) =
        (ExteriorAlgebra.ι R leftTwo * ExteriorAlgebra.ι R rightTwo) *
          ExteriorAlgebra.ι R leftOne := by
    simpa [exteriorElementary] using
      iota_mul_exteriorElementary_two (R := R) leftOne [leftTwo, rightTwo]
  have hright :
      ExteriorAlgebra.ι R rightOne *
          (ExteriorAlgebra.ι R leftTwo * ExteriorAlgebra.ι R rightTwo) =
        (ExteriorAlgebra.ι R leftTwo * ExteriorAlgebra.ι R rightTwo) *
          ExteriorAlgebra.ι R rightOne := by
    simpa [exteriorElementary] using
      iota_mul_exteriorElementary_two (R := R) rightOne [leftTwo, rightTwo]
  calc
    (ExteriorAlgebra.ι R leftOne * ExteriorAlgebra.ι R rightOne) *
        (ExteriorAlgebra.ι R leftTwo * ExteriorAlgebra.ι R rightTwo) =
      ExteriorAlgebra.ι R leftOne *
        (ExteriorAlgebra.ι R rightOne *
          (ExteriorAlgebra.ι R leftTwo * ExteriorAlgebra.ι R rightTwo)) := by
            rw [mul_assoc]
    _ = ExteriorAlgebra.ι R leftOne *
        ((ExteriorAlgebra.ι R leftTwo * ExteriorAlgebra.ι R rightTwo) *
          ExteriorAlgebra.ι R rightOne) := by rw [hright]
    _ = (ExteriorAlgebra.ι R leftOne *
        (ExteriorAlgebra.ι R leftTwo * ExteriorAlgebra.ι R rightTwo)) *
          ExteriorAlgebra.ι R rightOne := by rw [← mul_assoc]
    _ = ((ExteriorAlgebra.ι R leftTwo * ExteriorAlgebra.ι R rightTwo) *
        ExteriorAlgebra.ι R leftOne) * ExteriorAlgebra.ι R rightOne := by
          rw [hleft]
    _ = (ExteriorAlgebra.ι R leftTwo * ExteriorAlgebra.ι R rightTwo) *
        (ExteriorAlgebra.ι R leftOne * ExteriorAlgebra.ι R rightOne) := by
          rw [mul_assoc]

noncomputable def exteriorIotaPairList
    {dimension : ℕ} (left right : Fin dimension → M) :
    List (ExteriorAlgebra R M) :=
  List.ofFn fun index =>
    ExteriorAlgebra.ι R (left index) * ExteriorAlgebra.ι R (right index)

theorem exteriorIotaPairList_sum_pow
    {dimension : ℕ} (left right : Fin dimension → M) :
    (exteriorIotaPairList (R := R) left right).sum ^ dimension =
      (dimension.factorial : R) •
        (exteriorIotaPairList (R := R) left right).prod := by
  have hlength : (exteriorIotaPairList (R := R) left right).length =
      dimension := by simp [exteriorIotaPairList]
  have hpower := commuting_squareZero_list_sum_pow
    (exteriorIotaPairList (R := R) left right)
    (by
      intro value hvalue
      rw [exteriorIotaPairList, List.mem_ofFn] at hvalue
      obtain ⟨index, rfl⟩ := hvalue
      exact exterior_iota_pair_sq_zero (R := R) (left index) (right index))
    (by
      intro leftValue hleft rightValue hright
      rw [exteriorIotaPairList, List.mem_ofFn] at hleft hright
      obtain ⟨leftIndex, rfl⟩ := hleft
      obtain ⟨rightIndex, rfl⟩ := hright
      exact exterior_iota_pairs_commute (R := R)
        (left leftIndex) (right leftIndex)
        (left rightIndex) (right rightIndex))
  simpa only [hlength, Nat.cast_smul_eq_nsmul] using hpower

end FibonacciRibbonKernel
