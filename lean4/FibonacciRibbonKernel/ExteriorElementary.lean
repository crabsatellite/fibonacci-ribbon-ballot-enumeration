import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic.NoncommRing

namespace FibonacciRibbonKernel

open ExteriorAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Ordered elementary exterior sum over a list of vectors. -/
noncomputable def exteriorElementary : ℕ → List M → ExteriorAlgebra R M
  | 0, _ => 1
  | _ + 1, [] => 0
  | degree + 1, head :: tail =>
      ExteriorAlgebra.ι R head * exteriorElementary degree tail +
        exteriorElementary (degree + 1) tail

@[simp] theorem exteriorElementary_zero (vectors : List M) :
    exteriorElementary (R := R) 0 vectors = 1 := by
  simp [exteriorElementary]

@[simp] theorem exteriorElementary_nil_succ (degree : ℕ) :
    exteriorElementary (R := R) (degree + 1) ([] : List M) = 0 := rfl

@[simp] theorem exteriorElementary_cons_succ
    (degree : ℕ) (head : M) (tail : List M) :
    exteriorElementary (R := R) (degree + 1) (head :: tail) =
      ExteriorAlgebra.ι R head * exteriorElementary degree tail +
        exteriorElementary (degree + 1) tail := rfl

@[simp] theorem exteriorElementary_cons_one (head : M) (tail : List M) :
    exteriorElementary (R := R) 1 (head :: tail) =
      ExteriorAlgebra.ι R head + exteriorElementary 1 tail := by
  simp [exteriorElementary]

@[simp] theorem exteriorElementary_cons_two (head : M) (tail : List M) :
    exteriorElementary (R := R) 2 (head :: tail) =
      ExteriorAlgebra.ι R head * exteriorElementary 1 tail +
        exteriorElementary 2 tail := by
  simp [exteriorElementary]

@[simp] theorem exteriorElementary_cons_three (head : M) (tail : List M) :
    exteriorElementary (R := R) 3 (head :: tail) =
      ExteriorAlgebra.ι R head * exteriorElementary 2 tail +
        exteriorElementary 3 tail := by
  simp [exteriorElementary]

@[simp] theorem exteriorElementary_cons_four (head : M) (tail : List M) :
    exteriorElementary (R := R) 4 (head :: tail) =
      ExteriorAlgebra.ι R head * exteriorElementary 3 tail +
        exteriorElementary 4 tail := by
  simp [exteriorElementary]

@[simp] theorem exteriorElementary_cons_five (head : M) (tail : List M) :
    exteriorElementary (R := R) 5 (head :: tail) =
      ExteriorAlgebra.ι R head * exteriorElementary 4 tail +
        exteriorElementary 5 tail := by
  simp [exteriorElementary]

@[simp] theorem exteriorElementary_cons_six (head : M) (tail : List M) :
    exteriorElementary (R := R) 6 (head :: tail) =
      ExteriorAlgebra.ι R head * exteriorElementary 5 tail +
        exteriorElementary 6 tail := by
  simp [exteriorElementary]

theorem iota_mul_iota_neg (left right : M) :
    ExteriorAlgebra.ι R left * ExteriorAlgebra.ι R right =
      -(ExteriorAlgebra.ι R right * ExteriorAlgebra.ι R left) := by
  have h := ExteriorAlgebra.ι_add_mul_swap (R := R) left right
  exact eq_neg_of_add_eq_zero_left h

@[simp] theorem iota_mul_iota_mul_zero (vector : M)
    (element : ExteriorAlgebra R M) :
    ExteriorAlgebra.ι R vector *
        (ExteriorAlgebra.ι R vector * element) = 0 := by
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

theorem iota_mul_exteriorElementary_one
    (vector : M) (vectors : List M) :
    ExteriorAlgebra.ι R vector * exteriorElementary 1 vectors =
      -(exteriorElementary 1 vectors * ExteriorAlgebra.ι R vector) := by
  induction vectors with
  | nil => simp
  | cons head tail ih =>
      rw [exteriorElementary_cons_one]
      rw [mul_add, add_mul,
        iota_mul_iota_neg, ih]
      abel

theorem iota_mul_exteriorElementary_two
    (vector : M) (vectors : List M) :
    ExteriorAlgebra.ι R vector * exteriorElementary 2 vectors =
      exteriorElementary 2 vectors * ExteriorAlgebra.ι R vector := by
  induction vectors with
  | nil => simp
  | cons head tail ih =>
      have hhead := iota_mul_exteriorElementary_one (R := R) head tail
      have hvector := iota_mul_exteriorElementary_one (R := R) vector tail
      have hswap :
          ExteriorAlgebra.ι R head *
              (ExteriorAlgebra.ι R vector * exteriorElementary 1 tail) =
            exteriorElementary 1 tail *
              (ExteriorAlgebra.ι R head * ExteriorAlgebra.ι R vector) := by
        calc
          _ = ExteriorAlgebra.ι R head *
              (-(exteriorElementary 1 tail * ExteriorAlgebra.ι R vector)) := by rw [hvector]
          _ = -(ExteriorAlgebra.ι R head * exteriorElementary 1 tail) *
              ExteriorAlgebra.ι R vector := by noncomm_ring
          _ = -(-(exteriorElementary 1 tail * ExteriorAlgebra.ι R head)) *
              ExteriorAlgebra.ι R vector := by rw [hhead]
          _ = _ := by noncomm_ring
      have hswapAssoc :
          (ExteriorAlgebra.ι R head * ExteriorAlgebra.ι R vector) *
              exteriorElementary 1 tail =
            exteriorElementary 1 tail *
              (ExteriorAlgebra.ι R head * ExteriorAlgebra.ι R vector) := by
        simpa only [mul_assoc] using hswap
      rw [exteriorElementary_cons_two]
      rw [mul_add, add_mul,
        ← mul_assoc, iota_mul_iota_neg,
        iota_mul_exteriorElementary_one, ih]
      simp only [neg_mul]
      rw [hswapAssoc]
      simp only [mul_assoc]

theorem iota_mul_exteriorElementary_three
    (vector : M) (vectors : List M) :
    ExteriorAlgebra.ι R vector * exteriorElementary 3 vectors =
      -(exteriorElementary 3 vectors * ExteriorAlgebra.ι R vector) := by
  induction vectors with
  | nil => simp
  | cons head tail ih =>
      have hhead := iota_mul_exteriorElementary_two (R := R) head tail
      have hvector := iota_mul_exteriorElementary_two (R := R) vector tail
      have hswap :
          ExteriorAlgebra.ι R head *
              (ExteriorAlgebra.ι R vector * exteriorElementary 2 tail) =
            exteriorElementary 2 tail *
              (ExteriorAlgebra.ι R head * ExteriorAlgebra.ι R vector) := by
        calc
          _ = ExteriorAlgebra.ι R head *
              (exteriorElementary 2 tail * ExteriorAlgebra.ι R vector) := by rw [hvector]
          _ = (ExteriorAlgebra.ι R head * exteriorElementary 2 tail) *
              ExteriorAlgebra.ι R vector := by rw [mul_assoc]
          _ = (exteriorElementary 2 tail * ExteriorAlgebra.ι R head) *
              ExteriorAlgebra.ι R vector := by rw [hhead]
          _ = _ := by rw [mul_assoc]
      have hswapAssoc :
          (ExteriorAlgebra.ι R head * ExteriorAlgebra.ι R vector) *
              exteriorElementary 2 tail =
            exteriorElementary 2 tail *
              (ExteriorAlgebra.ι R head * ExteriorAlgebra.ι R vector) := by
        simpa only [mul_assoc] using hswap
      rw [exteriorElementary_cons_three]
      rw [mul_add, add_mul,
        ← mul_assoc, iota_mul_iota_neg,
        iota_mul_exteriorElementary_two, ih]
      simp only [neg_mul]
      rw [hswapAssoc]
      simp only [mul_assoc]
      abel

theorem iota_mul_exteriorElementary_four
    (vector : M) (vectors : List M) :
    ExteriorAlgebra.ι R vector * exteriorElementary 4 vectors =
      exteriorElementary 4 vectors * ExteriorAlgebra.ι R vector := by
  induction vectors with
  | nil => simp
  | cons head tail ih =>
      have hhead := iota_mul_exteriorElementary_three (R := R) head tail
      have hvector := iota_mul_exteriorElementary_three (R := R) vector tail
      have hswap :
          ExteriorAlgebra.ι R head *
              (ExteriorAlgebra.ι R vector * exteriorElementary 3 tail) =
            exteriorElementary 3 tail *
              (ExteriorAlgebra.ι R head * ExteriorAlgebra.ι R vector) := by
        calc
          _ = ExteriorAlgebra.ι R head *
              (-(exteriorElementary 3 tail * ExteriorAlgebra.ι R vector)) := by rw [hvector]
          _ = -(ExteriorAlgebra.ι R head * exteriorElementary 3 tail) *
              ExteriorAlgebra.ι R vector := by noncomm_ring
          _ = -(-(exteriorElementary 3 tail * ExteriorAlgebra.ι R head)) *
              ExteriorAlgebra.ι R vector := by rw [hhead]
          _ = _ := by noncomm_ring
      have hswapAssoc :
          (ExteriorAlgebra.ι R head * ExteriorAlgebra.ι R vector) *
              exteriorElementary 3 tail =
            exteriorElementary 3 tail *
              (ExteriorAlgebra.ι R head * ExteriorAlgebra.ι R vector) := by
        simpa only [mul_assoc] using hswap
      rw [exteriorElementary_cons_four]
      rw [mul_add, add_mul,
        ← mul_assoc, iota_mul_iota_neg,
        iota_mul_exteriorElementary_three, ih]
      simp only [neg_mul]
      rw [hswapAssoc]
      simp only [mul_assoc]

theorem exteriorElementary_one_sq_zero (vectors : List M) :
    exteriorElementary (R := R) 1 vectors ^ 2 = 0 := by
  induction vectors with
  | nil => simp
  | cons head tail ih =>
      have hcomm := iota_mul_exteriorElementary_one (R := R) head tail
      rw [exteriorElementary_cons_one]
      rw [pow_two, add_mul, mul_add, ExteriorAlgebra.ι_sq_zero]
      simp only [zero_add]
      rw [hcomm]
      simp_rw [mul_add]
      have ih' : exteriorElementary (R := R) 1 tail *
          exteriorElementary 1 tail = 0 := by simpa [pow_two] using ih
      rw [ih']
      abel

theorem exteriorElementary_one_mul_two (vectors : List M) :
    exteriorElementary (R := R) 1 vectors * exteriorElementary 2 vectors =
      exteriorElementary 3 vectors := by
  induction vectors with
  | nil => simp
  | cons head tail ih =>
      have hcomm := iota_mul_exteriorElementary_one (R := R) head tail
      have hcommRight : exteriorElementary (R := R) 1 tail *
          ExteriorAlgebra.ι R head =
        -(ExteriorAlgebra.ι R head * exteriorElementary 1 tail) := by
        have hneg := congrArg Neg.neg hcomm
        simpa only [neg_neg] using hneg.symm
      have hsquare : exteriorElementary (R := R) 1 tail *
          exteriorElementary 1 tail = 0 := by
        simpa [pow_two] using exteriorElementary_one_sq_zero (R := R) tail
      have hcross : exteriorElementary (R := R) 1 tail *
          (ExteriorAlgebra.ι R head * exteriorElementary 1 tail) = 0 := by
        calc
          _ = (exteriorElementary 1 tail * ExteriorAlgebra.ι R head) *
              exteriorElementary 1 tail := by rw [mul_assoc]
          _ = (-(ExteriorAlgebra.ι R head * exteriorElementary 1 tail)) *
              exteriorElementary 1 tail := by rw [hcommRight]
          _ = -(ExteriorAlgebra.ι R head) *
              (exteriorElementary 1 tail * exteriorElementary 1 tail) := by
                noncomm_ring
          _ = 0 := by rw [hsquare]; simp
      rw [exteriorElementary_cons_one, exteriorElementary_cons_two,
        exteriorElementary_cons_three]
      simp_rw [add_mul, mul_add]
      rw [iota_mul_iota_mul_zero, hcross, ih]
      simp

theorem exteriorElementary_two_mul_one (vectors : List M) :
    exteriorElementary (R := R) 2 vectors * exteriorElementary 1 vectors =
      exteriorElementary 3 vectors := by
  induction vectors with
  | nil => simp
  | cons head tail ih =>
      have hcommOne := iota_mul_exteriorElementary_one (R := R) head tail
      have hcommOneRight : exteriorElementary (R := R) 1 tail *
          ExteriorAlgebra.ι R head =
        -(ExteriorAlgebra.ι R head * exteriorElementary 1 tail) := by
        have hneg := congrArg Neg.neg hcommOne
        simpa only [neg_neg] using hneg.symm
      have hcommTwo := iota_mul_exteriorElementary_two (R := R) head tail
      have hsquare : exteriorElementary (R := R) 1 tail *
          exteriorElementary 1 tail = 0 := by
        simpa [pow_two] using exteriorElementary_one_sq_zero (R := R) tail
      have hfirst :
          (ExteriorAlgebra.ι R head * exteriorElementary 1 tail) *
              ExteriorAlgebra.ι R head = 0 := by
        calc
          _ = ExteriorAlgebra.ι R head *
              (exteriorElementary 1 tail * ExteriorAlgebra.ι R head) := by
                rw [mul_assoc]
          _ = ExteriorAlgebra.ι R head *
              (-(ExteriorAlgebra.ι R head * exteriorElementary 1 tail)) := by
                rw [hcommOneRight]
          _ = 0 := by rw [mul_neg, iota_mul_iota_mul_zero, neg_zero]
      have hsecond :
          (ExteriorAlgebra.ι R head * exteriorElementary 1 tail) *
              exteriorElementary 1 tail = 0 := by
        rw [mul_assoc, hsquare, mul_zero]
      rw [exteriorElementary_cons_two, exteriorElementary_cons_one,
        exteriorElementary_cons_three]
      simp_rw [add_mul, mul_add]
      rw [hfirst, hsecond, hcommTwo, ih]
      simp

theorem exteriorElementary_two_sq (vectors : List M) :
    exteriorElementary (R := R) 2 vectors ^ 2 =
      2 * exteriorElementary 4 vectors := by
  induction vectors with
  | nil => simp
  | cons head tail ih =>
      have hcommOneRight : exteriorElementary (R := R) 1 tail *
          ExteriorAlgebra.ι R head =
        -(ExteriorAlgebra.ι R head * exteriorElementary 1 tail) := by
        have hcomm := iota_mul_exteriorElementary_one (R := R) head tail
        have hneg := congrArg Neg.neg hcomm
        simpa only [neg_neg] using hneg.symm
      have hcommTwo := iota_mul_exteriorElementary_two (R := R) head tail
      have hsquare : exteriorElementary (R := R) 1 tail *
          exteriorElementary 1 tail = 0 := by
        simpa [pow_two] using exteriorElementary_one_sq_zero (R := R) tail
      have hfirst :
          (ExteriorAlgebra.ι R head * exteriorElementary 1 tail) *
              (ExteriorAlgebra.ι R head * exteriorElementary 1 tail) = 0 := by
        calc
          _ = ExteriorAlgebra.ι R head *
              (exteriorElementary 1 tail * ExteriorAlgebra.ι R head) *
                exteriorElementary 1 tail := by noncomm_ring
          _ = ExteriorAlgebra.ι R head *
              (-(ExteriorAlgebra.ι R head * exteriorElementary 1 tail)) *
                exteriorElementary 1 tail := by rw [hcommOneRight]
          _ = 0 := by rw [mul_neg, iota_mul_iota_mul_zero, neg_zero,
            zero_mul]
      have hcrossLeft :
          (ExteriorAlgebra.ι R head * exteriorElementary 1 tail) *
              exteriorElementary 2 tail =
            ExteriorAlgebra.ι R head * exteriorElementary 3 tail := by
        rw [mul_assoc, exteriorElementary_one_mul_two]
      have hcrossRight :
          exteriorElementary (R := R) 2 tail *
              (ExteriorAlgebra.ι R head * exteriorElementary 1 tail) =
            ExteriorAlgebra.ι R head * exteriorElementary 3 tail := by
        rw [← mul_assoc, ← hcommTwo, mul_assoc,
          exteriorElementary_two_mul_one]
      have ih' : exteriorElementary (R := R) 2 tail *
          exteriorElementary 2 tail = 2 * exteriorElementary 4 tail := by
        simpa [pow_two] using ih
      rw [exteriorElementary_cons_two, exteriorElementary_cons_four]
      rw [pow_two]
      simp_rw [add_mul, mul_add]
      rw [hfirst, hcrossLeft, hcrossRight, ih']
      noncomm_ring

theorem exteriorElementary_three_mul_one_zero (vectors : List M) :
    exteriorElementary (R := R) 3 vectors * exteriorElementary 1 vectors = 0 := by
  induction vectors with
  | nil => simp
  | cons head tail ih =>
      have hcommTwo := iota_mul_exteriorElementary_two (R := R) head tail
      have hcommThree := iota_mul_exteriorElementary_three (R := R) head tail
      have hfirst :
          (ExteriorAlgebra.ι R head * exteriorElementary 2 tail) *
              ExteriorAlgebra.ι R head = 0 := by
        calc
          _ = ExteriorAlgebra.ι R head *
              (exteriorElementary 2 tail * ExteriorAlgebra.ι R head) := by
                rw [mul_assoc]
          _ = ExteriorAlgebra.ι R head *
              (ExteriorAlgebra.ι R head * exteriorElementary 2 tail) := by
                rw [← hcommTwo]
          _ = 0 := iota_mul_iota_mul_zero head _
      have hsecond :
          (ExteriorAlgebra.ι R head * exteriorElementary 2 tail) *
              exteriorElementary 1 tail =
            ExteriorAlgebra.ι R head * exteriorElementary 3 tail := by
        rw [mul_assoc, exteriorElementary_two_mul_one]
      rw [exteriorElementary_cons_three, exteriorElementary_cons_one]
      simp_rw [add_mul, mul_add]
      rw [hfirst, hsecond, hcommThree, ih]
      abel

theorem exteriorElementary_four_mul_one (vectors : List M) :
    exteriorElementary (R := R) 4 vectors * exteriorElementary 1 vectors =
      exteriorElementary 5 vectors := by
  induction vectors with
  | nil => simp
  | cons head tail ih =>
      have hcommThreeRight : exteriorElementary (R := R) 3 tail *
          ExteriorAlgebra.ι R head =
        -(ExteriorAlgebra.ι R head * exteriorElementary 3 tail) := by
        have hcomm := iota_mul_exteriorElementary_three (R := R) head tail
        have hneg := congrArg Neg.neg hcomm
        simpa only [neg_neg] using hneg.symm
      have hcommFour := iota_mul_exteriorElementary_four (R := R) head tail
      have hfirst :
          (ExteriorAlgebra.ι R head * exteriorElementary 3 tail) *
              ExteriorAlgebra.ι R head = 0 := by
        calc
          _ = ExteriorAlgebra.ι R head *
              (exteriorElementary 3 tail * ExteriorAlgebra.ι R head) := by
                rw [mul_assoc]
          _ = ExteriorAlgebra.ι R head *
              (-(ExteriorAlgebra.ι R head * exteriorElementary 3 tail)) := by
                rw [hcommThreeRight]
          _ = 0 := by rw [mul_neg, iota_mul_iota_mul_zero, neg_zero]
      have hsecond :
          (ExteriorAlgebra.ι R head * exteriorElementary 3 tail) *
              exteriorElementary 1 tail = 0 := by
        rw [mul_assoc, exteriorElementary_three_mul_one_zero, mul_zero]
      rw [exteriorElementary_cons_four, exteriorElementary_cons_one,
        exteriorElementary_cons_five]
      simp_rw [add_mul, mul_add]
      rw [hfirst, hsecond, hcommFour, ih]
      simp

theorem exteriorElementary_three_mul_two (vectors : List M) :
    exteriorElementary (R := R) 3 vectors * exteriorElementary 2 vectors =
      2 * exteriorElementary 5 vectors := by
  induction vectors with
  | nil => simp
  | cons head tail ih =>
      have hcommOneRight : exteriorElementary (R := R) 1 tail *
          ExteriorAlgebra.ι R head =
        -(ExteriorAlgebra.ι R head * exteriorElementary 1 tail) := by
        have hcomm := iota_mul_exteriorElementary_one (R := R) head tail
        have hneg := congrArg Neg.neg hcomm
        simpa only [neg_neg] using hneg.symm
      have hcommTwo := iota_mul_exteriorElementary_two (R := R) head tail
      have hfirst :
          (ExteriorAlgebra.ι R head * exteriorElementary 2 tail) *
              (ExteriorAlgebra.ι R head * exteriorElementary 1 tail) = 0 := by
        calc
          _ = ExteriorAlgebra.ι R head *
              (exteriorElementary 2 tail * ExteriorAlgebra.ι R head) *
                exteriorElementary 1 tail := by noncomm_ring
          _ = ExteriorAlgebra.ι R head *
              (ExteriorAlgebra.ι R head * exteriorElementary 2 tail) *
                exteriorElementary 1 tail := by rw [← hcommTwo]
          _ = 0 := by rw [iota_mul_iota_mul_zero, zero_mul]
      have hcross :
          (ExteriorAlgebra.ι R head * exteriorElementary 2 tail) *
              exteriorElementary 2 tail =
            2 * (ExteriorAlgebra.ι R head * exteriorElementary 4 tail) := by
        rw [mul_assoc, show exteriorElementary (R := R) 2 tail *
            exteriorElementary 2 tail = exteriorElementary 2 tail ^ 2 by
              rw [pow_two],
          exteriorElementary_two_sq]
        noncomm_ring
      have hother : exteriorElementary (R := R) 3 tail *
          (ExteriorAlgebra.ι R head * exteriorElementary 1 tail) = 0 := by
        calc
          _ = (exteriorElementary 3 tail * ExteriorAlgebra.ι R head) *
              exteriorElementary 1 tail := by rw [mul_assoc]
          _ = (-(ExteriorAlgebra.ι R head * exteriorElementary 3 tail)) *
              exteriorElementary 1 tail := by
                rw [show exteriorElementary (R := R) 3 tail *
                    ExteriorAlgebra.ι R head =
                  -(ExteriorAlgebra.ι R head * exteriorElementary 3 tail) by
                    have h := iota_mul_exteriorElementary_three
                      (R := R) head tail
                    have hneg := congrArg Neg.neg h
                    simpa only [neg_neg] using hneg.symm]
          _ = 0 := by
            rw [neg_mul, mul_assoc,
              exteriorElementary_three_mul_one_zero, mul_zero, neg_zero]
      rw [exteriorElementary_cons_three, exteriorElementary_cons_two,
        exteriorElementary_cons_five]
      simp_rw [add_mul, mul_add]
      rw [hfirst, hcross, hother, ih]
      noncomm_ring

theorem exteriorElementary_four_mul_two (vectors : List M) :
    exteriorElementary (R := R) 4 vectors * exteriorElementary 2 vectors =
      3 * exteriorElementary 6 vectors := by
  induction vectors with
  | nil => simp
  | cons head tail ih =>
      have hcommOneRight : exteriorElementary (R := R) 1 tail *
          ExteriorAlgebra.ι R head =
        -(ExteriorAlgebra.ι R head * exteriorElementary 1 tail) := by
        have hcomm := iota_mul_exteriorElementary_one (R := R) head tail
        have hneg := congrArg Neg.neg hcomm
        simpa only [neg_neg] using hneg.symm
      have hcommFour := iota_mul_exteriorElementary_four (R := R) head tail
      have hfirst :
          (ExteriorAlgebra.ι R head * exteriorElementary 3 tail) *
              (ExteriorAlgebra.ι R head * exteriorElementary 1 tail) = 0 := by
        calc
          _ = ExteriorAlgebra.ι R head *
              (exteriorElementary 3 tail * ExteriorAlgebra.ι R head) *
                exteriorElementary 1 tail := by noncomm_ring
          _ = ExteriorAlgebra.ι R head *
              (-(ExteriorAlgebra.ι R head * exteriorElementary 3 tail)) *
                exteriorElementary 1 tail := by
                rw [show exteriorElementary (R := R) 3 tail *
                    ExteriorAlgebra.ι R head =
                  -(ExteriorAlgebra.ι R head * exteriorElementary 3 tail) by
                    have h := iota_mul_exteriorElementary_three
                      (R := R) head tail
                    have hneg := congrArg Neg.neg h
                    simpa only [neg_neg] using hneg.symm]
          _ = 0 := by rw [mul_neg, iota_mul_iota_mul_zero, neg_zero,
            zero_mul]
      have hcross :
          (ExteriorAlgebra.ι R head * exteriorElementary 3 tail) *
              exteriorElementary 2 tail =
            2 * (ExteriorAlgebra.ι R head * exteriorElementary 5 tail) := by
        rw [mul_assoc, exteriorElementary_three_mul_two]
        noncomm_ring
      have hother : exteriorElementary (R := R) 4 tail *
          (ExteriorAlgebra.ι R head * exteriorElementary 1 tail) =
        ExteriorAlgebra.ι R head * exteriorElementary 5 tail := by
        calc
          _ = (exteriorElementary 4 tail * ExteriorAlgebra.ι R head) *
              exteriorElementary 1 tail := by rw [mul_assoc]
          _ = (ExteriorAlgebra.ι R head * exteriorElementary 4 tail) *
              exteriorElementary 1 tail := by rw [← hcommFour]
          _ = _ := by rw [mul_assoc, exteriorElementary_four_mul_one]
      rw [exteriorElementary_cons_four, exteriorElementary_cons_two,
        exteriorElementary_cons_six]
      simp_rw [add_mul, mul_add]
      rw [hfirst, hcross, hother, ih]
      noncomm_ring

theorem exteriorElementary_two_cube (vectors : List M) :
    exteriorElementary (R := R) 2 vectors ^ 3 =
      6 * exteriorElementary 6 vectors := by
  rw [show (3 : ℕ) = 2 + 1 by omega, pow_succ,
    exteriorElementary_two_sq]
  rw [mul_assoc, exteriorElementary_four_mul_two]
  noncomm_ring

/-- Five-vector minor-summation identity inside the exterior algebra. -/
theorem exterior_minor_sum_five (vectors : List M) :
    exteriorElementary (R := R) 2 vectors ^ 2 *
        exteriorElementary 1 vectors =
      2 * exteriorElementary 5 vectors := by
  rw [exteriorElementary_two_sq, mul_assoc,
    exteriorElementary_four_mul_one]

end FibonacciRibbonKernel
