import FibonacciRibbonKernel.ExteriorElementary
import FibonacciRibbonKernel.NilpotentBinomial

namespace FibonacciRibbonKernel

open ExteriorAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem exterior_cross_sq_zero (head : M) (tail : List M) :
    (ExteriorAlgebra.ι R head * exteriorElementary 1 tail) *
        (ExteriorAlgebra.ι R head * exteriorElementary 1 tail) = 0 := by
  have hswap := iota_mul_exteriorElementary_one (R := R) head tail
  have hswapRight : exteriorElementary (R := R) 1 tail *
      ExteriorAlgebra.ι R head =
        -(ExteriorAlgebra.ι R head * exteriorElementary 1 tail) := by
    have hneg := congrArg Neg.neg hswap
    simpa only [neg_neg] using hneg.symm
  calc
    (ExteriorAlgebra.ι R head * exteriorElementary 1 tail) *
        (ExteriorAlgebra.ι R head * exteriorElementary 1 tail) =
      (ExteriorAlgebra.ι R head *
        (exteriorElementary 1 tail * ExteriorAlgebra.ι R head)) *
          exteriorElementary 1 tail := by noncomm_ring
    _ = (ExteriorAlgebra.ι R head *
        (-(ExteriorAlgebra.ι R head * exteriorElementary 1 tail))) *
          exteriorElementary 1 tail := by rw [hswapRight]
    _ = 0 := by
      rw [show ExteriorAlgebra.ι R head *
          (-(ExteriorAlgebra.ι R head * exteriorElementary 1 tail)) = 0 by
        rw [mul_neg, ← mul_assoc, ExteriorAlgebra.ι_sq_zero,
          zero_mul, neg_zero], zero_mul]

theorem exterior_cross_commutes_two (head : M) (tail : List M) :
    Commute
      (ExteriorAlgebra.ι R head * exteriorElementary 1 tail)
      (exteriorElementary 2 tail) := by
  apply Commute.eq
  have hhead := iota_mul_exteriorElementary_two (R := R) head tail
  have hpair : exteriorElementary (R := R) 1 tail * exteriorElementary 2 tail =
      exteriorElementary 2 tail * exteriorElementary 1 tail := by
    rw [exteriorElementary_one_mul_two, exteriorElementary_two_mul_one]
  calc
    (ExteriorAlgebra.ι R head * exteriorElementary 1 tail) *
        exteriorElementary 2 tail =
      ExteriorAlgebra.ι R head *
        (exteriorElementary 1 tail * exteriorElementary 2 tail) := by
          rw [mul_assoc]
    _ = ExteriorAlgebra.ι R head *
        (exteriorElementary 2 tail * exteriorElementary 1 tail) := by rw [hpair]
    _ = (ExteriorAlgebra.ι R head * exteriorElementary 2 tail) *
        exteriorElementary 1 tail := by rw [mul_assoc]
    _ = (exteriorElementary 2 tail * ExteriorAlgebra.ι R head) *
        exteriorElementary 1 tail := by rw [hhead]
    _ = exteriorElementary 2 tail *
        (ExteriorAlgebra.ι R head * exteriorElementary 1 tail) := by
          rw [mul_assoc]

theorem exterior_pair_commutes_one (tail : List M) :
    Commute (exteriorElementary (R := R) 2 tail)
      (exteriorElementary 1 tail) := by
  change exteriorElementary (R := R) 2 tail * exteriorElementary 1 tail =
    exteriorElementary 1 tail * exteriorElementary 2 tail
  rw [exteriorElementary_two_mul_one, exteriorElementary_one_mul_two]

/-- Uniform even and odd divided-power identities. -/
theorem exteriorElementary_divided_powers (vectors : List M) (degree : ℕ) :
    exteriorElementary (R := R) 2 vectors ^ degree =
        (degree.factorial : R) • exteriorElementary (2 * degree) vectors ∧
      exteriorElementary (R := R) 2 vectors ^ degree *
          exteriorElementary 1 vectors =
        (degree.factorial : R) • exteriorElementary (2 * degree + 1) vectors := by
  induction vectors generalizing degree with
  | nil =>
      cases degree with
      | zero => simp
      | succ degree =>
          have heven : 2 * (degree + 1) = (2 * degree + 1) + 1 := by omega
          rw [heven]
          simp [exteriorElementary]
  | cons head tail ih =>
      let cross := ExteriorAlgebra.ι R head * exteriorElementary 1 tail
      let pair := exteriorElementary (R := R) 2 tail
      have hcrossPair : Commute cross pair :=
        exterior_cross_commutes_two (R := R) head tail
      have hcrossSq : cross * cross = 0 :=
        exterior_cross_sq_zero (R := R) head tail
      have hpower := add_pow_of_commute_sq_zero cross pair
        hcrossPair hcrossSq degree
      have hpairOne : Commute pair (exteriorElementary (R := R) 1 tail) :=
        exterior_pair_commutes_one (R := R) tail
      have hheadPair : Commute (ExteriorAlgebra.ι R head) pair := by
        change ExteriorAlgebra.ι R head * exteriorElementary 2 tail =
          exteriorElementary 2 tail * ExteriorAlgebra.ι R head
        exact iota_mul_exteriorElementary_two (R := R) head tail
      constructor
      · cases degree with
        | zero => simp
        | succ degree =>
            have htailCurrent := (ih (degree + 1)).1
            have htailPrevious := (ih degree).2
            rw [exteriorElementary_cons_two]
            change (cross + pair) ^ (degree + 1) = _
            rw [hpower]
            rw [show degree + 1 - 1 = degree by omega]
            rw [htailCurrent]
            have hcrossPower : cross * pair ^ degree =
                ExteriorAlgebra.ι R head *
                  (pair ^ degree * exteriorElementary 1 tail) := by
              unfold cross
              rw [mul_assoc]
              rw [(hpairOne.pow_left degree).eq.symm]
            rw [hcrossPower, htailPrevious]
            have heven : 2 * (degree + 1) = (2 * degree + 1) + 1 := by omega
            rw [heven, exteriorElementary_cons_succ]
            rw [Nat.factorial_succ]
            push_cast
            rw [← Nat.cast_smul_eq_nsmul R (degree + 1)]
            simp only [mul_smul, smul_add, mul_smul_comm]
            module
      · rw [exteriorElementary_cons_two, exteriorElementary_cons_one]
        change (cross + pair) ^ degree *
            (ExteriorAlgebra.ι R head + exteriorElementary 1 tail) = _
        rw [hpower]
        simp only [add_mul, mul_add]
        have hpairHead : pair ^ degree * ExteriorAlgebra.ι R head =
            ExteriorAlgebra.ι R head * pair ^ degree :=
          (hheadPair.pow_right degree).eq.symm
        have hcrossHeadBase : cross * ExteriorAlgebra.ι R head = 0 := by
          unfold cross
          have hswap := iota_mul_exteriorElementary_one (R := R) head tail
          have hswapRight : exteriorElementary (R := R) 1 tail *
              ExteriorAlgebra.ι R head =
                -(ExteriorAlgebra.ι R head * exteriorElementary 1 tail) := by
            have hneg := congrArg Neg.neg hswap
            simpa only [neg_neg] using hneg.symm
          rw [mul_assoc, hswapRight, mul_neg, ← mul_assoc,
            ExteriorAlgebra.ι_sq_zero, zero_mul, neg_zero]
        have hcrossOneBase : cross * exteriorElementary 1 tail = 0 := by
          unfold cross
          rw [mul_assoc]
          have hsquare := exteriorElementary_one_sq_zero (R := R) tail
          rw [show exteriorElementary (R := R) 1 tail *
              exteriorElementary 1 tail = exteriorElementary 1 tail ^ 2 by
                rw [pow_two], hsquare, mul_zero]
        have hcrossHead : cross * pair ^ (degree - 1) *
            ExteriorAlgebra.ι R head = 0 := by
          have hcomm : pair ^ (degree - 1) * ExteriorAlgebra.ι R head =
              ExteriorAlgebra.ι R head * pair ^ (degree - 1) :=
            (hheadPair.pow_right (degree - 1)).eq.symm
          rw [mul_assoc, hcomm, ← mul_assoc, hcrossHeadBase, zero_mul]
        have hcrossOne : cross * pair ^ (degree - 1) *
            exteriorElementary 1 tail = 0 := by
          have hcomm : pair ^ (degree - 1) * exteriorElementary 1 tail =
              exteriorElementary 1 tail * pair ^ (degree - 1) :=
            (hpairOne.pow_left (degree - 1)).eq
          rw [mul_assoc, hcomm, ← mul_assoc, hcrossOneBase, zero_mul]
        have hcrossHeadNsmul : degree • (cross * pair ^ (degree - 1)) *
            ExteriorAlgebra.ι R head = 0 := by
          simp only [nsmul_eq_mul]
          rw [mul_assoc, hcrossHead, mul_zero]
        have hcrossOneNsmul : degree • (cross * pair ^ (degree - 1)) *
            exteriorElementary 1 tail = 0 := by
          simp only [nsmul_eq_mul]
          rw [mul_assoc, hcrossOne, mul_zero]
        rw [hpairHead]
        rw [hcrossHeadNsmul, hcrossOneNsmul]
        rw [(ih degree).2, (ih degree).1]
        have hodd : 2 * degree + 1 = (2 * degree) + 1 := rfl
        rw [hodd, exteriorElementary_cons_succ]
        rw [smul_add, mul_smul_comm]
        simp only [add_zero]

end FibonacciRibbonKernel
