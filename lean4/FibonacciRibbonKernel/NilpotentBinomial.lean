import Mathlib.Tactic.NoncommRing

namespace FibonacciRibbonKernel

theorem add_pow_of_commute_sq_zero
    {A : Type*} [Ring A] (left right : A)
    (hcommute : Commute left right) (hsquare : left * left = 0)
    (degree : ℕ) :
    (left + right) ^ degree =
      right ^ degree + degree • (left * right ^ (degree - 1)) := by
  induction degree with
  | zero => simp
  | succ degree ih =>
      cases degree with
      | zero =>
          simp
          abel
      | succ degree =>
          rw [pow_succ, ih]
          simp only [add_mul, mul_add]
          have hpow : right ^ (degree + 1) * left =
              left * right ^ (degree + 1) :=
            (hcommute.pow_right (degree + 1)).eq.symm
          have hprevious : right ^ degree * left = left * right ^ degree :=
            (hcommute.pow_right degree).eq.symm
          have hvanish : left * right ^ degree * left = 0 := by
            rw [mul_assoc, hprevious, ← mul_assoc, hsquare, zero_mul]
          rw [hpow]
          simp only [nsmul_eq_mul]
          rw [show degree + 1 - 1 = degree by omega]
          rw [show (↑(degree + 1) : A) * (left * right ^ degree) * left = 0 by
            rw [mul_assoc, hvanish, mul_zero]]
          simp only [pow_succ]
          rw [show degree + 1 + 1 - 1 = degree + 1 by omega]
          push_cast
          noncomm_ring

end FibonacciRibbonKernel
