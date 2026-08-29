import FibonacciRibbonKernel.BesselSignedOneFactorMoment

namespace FibonacciRibbonKernel

open PowerSeries
open scoped BigOperators

noncomputable def factorialScaledCoeffQ (series : ℚ⟦X⟧) (power : ℕ) : ℚ :=
  (power.factorial : ℚ) * PowerSeries.coeff power series

theorem factorialScaledCoeffQ_mul (left right : ℚ⟦X⟧) (power : ℕ) :
    factorialScaledCoeffQ (left * right) power =
      ∑ index : Fin (power + 1),
        (Nat.choose power index.val : ℚ) *
          factorialScaledCoeffQ left index.val *
          factorialScaledCoeffQ right (power - index.val) := by
  unfold factorialScaledCoeffQ
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _hindex
  have hindex : index.val ≤ power := by omega
  have hfactorialNat := Nat.choose_mul_factorial_mul_factorial hindex
  have hfactorial :
      (power.factorial : ℚ) =
        (Nat.choose power index.val : ℚ) *
          (index.val.factorial : ℚ) *
          ((power - index.val).factorial : ℚ) := by
    exact_mod_cast hfactorialNat.symm
  rw [hfactorial]
  ring

theorem factorialScaledCoeffQ_pow_succ
    (series : ℚ⟦X⟧) (factorCount power : ℕ) :
    factorialScaledCoeffQ (series ^ (factorCount + 1)) power =
      ∑ index : Fin (power + 1),
        (Nat.choose power index.val : ℚ) *
          factorialScaledCoeffQ (series ^ factorCount) index.val *
          factorialScaledCoeffQ series (power - index.val) := by
  rw [pow_succ, factorialScaledCoeffQ_mul]

end FibonacciRibbonKernel
