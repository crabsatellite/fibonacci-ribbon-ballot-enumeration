import FibonacciRibbonKernel.IntegerCosineMomentRecurrence

namespace FibonacciRibbonKernel

open PowerSeries

theorem derivative_literalBesselJ_succ
    (order : ℕ) :
    PowerSeries.derivative ℚ (literalBesselJ (order + 1)) =
      literalBesselJ order + literalBesselJ (order + 2) := by
  ext degree
  rw [map_add, PowerSeries.coeff_derivative]
  by_cases hdegree : ∃ index : ℕ, degree = 2 * index + order
  · obtain ⟨index, rfl⟩ := hdegree
    cases index with
    | zero =>
        rw [show 2 * 0 + order + 1 = 2 * 0 + (order + 1) by omega,
          literalBesselJ_coeff_of_eq (order + 1) 0,
          literalBesselJ_coeff_of_eq order 0]
        have hhigh : ¬ ∃ candidate : ℕ,
            order = 2 * candidate + (order + 2) := by
          rintro ⟨candidate, heq⟩
          omega
        rw [show 2 * 0 + order = order by omega,
          literalBesselJ_coeff_eq_zero (order + 2) order hhigh]
        norm_num [Nat.factorial_zero]
        have hfactorial : (order.factorial : ℚ) ≠ 0 := by positivity
        rw [Nat.factorial_succ]
        push_cast
        field_simp
    | succ index =>
        have hdegreeLhs :
            2 * (index + 1) + order + 1 =
              2 * (index + 1) + (order + 1) := by omega
        rw [hdegreeLhs,
          literalBesselJ_coeff_of_eq (order + 1) (index + 1),
          literalBesselJ_coeff_of_eq order (index + 1)]
        have hdegreeHigh :
            2 * (index + 1) + order = 2 * index + (order + 2) := by omega
        rw [hdegreeHigh,
          literalBesselJ_coeff_of_eq (order + 2) index]
        rw [show index + 1 + (order + 1) =
            (index + order + 1) + 1 by omega,
          show index + 1 + order = index + order + 1 by omega,
          show index + (order + 2) = (index + order + 1) + 1 by omega,
          Nat.factorial_succ index,
          Nat.factorial_succ (index + order + 1)]
        push_cast
        have hindexFactorial : (index.factorial : ℚ) ≠ 0 := by positivity
        have hrightFactorial : ((index + order + 1).factorial : ℚ) ≠ 0 := by
          positivity
        field_simp
        ring
  · have hleft : ¬ ∃ index : ℕ,
        degree + 1 = 2 * index + (order + 1) := by
      rintro ⟨index, heq⟩
      apply hdegree
      exact ⟨index, by omega⟩
    have hhigh : ¬ ∃ index : ℕ,
        degree = 2 * index + (order + 2) := by
      rintro ⟨index, heq⟩
      apply hdegree
      exact ⟨index + 1, by omega⟩
    rw [literalBesselJ_coeff_eq_zero (order + 1) (degree + 1) hleft,
      literalBesselJ_coeff_eq_zero order degree hdegree,
      literalBesselJ_coeff_eq_zero (order + 2) degree hhigh]
    ring

theorem derivative_literalBesselJ_zero :
    PowerSeries.derivative ℚ (literalBesselJ 0) =
      2 * literalBesselJ 1 := by
  ext degree
  rw [PowerSeries.coeff_derivative]
  have htwo : (2 : ℚ⟦X⟧) = PowerSeries.C (2 : ℚ) :=
    (map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 2).symm
  rw [htwo, PowerSeries.coeff_C_mul]
  by_cases hdegree : ∃ index : ℕ, degree = 2 * index + 1
  · obtain ⟨index, rfl⟩ := hdegree
    have heq : 2 * index + 1 + 1 = 2 * (index + 1) + 0 := by omega
    rw [heq, literalBesselJ_coeff_of_eq 0 (index + 1),
      literalBesselJ_coeff_of_eq 1 index]
    rw [Nat.factorial_succ]
    push_cast
    have hfactorial : (index.factorial : ℚ) ≠ 0 := by positivity
    field_simp
    ring
  · have hleft : ¬ ∃ index : ℕ,
        degree + 1 = 2 * index + 0 := by
      rintro ⟨index, heq⟩
      rcases index with _ | index
      · omega
      · apply hdegree
        exact ⟨index, by omega⟩
    rw [literalBesselJ_coeff_eq_zero 0 (degree + 1) hleft,
      literalBesselJ_coeff_eq_zero 1 degree hdegree]
    ring

end FibonacciRibbonKernel
