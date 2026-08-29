import FibonacciRibbonKernel.FivePairBoundaryGeneral

namespace FibonacciRibbonKernel

open PowerSeries

theorem pairBoundary_two_even_first (index : ℕ) :
    pairBoundary 2 (2 * index + 2) ((2 * index + 2) / 2 + 1) =
      1 / ((index.factorial : ℚ) ^ 2) := by
  unfold pairBoundary
  rw [show (2 * index + 2) / 2 + 1 = index + 2 by omega]
  rw [show (((index + 2 : ℕ) : ℤ) - ((2 : ℕ) : ℤ)) = (index : ℤ) by omega,
    show (((2 * index + 2 : ℕ) : ℤ) - ((index + 2 : ℕ) : ℤ)) =
      (index : ℤ) by omega]
  rw [show reciprocalFactorialInt (index : ℤ) =
      ((index.factorial : ℚ) : ℚ)⁻¹ by
        exact reciprocalFactorialInt_ofNat index]
  field_simp

theorem pairBoundary_two_even_second
    (index : ℕ) (hindex : 1 ≤ index) :
    pairBoundary 2 (2 * index + 2) ((2 * index + 2) / 2 + 2) =
      1 / (((index - 1).factorial : ℚ) * ((index + 1).factorial : ℚ)) := by
  unfold pairBoundary
  rw [show (2 * index + 2) / 2 + 2 = index + 3 by omega]
  rw [show (((index + 3 : ℕ) : ℤ) - ((2 : ℕ) : ℤ)) =
      ((index + 1 : ℕ) : ℤ) by omega,
    show (((2 * index + 2 : ℕ) : ℤ) - ((index + 3 : ℕ) : ℤ)) =
      ((index - 1 : ℕ) : ℤ) by omega]
  rw [show reciprocalFactorialInt ((index + 1 : ℕ) : ℤ) =
      (((index + 1).factorial : ℚ) : ℚ)⁻¹ by
        exact reciprocalFactorialInt_ofNat (index + 1),
    show reciprocalFactorialInt ((index - 1 : ℕ) : ℤ) =
      (((index - 1).factorial : ℚ) : ℚ)⁻¹ by
        exact reciprocalFactorialInt_ofNat (index - 1)]
  ring

theorem pairBoundary_two_odd_first (index : ℕ) :
    pairBoundary 2 (2 * index + 3) ((2 * index + 3) / 2 + 1) =
      1 / ((index.factorial : ℚ) * ((index + 1).factorial : ℚ)) := by
  unfold pairBoundary
  rw [show (2 * index + 3) / 2 + 1 = index + 2 by omega]
  rw [show (((index + 2 : ℕ) : ℤ) - ((2 : ℕ) : ℤ)) = (index : ℤ) by omega,
    show (((2 * index + 3 : ℕ) : ℤ) - ((index + 2 : ℕ) : ℤ)) =
      ((index + 1 : ℕ) : ℤ) by omega]
  rw [show reciprocalFactorialInt (index : ℤ) =
      ((index.factorial : ℚ) : ℚ)⁻¹ by
        exact reciprocalFactorialInt_ofNat index,
    show reciprocalFactorialInt ((index + 1 : ℕ) : ℤ) =
      (((index + 1).factorial : ℚ) : ℚ)⁻¹ by
        exact reciprocalFactorialInt_ofNat (index + 1)]
  ring

theorem pairBoundary_two_odd_second (index : ℕ) :
    pairBoundary 2 (2 * index + 3) ((2 * index + 3) / 2 + 2) =
      1 / ((index.factorial : ℚ) * ((index + 1).factorial : ℚ)) := by
  unfold pairBoundary
  rw [show (2 * index + 3) / 2 + 2 = index + 3 by omega]
  rw [show (((index + 3 : ℕ) : ℤ) - ((2 : ℕ) : ℤ)) =
      ((index + 1 : ℕ) : ℤ) by omega,
    show (((2 * index + 3 : ℕ) : ℤ) - ((index + 3 : ℕ) : ℤ)) =
      (index : ℤ) by omega]
  rw [show reciprocalFactorialInt ((index + 1 : ℕ) : ℤ) =
      (((index + 1).factorial : ℚ) : ℚ)⁻¹ by
        exact reciprocalFactorialInt_ofNat (index + 1),
    show reciprocalFactorialInt (index : ℤ) =
      ((index.factorial : ℚ) : ℚ)⁻¹ by
        exact reciprocalFactorialInt_ofNat index]
  ring

theorem sum_Ico_two_terms (function : ℕ → ℚ) (start : ℕ) :
    (∑ index ∈ Finset.Ico start (start + 2), function index) =
      function start + function (start + 1) := by
  have hfinset : Finset.Ico start (start + 2) = {start, start + 1} := by
    ext index
    simp
    omega
  rw [hfinset]
  simp

theorem fiveClosedPair_two_four_eq_bessel :
    fiveClosedPair 2 4 =
      X ^ 2 *
        (literalBesselJ 0 + 2 * literalBesselJ 1 + literalBesselJ 2) := by
  ext degree
  by_cases hsmall : degree < 2
  · interval_cases degree <;>
      norm_num [fiveClosedPair_coeff_formula, fiveFactorialScalarRow,
        reciprocalFactorialInt, Fin.rev, PowerSeries.coeff_X_pow_mul',
        Finset.sum_range_succ]
  · rw [PowerSeries.coeff_X_pow_mul', if_pos (by omega : 2 ≤ degree)]
    by_cases htailZero : degree - 2 = 0
    · have hdegreeTwo : degree = 2 := by
        omega
      subst degree
      norm_num [fiveClosedPair_coeff_formula, fiveFactorialScalarRow,
        reciprocalFactorialInt, Fin.rev, literalBesselJ_coeff_of_eq,
        Finset.sum_range_succ]
      have hJ0 := literalBesselJ_coeff_of_eq 0 0
      norm_num at hJ0
      have hJ1 := literalBesselJ_coeff_eq_zero 1 0 (by
          rintro ⟨candidate, heq⟩
          omega)
      have hJ2 := literalBesselJ_coeff_eq_zero 2 0 (by
          rintro ⟨candidate, heq⟩
          omega)
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply] at hJ1 hJ2
      rw [hJ0, hJ1, hJ2]
      norm_num
    · have hlarge : degree / 2 + 1 + 2 ≤ degree + 1 := by
        omega
      rw [fiveClosedPair_coeff_first_boundaries 2 degree 2
        (by decide) hlarge]
      rw [sum_Ico_two_terms]
      obtain ⟨index, htail | htail⟩ := Nat.even_or_odd' (degree - 2)
      · have hdegreeEven : degree = 2 * index + 2 := by omega
        rw [hdegreeEven]
        rw [show 2 * index + 2 - 2 = 2 * index by omega]
        rw [show (2 * index + 2) / 2 + 1 + 1 =
          (2 * index + 2) / 2 + 2 by omega]
        have hindex : 1 ≤ index := by omega
        rw [pairBoundary_two_even_first,
          pairBoundary_two_even_second index hindex]
        rw [map_add, map_add]
        rw [show (2 : ℚ⟦X⟧) = PowerSeries.C (2 : ℚ) by
          exact (map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 2).symm,
          PowerSeries.coeff_C_mul]
        have hJ0 := literalBesselJ_coeff_of_eq 0 index
        norm_num at hJ0
        rw [hJ0]
        rw [literalBesselJ_coeff_eq_zero 1 (2 * index) (by
          rintro ⟨candidate, heq⟩
          omega)]
        have hJ2 := literalBesselJ_coeff_of_eq 2 (index - 1)
        have hdegreeJ2 : 2 * (index - 1) + 2 = 2 * index := by omega
        rw [← hdegreeJ2, hJ2]
        rw [show index - 1 + 2 = index + 1 by omega]
        ring
      · have hdegreeOdd : degree = 2 * index + 3 := by omega
        rw [hdegreeOdd]
        rw [show 2 * index + 3 - 2 = 2 * index + 1 by omega]
        rw [show (2 * index + 3) / 2 + 1 + 1 =
          (2 * index + 3) / 2 + 2 by omega]
        rw [pairBoundary_two_odd_first,
          pairBoundary_two_odd_second]
        rw [map_add, map_add]
        rw [show (2 : ℚ⟦X⟧) = PowerSeries.C (2 : ℚ) by
          exact (map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 2).symm,
          PowerSeries.coeff_C_mul]
        rw [literalBesselJ_coeff_eq_zero 0 (2 * index + 1) (by
          rintro ⟨candidate, heq⟩
          omega)]
        have hJ1 := literalBesselJ_coeff_of_eq 1 index
        rw [hJ1]
        rw [literalBesselJ_coeff_eq_zero 2 (2 * index + 1) (by
          rintro ⟨candidate, heq⟩
          omega)]
        ring

end FibonacciRibbonKernel
