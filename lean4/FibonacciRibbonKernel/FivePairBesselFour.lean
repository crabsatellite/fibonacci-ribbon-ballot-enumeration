import FibonacciRibbonKernel.FivePairBesselThree

namespace FibonacciRibbonKernel

open PowerSeries

theorem sum_Ico_four_terms (function : ℕ → ℚ) (start : ℕ) :
    (∑ index ∈ Finset.Ico start (start + 4), function index) =
      function start + function (start + 1) +
        function (start + 2) + function (start + 3) := by
  have hfinset : Finset.Ico start (start + 4) =
      {start, start + 1, start + 2, start + 3} := by
    ext index
    simp
    omega
  rw [hfinset]
  simp
  ring

theorem fiveClosedPair_zero_four_eq_bessel :
    fiveClosedPair 0 4 =
      X ^ 4 *
        (literalBesselJ 0 + 2 * literalBesselJ 1 +
          2 * literalBesselJ 2 + 2 * literalBesselJ 3 +
          literalBesselJ 4) := by
  ext degree
  by_cases hsmall : degree < 4
  · interval_cases degree <;>
      norm_num [fiveClosedPair_coeff_formula, fiveFactorialScalarRow,
        reciprocalFactorialInt, Fin.rev, PowerSeries.coeff_X_pow_mul',
        Finset.sum_range_succ]
  · rw [PowerSeries.coeff_X_pow_mul', if_pos (by omega : 4 ≤ degree)]
    by_cases htailSmall : degree - 4 < 3
    · have hdegreeCases : degree = 4 ∨ degree = 5 ∨ degree = 6 := by omega
      rcases hdegreeCases with rfl | rfl | rfl
      · norm_num [fiveClosedPair_coeff_formula, fiveFactorialScalarRow,
          reciprocalFactorialInt, Fin.rev, Finset.sum_range_succ]
        have hJ0 := literalBesselJ_coeff_of_eq 0 0
        norm_num at hJ0
        have hJ1 := literalBesselJ_coeff_eq_zero 1 0 (by
          rintro ⟨candidate, heq⟩; omega)
        have hJ2 := literalBesselJ_coeff_eq_zero 2 0 (by
          rintro ⟨candidate, heq⟩; omega)
        have hJ3 := literalBesselJ_coeff_eq_zero 3 0 (by
          rintro ⟨candidate, heq⟩; omega)
        have hJ4 := literalBesselJ_coeff_eq_zero 4 0 (by
          rintro ⟨candidate, heq⟩; omega)
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply] at hJ1 hJ2 hJ3 hJ4
        rw [hJ0, hJ1, hJ2, hJ3, hJ4]
        norm_num
      · norm_num [fiveClosedPair_coeff_formula, fiveFactorialScalarRow,
          reciprocalFactorialInt, Fin.rev, Finset.sum_range_succ]
        rw [show (2 : ℚ⟦X⟧) = PowerSeries.C (2 : ℚ) by
          exact (map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 2).symm,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
          PowerSeries.coeff_C_mul]
        rw [literalBesselJ_coeff_eq_zero 0 1 (by
          rintro ⟨candidate, heq⟩; omega)]
        have hJ1 := literalBesselJ_coeff_of_eq 1 0
        norm_num at hJ1
        rw [hJ1,
          literalBesselJ_coeff_eq_zero 2 1 (by
            rintro ⟨candidate, heq⟩; omega),
          literalBesselJ_coeff_eq_zero 3 1 (by
            rintro ⟨candidate, heq⟩; omega),
          literalBesselJ_coeff_eq_zero 4 1 (by
            rintro ⟨candidate, heq⟩; omega)]
        norm_num
      · norm_num [fiveClosedPair_coeff_formula, fiveFactorialScalarRow,
          reciprocalFactorialInt, Fin.rev, Finset.sum_range_succ]
        rw [show (2 : ℚ⟦X⟧) = PowerSeries.C (2 : ℚ) by
          exact (map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 2).symm,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
          PowerSeries.coeff_C_mul]
        have hJ0 := literalBesselJ_coeff_of_eq 0 1
        norm_num at hJ0
        rw [hJ0,
          literalBesselJ_coeff_eq_zero 1 2 (by
            rintro ⟨candidate, heq⟩; omega)]
        have hJ2 := literalBesselJ_coeff_of_eq 2 0
        norm_num at hJ2
        rw [hJ2,
          literalBesselJ_coeff_eq_zero 3 2 (by
            rintro ⟨candidate, heq⟩; omega),
          literalBesselJ_coeff_eq_zero 4 2 (by
            rintro ⟨candidate, heq⟩; omega)]
        rw [show Int.toNat (2 : ℤ) = 2 by rfl]
        norm_num
    · have hlarge : degree / 2 + 1 + 4 ≤ degree + 1 := by omega
      rw [fiveClosedPair_coeff_first_boundaries 4 degree 0
        (by decide) hlarge, sum_Ico_four_terms]
      obtain ⟨index, htail | htail⟩ := Nat.even_or_odd' (degree - 4)
      · have hdegreeEven : degree = 2 * index + 4 := by omega
        have hindex : 2 ≤ index := by omega
        rw [hdegreeEven]
        rw [show 2 * index + 4 - 4 = 2 * index by omega]
        rw [show (2 * index + 4) / 2 + 1 = index + 3 by omega]
        rw [show index + 3 + 1 = index + 4 by omega,
          show index + 3 + 2 = index + 5 by omega,
          show index + 3 + 3 = index + 6 by omega]
        rw [pairBoundary_of_le 4 (2 * index + 4) (index + 3)
            (by omega) (by omega),
          pairBoundary_of_le 4 (2 * index + 4) (index + 4)
            (by omega) (by omega),
          pairBoundary_of_le 4 (2 * index + 4) (index + 5)
            (by omega) (by omega),
          pairBoundary_of_le 4 (2 * index + 4) (index + 6)
            (by omega) (by omega)]
        rw [map_add, map_add, map_add, map_add]
        rw [show (2 : ℚ⟦X⟧) = PowerSeries.C (2 : ℚ) by
          exact (map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 2).symm,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
          PowerSeries.coeff_C_mul]
        have hJ0 := literalBesselJ_coeff_of_eq 0 index
        norm_num at hJ0
        rw [hJ0,
          literalBesselJ_coeff_eq_zero 1 (2 * index) (by
            rintro ⟨candidate, heq⟩; omega)]
        have hJ2 := literalBesselJ_coeff_of_eq 2 (index - 1)
        have hdegreeJ2 : 2 * (index - 1) + 2 = 2 * index := by omega
        have hJ2current : PowerSeries.coeff (2 * index) (literalBesselJ 2) =
            1 / (((index - 1).factorial : ℚ) *
              ((index - 1 + 2).factorial : ℚ)) := by
          rw [← hdegreeJ2]
          exact hJ2
        rw [hJ2current,
          literalBesselJ_coeff_eq_zero 3 (2 * index) (by
            rintro ⟨candidate, heq⟩; omega)]
        have hJ4 := literalBesselJ_coeff_of_eq 4 (index - 2)
        have hdegreeJ4 : 2 * (index - 2) + 4 = 2 * index := by omega
        have hJ4current : PowerSeries.coeff (2 * index) (literalBesselJ 4) =
            1 / (((index - 2).factorial : ℚ) *
              ((index - 2 + 4).factorial : ℚ)) := by
          rw [← hdegreeJ4]
          exact hJ4
        rw [hJ4current]
        rw [show index + 3 - 4 = index - 1 by omega,
          show 2 * index + 4 - (index + 3) = index + 1 by omega,
          show index + 4 - 4 = index by omega,
          show 2 * index + 4 - (index + 4) = index by omega,
          show index + 5 - 4 = index + 1 by omega,
          show 2 * index + 4 - (index + 5) = index - 1 by omega,
          show index + 6 - 4 = index + 2 by omega,
          show 2 * index + 4 - (index + 6) = index - 2 by omega,
          show index - 1 + 2 = index + 1 by omega,
          show index - 2 + 4 = index + 2 by omega]
        ring
      · have hdegreeOdd : degree = 2 * index + 5 := by omega
        have hindex : 1 ≤ index := by omega
        rw [hdegreeOdd]
        rw [show 2 * index + 5 - 4 = 2 * index + 1 by omega]
        rw [show (2 * index + 5) / 2 + 1 = index + 3 by omega]
        rw [show index + 3 + 1 = index + 4 by omega,
          show index + 3 + 2 = index + 5 by omega,
          show index + 3 + 3 = index + 6 by omega]
        rw [pairBoundary_of_le 4 (2 * index + 5) (index + 3)
            (by omega) (by omega),
          pairBoundary_of_le 4 (2 * index + 5) (index + 4)
            (by omega) (by omega),
          pairBoundary_of_le 4 (2 * index + 5) (index + 5)
            (by omega) (by omega),
          pairBoundary_of_le 4 (2 * index + 5) (index + 6)
            (by omega) (by omega)]
        rw [map_add, map_add, map_add, map_add]
        rw [show (2 : ℚ⟦X⟧) = PowerSeries.C (2 : ℚ) by
          exact (map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 2).symm,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
          PowerSeries.coeff_C_mul]
        rw [literalBesselJ_coeff_eq_zero 0 (2 * index + 1) (by
          rintro ⟨candidate, heq⟩; omega)]
        have hJ1 := literalBesselJ_coeff_of_eq 1 index
        rw [hJ1,
          literalBesselJ_coeff_eq_zero 2 (2 * index + 1) (by
            rintro ⟨candidate, heq⟩; omega)]
        have hJ3 := literalBesselJ_coeff_of_eq 3 (index - 1)
        have hdegreeJ3 : 2 * (index - 1) + 3 = 2 * index + 1 := by omega
        have hJ3current : PowerSeries.coeff (2 * index + 1) (literalBesselJ 3) =
            1 / (((index - 1).factorial : ℚ) *
              ((index - 1 + 3).factorial : ℚ)) := by
          rw [← hdegreeJ3]
          exact hJ3
        rw [hJ3current,
          literalBesselJ_coeff_eq_zero 4 (2 * index + 1) (by
            rintro ⟨candidate, heq⟩; omega)]
        rw [show index + 3 - 4 = index - 1 by omega,
          show 2 * index + 5 - (index + 3) = index + 2 by omega,
          show index + 4 - 4 = index by omega,
          show 2 * index + 5 - (index + 4) = index + 1 by omega,
          show index + 5 - 4 = index + 1 by omega,
          show 2 * index + 5 - (index + 5) = index by omega,
          show index + 6 - 4 = index + 2 by omega,
          show 2 * index + 5 - (index + 6) = index - 1 by omega,
          show index - 1 + 3 = index + 2 by omega]
        ring

end FibonacciRibbonKernel
