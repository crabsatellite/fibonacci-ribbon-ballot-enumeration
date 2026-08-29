import FibonacciRibbonKernel.FivePairBesselTwo

namespace FibonacciRibbonKernel

open PowerSeries

theorem sum_Ico_three_terms (function : ℕ → ℚ) (start : ℕ) :
    (∑ index ∈ Finset.Ico start (start + 3), function index) =
      function start + function (start + 1) + function (start + 2) := by
  have hfinset : Finset.Ico start (start + 3) =
      {start, start + 1, start + 2} := by
    ext index
    simp
    omega
  rw [hfinset]
  simp
  ring

theorem fiveClosedPair_one_four_eq_bessel :
    fiveClosedPair 1 4 =
      X ^ 3 *
        (literalBesselJ 0 + 2 * literalBesselJ 1 +
          2 * literalBesselJ 2 + literalBesselJ 3) := by
  ext degree
  by_cases hsmall : degree < 3
  · interval_cases degree <;>
      norm_num [fiveClosedPair_coeff_formula, fiveFactorialScalarRow,
        reciprocalFactorialInt, Fin.rev, PowerSeries.coeff_X_pow_mul',
        Finset.sum_range_succ]
  · rw [PowerSeries.coeff_X_pow_mul', if_pos (by omega : 3 ≤ degree)]
    by_cases htailSmall : degree - 3 < 2
    · have hdegreeCases : degree = 3 ∨ degree = 4 := by omega
      rcases hdegreeCases with rfl | rfl
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
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply] at hJ1 hJ2 hJ3
        rw [hJ0, hJ1, hJ2, hJ3]
        norm_num
      · norm_num [fiveClosedPair_coeff_formula, fiveFactorialScalarRow,
          reciprocalFactorialInt, Fin.rev, Finset.sum_range_succ]
        rw [show (2 : ℚ⟦X⟧) = PowerSeries.C (2 : ℚ) by
          exact (map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 2).symm,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
        rw [literalBesselJ_coeff_eq_zero 0 1 (by
          rintro ⟨candidate, heq⟩; omega)]
        have hJ1 := literalBesselJ_coeff_of_eq 1 0
        norm_num at hJ1
        rw [hJ1,
          literalBesselJ_coeff_eq_zero 2 1 (by
            rintro ⟨candidate, heq⟩; omega),
          literalBesselJ_coeff_eq_zero 3 1 (by
            rintro ⟨candidate, heq⟩; omega)]
        norm_num
    · have hlarge : degree / 2 + 1 + 3 ≤ degree + 1 := by omega
      rw [fiveClosedPair_coeff_first_boundaries 3 degree 1
        (by decide) hlarge, sum_Ico_three_terms]
      obtain ⟨index, htail | htail⟩ := Nat.even_or_odd' (degree - 3)
      · have hdegreeEven : degree = 2 * index + 3 := by omega
        have hindex : 1 ≤ index := by omega
        rw [hdegreeEven]
        rw [show 2 * index + 3 - 3 = 2 * index by omega]
        rw [show (2 * index + 3) / 2 + 1 = index + 2 by omega]
        rw [show index + 2 + 1 = index + 3 by omega,
          show index + 2 + 2 = index + 4 by omega]
        rw [pairBoundary_of_le 3 (2 * index + 3) (index + 2)
            (by omega) (by omega),
          pairBoundary_of_le 3 (2 * index + 3) (index + 3)
            (by omega) (by omega),
          pairBoundary_of_le 3 (2 * index + 3) (index + 4)
            (by omega) (by omega)]
        rw [map_add, map_add, map_add]
        rw [show (2 : ℚ⟦X⟧) = PowerSeries.C (2 : ℚ) by
          exact (map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 2).symm,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
        have hJ0 := literalBesselJ_coeff_of_eq 0 index
        norm_num at hJ0
        rw [hJ0]
        rw [literalBesselJ_coeff_eq_zero 1 (2 * index) (by
          rintro ⟨candidate, heq⟩
          omega)]
        have hJ2 := literalBesselJ_coeff_of_eq 2 (index - 1)
        have hdegreeJ2 : 2 * (index - 1) + 2 = 2 * index := by omega
        rw [literalBesselJ_coeff_eq_zero 3 (2 * index) (by
          rintro ⟨candidate, heq⟩
          omega)]
        have hJ2current : PowerSeries.coeff (2 * index) (literalBesselJ 2) =
            1 / (((index - 1).factorial : ℚ) *
              ((index - 1 + 2).factorial : ℚ)) := by
          rw [← hdegreeJ2]
          exact hJ2
        rw [hJ2current]
        rw [show index + 2 - 3 = index - 1 by omega,
          show 2 * index + 3 - (index + 2) = index + 1 by omega,
          show index + 3 - 3 = index by omega,
          show 2 * index + 3 - (index + 3) = index by omega,
          show index + 4 - 3 = index + 1 by omega,
          show 2 * index + 3 - (index + 4) = index - 1 by omega,
          show index - 1 + 2 = index + 1 by omega]
        ring
      · have hdegreeOdd : degree = 2 * index + 4 := by omega
        have hindex : 1 ≤ index := by omega
        rw [hdegreeOdd]
        rw [show 2 * index + 4 - 3 = 2 * index + 1 by omega]
        rw [show (2 * index + 4) / 2 + 1 = index + 3 by omega]
        rw [show index + 3 + 1 = index + 4 by omega,
          show index + 3 + 2 = index + 5 by omega]
        rw [pairBoundary_of_le 3 (2 * index + 4) (index + 3)
            (by omega) (by omega),
          pairBoundary_of_le 3 (2 * index + 4) (index + 4)
            (by omega) (by omega),
          pairBoundary_of_le 3 (2 * index + 4) (index + 5)
            (by omega) (by omega)]
        rw [map_add, map_add, map_add]
        rw [show (2 : ℚ⟦X⟧) = PowerSeries.C (2 : ℚ) by
          exact (map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 2).symm,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
        rw [literalBesselJ_coeff_eq_zero 0 (2 * index + 1) (by
          rintro ⟨candidate, heq⟩
          omega)]
        have hJ1 := literalBesselJ_coeff_of_eq 1 index
        rw [hJ1]
        rw [literalBesselJ_coeff_eq_zero 2 (2 * index + 1) (by
          rintro ⟨candidate, heq⟩
          omega)]
        have hJ3 := literalBesselJ_coeff_of_eq 3 (index - 1)
        have hdegreeJ3 : 2 * (index - 1) + 3 = 2 * index + 1 := by omega
        have hJ3current :
            PowerSeries.coeff (2 * index + 1) (literalBesselJ 3) =
              1 / (((index - 1).factorial : ℚ) *
                ((index - 1 + 3).factorial : ℚ)) := by
          rw [← hdegreeJ3]
          exact hJ3
        rw [hJ3current]
        rw [show index + 3 - 3 = index by omega,
          show 2 * index + 4 - (index + 3) = index + 1 by omega,
          show index + 4 - 3 = index + 1 by omega,
          show 2 * index + 4 - (index + 4) = index by omega,
          show index + 5 - 3 = index + 2 by omega,
          show 2 * index + 4 - (index + 5) = index - 1 by omega,
          show index - 1 + 3 = index + 2 by omega]
        ring

end FibonacciRibbonKernel
