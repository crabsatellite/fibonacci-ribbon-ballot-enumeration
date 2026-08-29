import FibonacciRibbonKernel.SixPairBoundary
import FibonacciRibbonKernel.FivePfaffianBessel

namespace FibonacciRibbonKernel

open PowerSeries

noncomputable def pairQ5 : ℚ⟦X⟧ :=
  literalBesselJ 0 + 2 * literalBesselJ 1 +
    2 * literalBesselJ 2 + 2 * literalBesselJ 3 +
    2 * literalBesselJ 4 + literalBesselJ 5

theorem sum_Ico_five_terms (function : ℕ → ℚ) (start : ℕ) :
    (∑ index ∈ Finset.Ico start (start + 5), function index) =
      function start + function (start + 1) + function (start + 2) +
        function (start + 3) + function (start + 4) := by
  have hfinset : Finset.Ico start (start + 5) =
      {start, start + 1, start + 2, start + 3, start + 4} := by
    ext index
    simp
    omega
  rw [hfinset]
  simp
  ring

theorem sixClosedPair_zero_five_eq_bessel :
    sixClosedPair 0 5 = X ^ 5 * pairQ5 := by
  ext degree
  by_cases hsmall : degree < 5
  · interval_cases degree <;>
      norm_num [sixClosedPair_coeff_formula, sixFactorialScalarRow,
        reciprocalFactorialInt, Fin.rev, PowerSeries.coeff_X_pow_mul',
        Finset.sum_range_succ]
  · rw [PowerSeries.coeff_X_pow_mul', if_pos (by omega : 5 ≤ degree)]
    by_cases htailSmall : degree - 5 < 4
    · have hcases : degree = 5 ∨ degree = 6 ∨ degree = 7 ∨ degree = 8 := by omega
      rcases hcases with rfl | rfl | rfl | rfl
      · norm_num [sixClosedPair_coeff_formula, sixFactorialScalarRow,
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
        have hJ5 := literalBesselJ_coeff_eq_zero 5 0 (by
          rintro ⟨candidate, heq⟩; omega)
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply] at hJ1 hJ2 hJ3 hJ4 hJ5
        unfold pairQ5
        norm_num only [map_add, map_mul, map_ofNat]
        rw [hJ0, hJ1, hJ2, hJ3, hJ4, hJ5]
        norm_num
      · norm_num [sixClosedPair_coeff_formula, sixFactorialScalarRow,
          reciprocalFactorialInt, Fin.rev, Finset.sum_range_succ]
        simp only [pairQ5, map_add]
        rw [show (2 : ℚ⟦X⟧) = PowerSeries.C (2 : ℚ) by
          exact (map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 2).symm,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
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
            rintro ⟨candidate, heq⟩; omega),
          literalBesselJ_coeff_eq_zero 5 1 (by
            rintro ⟨candidate, heq⟩; omega)]
        norm_num
      · norm_num [sixClosedPair_coeff_formula, sixFactorialScalarRow,
          reciprocalFactorialInt, Fin.rev, Finset.sum_range_succ]
        simp only [pairQ5, map_add]
        rw [show (2 : ℚ⟦X⟧) = PowerSeries.C (2 : ℚ) by
          exact (map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 2).symm,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
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
            rintro ⟨candidate, heq⟩; omega),
          literalBesselJ_coeff_eq_zero 5 2 (by
            rintro ⟨candidate, heq⟩; omega)]
        rw [show Int.toNat (2 : ℤ) = 2 by rfl]
        norm_num
      · norm_num [sixClosedPair_coeff_formula, sixFactorialScalarRow,
          reciprocalFactorialInt, Fin.rev, Finset.sum_range_succ]
        simp only [pairQ5, map_add]
        rw [show (2 : ℚ⟦X⟧) = PowerSeries.C (2 : ℚ) by
          exact (map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 2).symm,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
        rw [literalBesselJ_coeff_eq_zero 0 3 (by
          rintro ⟨candidate, heq⟩; omega)]
        have hJ1 := literalBesselJ_coeff_of_eq 1 1
        norm_num at hJ1
        rw [hJ1,
          literalBesselJ_coeff_eq_zero 2 3 (by
            rintro ⟨candidate, heq⟩; omega)]
        have hJ3 := literalBesselJ_coeff_of_eq 3 0
        norm_num at hJ3
        rw [hJ3,
          literalBesselJ_coeff_eq_zero 4 3 (by
            rintro ⟨candidate, heq⟩; omega),
          literalBesselJ_coeff_eq_zero 5 3 (by
            rintro ⟨candidate, heq⟩; omega)]
        rw [show Int.toNat (2 : ℤ) = 2 by rfl,
          show Int.toNat (3 : ℤ) = 3 by rfl]
        norm_num
    · have hlarge : degree / 2 + 1 + 5 ≤ degree + 1 := by omega
      rw [sixClosedPair_coeff_first_boundaries 5 degree 0
        (by decide) hlarge, sum_Ico_five_terms]
      obtain ⟨index, htail | htail⟩ := Nat.even_or_odd' (degree - 5)
      · have hdegreeEven : degree = 2 * index + 5 := by omega
        have hindex : 2 ≤ index := by omega
        rw [hdegreeEven]
        rw [show 2 * index + 5 - 5 = 2 * index by omega]
        rw [show (2 * index + 5) / 2 + 1 = index + 3 by omega]
        rw [show index + 3 + 1 = index + 4 by omega,
          show index + 3 + 2 = index + 5 by omega,
          show index + 3 + 3 = index + 6 by omega,
          show index + 3 + 4 = index + 7 by omega]
        rw [pairBoundary_of_le 5 (2 * index + 5) (index + 3)
            (by omega) (by omega),
          pairBoundary_of_le 5 (2 * index + 5) (index + 4)
            (by omega) (by omega),
          pairBoundary_of_le 5 (2 * index + 5) (index + 5)
            (by omega) (by omega),
          pairBoundary_of_le 5 (2 * index + 5) (index + 6)
            (by omega) (by omega),
          pairBoundary_of_le 5 (2 * index + 5) (index + 7)
            (by omega) (by omega)]
        simp only [pairQ5, map_add]
        rw [show (2 : ℚ⟦X⟧) = PowerSeries.C (2 : ℚ) by
          exact (map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 2).symm,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
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
          rw [← hdegreeJ2]; exact hJ2
        rw [hJ2current,
          literalBesselJ_coeff_eq_zero 3 (2 * index) (by
            rintro ⟨candidate, heq⟩; omega)]
        have hJ4 := literalBesselJ_coeff_of_eq 4 (index - 2)
        have hdegreeJ4 : 2 * (index - 2) + 4 = 2 * index := by omega
        have hJ4current : PowerSeries.coeff (2 * index) (literalBesselJ 4) =
            1 / (((index - 2).factorial : ℚ) *
              ((index - 2 + 4).factorial : ℚ)) := by
          rw [← hdegreeJ4]; exact hJ4
        rw [hJ4current,
          literalBesselJ_coeff_eq_zero 5 (2 * index) (by
            rintro ⟨candidate, heq⟩; omega)]
        rw [show index + 3 - 5 = index - 2 by omega,
          show 2 * index + 5 - (index + 3) = index + 2 by omega,
          show index + 4 - 5 = index - 1 by omega,
          show 2 * index + 5 - (index + 4) = index + 1 by omega,
          show index + 5 - 5 = index by omega,
          show 2 * index + 5 - (index + 5) = index by omega,
          show index + 6 - 5 = index + 1 by omega,
          show 2 * index + 5 - (index + 6) = index - 1 by omega,
          show index + 7 - 5 = index + 2 by omega,
          show 2 * index + 5 - (index + 7) = index - 2 by omega,
          show index - 1 + 2 = index + 1 by omega,
          show index - 2 + 4 = index + 2 by omega]
        ring
      · have hdegreeOdd : degree = 2 * index + 6 := by omega
        have hindex : 2 ≤ index := by omega
        rw [hdegreeOdd]
        rw [show 2 * index + 6 - 5 = 2 * index + 1 by omega]
        rw [show (2 * index + 6) / 2 + 1 = index + 4 by omega]
        rw [show index + 4 + 1 = index + 5 by omega,
          show index + 4 + 2 = index + 6 by omega,
          show index + 4 + 3 = index + 7 by omega,
          show index + 4 + 4 = index + 8 by omega]
        rw [pairBoundary_of_le 5 (2 * index + 6) (index + 4)
            (by omega) (by omega),
          pairBoundary_of_le 5 (2 * index + 6) (index + 5)
            (by omega) (by omega),
          pairBoundary_of_le 5 (2 * index + 6) (index + 6)
            (by omega) (by omega),
          pairBoundary_of_le 5 (2 * index + 6) (index + 7)
            (by omega) (by omega),
          pairBoundary_of_le 5 (2 * index + 6) (index + 8)
            (by omega) (by omega)]
        simp only [pairQ5, map_add]
        rw [show (2 : ℚ⟦X⟧) = PowerSeries.C (2 : ℚ) by
          exact (map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 2).symm,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
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
          rw [← hdegreeJ3]; exact hJ3
        rw [hJ3current,
          literalBesselJ_coeff_eq_zero 4 (2 * index + 1) (by
            rintro ⟨candidate, heq⟩; omega)]
        have hJ5 := literalBesselJ_coeff_of_eq 5 (index - 2)
        have hdegreeJ5 : 2 * (index - 2) + 5 = 2 * index + 1 := by omega
        have hJ5current : PowerSeries.coeff (2 * index + 1) (literalBesselJ 5) =
            1 / (((index - 2).factorial : ℚ) *
              ((index - 2 + 5).factorial : ℚ)) := by
          rw [← hdegreeJ5]; exact hJ5
        rw [hJ5current]
        rw [show index + 4 - 5 = index - 1 by omega,
          show 2 * index + 6 - (index + 4) = index + 2 by omega,
          show index + 5 - 5 = index by omega,
          show 2 * index + 6 - (index + 5) = index + 1 by omega,
          show index + 6 - 5 = index + 1 by omega,
          show 2 * index + 6 - (index + 6) = index by omega,
          show index + 7 - 5 = index + 2 by omega,
          show 2 * index + 6 - (index + 7) = index - 1 by omega,
          show index + 8 - 5 = index + 3 by omega,
          show 2 * index + 6 - (index + 8) = index - 2 by omega,
          show index - 1 + 3 = index + 2 by omega,
          show index - 2 + 5 = index + 3 by omega]
        ring

end FibonacciRibbonKernel
