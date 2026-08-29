import FibonacciRibbonKernel.UniversalPairInterval

namespace FibonacciRibbonKernel

open PowerSeries

theorem factorialConvolutionTerm_bessel_left (index order : ℕ) :
    factorialConvolutionTerm (2 * index + order) index =
      PowerSeries.coeff (2 * index + order) (literalBesselJ order) := by
  rw [literalBesselJ_coeff_of_eq]
  unfold factorialConvolutionTerm
  rw [show ((2 * index + order : ℕ) : ℤ) - (index : ℤ) =
      ((index + order : ℕ) : ℤ) by push_cast; ring,
    reciprocalFactorialInt_ofNat, reciprocalFactorialInt_ofNat]
  ring

theorem factorialConvolutionTerm_bessel_right (index order : ℕ) :
    factorialConvolutionTerm (2 * index + order) (index + order) =
      PowerSeries.coeff (2 * index + order) (literalBesselJ order) := by
  rw [literalBesselJ_coeff_of_eq]
  unfold factorialConvolutionTerm
  rw [show ((2 * index + order : ℕ) : ℤ) -
      ((index + order : ℕ) : ℤ) = (index : ℤ) by
        push_cast; ring,
    reciprocalFactorialInt_ofNat, reciprocalFactorialInt_ofNat]
  ring

theorem universalPairLower_even_even (index halfGap : ℕ) :
    universalPairLower (2 * halfGap) (2 * index) =
      index + 1 - halfGap := by
  unfold universalPairLower
  omega

theorem universalPairUpper_even_even (index halfGap : ℕ) :
    universalPairUpper (2 * halfGap) (2 * index) =
      min (index + halfGap + 1) (2 * index + 1) := by
  unfold universalPairUpper
  have hfirst : (2 * index + 2 * halfGap) / 2 + 1 =
      index + halfGap + 1 := by omega
  rw [hfirst]

theorem universalPairLower_odd_even (index halfGap : ℕ) :
    universalPairLower (2 * halfGap + 1) (2 * index) =
      index - halfGap := by
  unfold universalPairLower
  omega

theorem universalPairUpper_odd_even (index halfGap : ℕ) :
    universalPairUpper (2 * halfGap + 1) (2 * index) =
      min (index + halfGap + 1) (2 * index + 1) := by
  unfold universalPairUpper
  have hfirst : (2 * index + (2 * halfGap + 1)) / 2 + 1 =
      index + halfGap + 1 := by omega
  rw [hfirst]

theorem universalPairLower_even_odd (index halfGap : ℕ) :
    universalPairLower (2 * halfGap) (2 * index + 1) =
      index + 1 - halfGap := by
  unfold universalPairLower
  omega

theorem universalPairUpper_even_odd (index halfGap : ℕ) :
    universalPairUpper (2 * halfGap) (2 * index + 1) =
      min (index + halfGap + 1) (2 * index + 2) := by
  unfold universalPairUpper
  have hfirst : (2 * index + 1 + 2 * halfGap) / 2 + 1 =
      index + halfGap + 1 := by omega
  rw [hfirst]

theorem universalPairLower_odd_odd (index halfGap : ℕ) :
    universalPairLower (2 * halfGap + 1) (2 * index + 1) =
      index + 1 - halfGap := by
  unfold universalPairLower
  omega

theorem universalPairUpper_odd_odd (index halfGap : ℕ) :
    universalPairUpper (2 * halfGap + 1) (2 * index + 1) =
      min (index + halfGap + 2) (2 * index + 2) := by
  unfold universalPairUpper
  have hfirst : (2 * index + 1 + (2 * halfGap + 1)) / 2 + 1 =
      index + halfGap + 2 := by omega
  rw [hfirst]

theorem universalPairQ_even_to_odd_recurrence
    (halfGap : ℕ) (hgap : 1 ≤ halfGap) :
    universalPairQ (2 * halfGap + 1) =
      universalPairQ (2 * halfGap) + literalBesselJ (2 * halfGap) +
        literalBesselJ (2 * halfGap + 1) := by
  ext degree
  simp only [map_add]
  obtain ⟨index, rfl | rfl⟩ := Nat.even_or_odd' degree
  · rw [universalPairQ_coeff_interval (2 * halfGap + 1) (2 * index)
        (by omega),
      universalPairQ_coeff_interval (2 * halfGap) (2 * index) (by omega),
      universalPairLower_odd_even, universalPairUpper_odd_even,
      universalPairLower_even_even, universalPairUpper_even_even]
    by_cases horder : halfGap ≤ index
    · rw [min_eq_left (by omega : index + halfGap + 1 ≤ 2 * index + 1)]
      have hlower : index + 1 - halfGap = index - halfGap + 1 := by omega
      rw [hlower]
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)
        (factorialConvolutionTerm (2 * index))]
      rw [literalBesselJ_coeff_eq_zero (2 * halfGap + 1) (2 * index) (by
        rintro ⟨candidate, heq⟩
        omega)]
      have hterm := factorialConvolutionTerm_bessel_left
        (index - halfGap) (2 * halfGap)
      rw [show 2 * (index - halfGap) + 2 * halfGap = 2 * index by omega]
        at hterm
      rw [hterm]
      ring
    · have hsubOdd : index - halfGap = 0 := by omega
      have hsubEven : index + 1 - halfGap = 0 := by omega
      rw [hsubOdd, hsubEven,
        min_eq_right (by omega : 2 * index + 1 ≤ index + halfGap + 1)]
      rw [literalBesselJ_coeff_eq_zero (2 * halfGap) (2 * index) (by
          rintro ⟨candidate, heq⟩
          omega),
        literalBesselJ_coeff_eq_zero (2 * halfGap + 1) (2 * index) (by
          rintro ⟨candidate, heq⟩
          omega)]
      ring
  · rw [universalPairQ_coeff_interval (2 * halfGap + 1) (2 * index + 1)
        (by omega),
      universalPairQ_coeff_interval (2 * halfGap) (2 * index + 1) (by omega),
      universalPairLower_odd_odd, universalPairUpper_odd_odd,
      universalPairLower_even_odd, universalPairUpper_even_odd]
    by_cases horder : halfGap ≤ index
    · rw [min_eq_left (by omega : index + halfGap + 2 ≤ 2 * index + 2),
        min_eq_left (by omega : index + halfGap + 1 ≤ 2 * index + 2)]
      rw [Finset.sum_Ico_succ_top (by omega)
        (factorialConvolutionTerm (2 * index + 1))]
      rw [literalBesselJ_coeff_eq_zero (2 * halfGap) (2 * index + 1) (by
        rintro ⟨candidate, heq⟩
        omega)]
      have hterm := factorialConvolutionTerm_bessel_right
        (index - halfGap) (2 * halfGap + 1)
      rw [show 2 * (index - halfGap) + (2 * halfGap + 1) =
        2 * index + 1 by omega] at hterm
      have hterm' : factorialConvolutionTerm (2 * index + 1)
          (index + halfGap + 1) =
          PowerSeries.coeff (2 * index + 1)
            (literalBesselJ (2 * halfGap + 1)) := by
        rw [← show index - halfGap + (2 * halfGap + 1) =
          index + halfGap + 1 by omega]
        exact hterm
      rw [hterm']
      ring
    · have hsub : index + 1 - halfGap = 0 := by omega
      rw [hsub,
        min_eq_right (by omega : 2 * index + 2 ≤ index + halfGap + 2),
        min_eq_right (by omega : 2 * index + 2 ≤ index + halfGap + 1)]
      rw [literalBesselJ_coeff_eq_zero (2 * halfGap) (2 * index + 1) (by
          rintro ⟨candidate, heq⟩
          omega),
        literalBesselJ_coeff_eq_zero (2 * halfGap + 1) (2 * index + 1) (by
          rintro ⟨candidate, heq⟩
          omega)]
      ring

theorem universalPairQ_odd_to_even_recurrence (halfGap : ℕ) :
    universalPairQ (2 * halfGap + 2) =
      universalPairQ (2 * halfGap + 1) + literalBesselJ (2 * halfGap + 1) +
        literalBesselJ (2 * halfGap + 2) := by
  ext degree
  simp only [map_add]
  obtain ⟨index, rfl | rfl⟩ := Nat.even_or_odd' degree
  · rw [universalPairQ_coeff_interval (2 * halfGap + 2) (2 * index)
        (by omega),
      universalPairQ_coeff_interval (2 * halfGap + 1) (2 * index) (by omega),
      show 2 * halfGap + 2 = 2 * (halfGap + 1) by omega,
      universalPairLower_even_even, universalPairUpper_even_even,
      universalPairLower_odd_even, universalPairUpper_odd_even]
    rw [show 2 * (halfGap + 1) = 2 * halfGap + 2 by omega]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    by_cases horder : halfGap < index
    · rw [min_eq_left (by omega : index + (halfGap + 2) ≤
          2 * index + 1),
        min_eq_left (by omega : index + (halfGap + 1) ≤ 2 * index + 1)]
      have hlower : index + 1 - (halfGap + 1) = index - halfGap := by omega
      rw [hlower]
      have hupperSucc : index + (halfGap + 2) =
          index + (halfGap + 1) + 1 := by omega
      rw [hupperSucc]
      rw [Finset.sum_Ico_succ_top (by omega)
        (factorialConvolutionTerm (2 * index))]
      rw [literalBesselJ_coeff_eq_zero (2 * halfGap + 1) (2 * index) (by
        rintro ⟨candidate, heq⟩
        omega)]
      have hterm := factorialConvolutionTerm_bessel_right
        (index - halfGap - 1) (2 * halfGap + 2)
      rw [show 2 * (index - halfGap - 1) + (2 * halfGap + 2) =
        2 * index by omega] at hterm
      have hterm' : factorialConvolutionTerm (2 * index)
          (index + halfGap + 1) =
          PowerSeries.coeff (2 * index)
            (literalBesselJ (2 * halfGap + 2)) := by
        rw [← show index - halfGap - 1 + (2 * halfGap + 2) =
          index + halfGap + 1 by omega]
        exact hterm
      have hterm'' : factorialConvolutionTerm (2 * index)
          (index + (halfGap + 1)) =
          PowerSeries.coeff (2 * index)
            (literalBesselJ (2 * halfGap + 2)) := by
        simpa [Nat.add_assoc] using hterm'
      rw [hterm'']
      ring
    · have hsubCurrent : index - halfGap = 0 := by omega
      have hsubNext : index + 1 - (halfGap + 1) = 0 := by omega
      rw [hsubCurrent, hsubNext,
        min_eq_right (by omega : 2 * index + 1 ≤
          index + (halfGap + 2)),
        min_eq_right (by omega : 2 * index + 1 ≤ index + (halfGap + 1))]
      rw [literalBesselJ_coeff_eq_zero (2 * halfGap + 1) (2 * index) (by
          rintro ⟨candidate, heq⟩
          omega),
        literalBesselJ_coeff_eq_zero (2 * halfGap + 2) (2 * index) (by
          rintro ⟨candidate, heq⟩
          omega)]
      ring
  · rw [universalPairQ_coeff_interval (2 * halfGap + 2) (2 * index + 1)
        (by omega),
      universalPairQ_coeff_interval (2 * halfGap + 1) (2 * index + 1) (by omega),
      show 2 * halfGap + 2 = 2 * (halfGap + 1) by omega,
      universalPairLower_even_odd, universalPairUpper_even_odd,
      universalPairLower_odd_odd, universalPairUpper_odd_odd]
    rw [show 2 * (halfGap + 1) = 2 * halfGap + 2 by omega]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    by_cases horder : halfGap ≤ index
    · rw [min_eq_left (by omega : index + (halfGap + 2) ≤
          2 * index + 2)]
      have hlower : index + 1 - halfGap = index - halfGap + 1 := by omega
      have hnextLower : index + 1 - (halfGap + 1) = index - halfGap := by
        omega
      rw [hlower, hnextLower]
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)
        (factorialConvolutionTerm (2 * index + 1))]
      rw [literalBesselJ_coeff_eq_zero (2 * halfGap + 2) (2 * index + 1) (by
        rintro ⟨candidate, heq⟩
        omega)]
      have hterm := factorialConvolutionTerm_bessel_left
        (index - halfGap) (2 * halfGap + 1)
      rw [show 2 * (index - halfGap) + (2 * halfGap + 1) =
        2 * index + 1 by omega] at hterm
      rw [hterm]
      ring
    · have hsubCurrent : index + 1 - halfGap = 0 := by omega
      have hsubNext : index + 1 - (halfGap + 1) = 0 := by omega
      rw [hsubCurrent, hsubNext,
        min_eq_right (by omega : 2 * index + 2 ≤
          index + (halfGap + 2))]
      rw [literalBesselJ_coeff_eq_zero (2 * halfGap + 1) (2 * index + 1) (by
          rintro ⟨candidate, heq⟩
          omega),
        literalBesselJ_coeff_eq_zero (2 * halfGap + 2) (2 * index + 1) (by
          rintro ⟨candidate, heq⟩
          omega)]
      ring

end FibonacciRibbonKernel
