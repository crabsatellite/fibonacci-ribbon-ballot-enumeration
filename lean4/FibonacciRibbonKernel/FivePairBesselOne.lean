import FibonacciRibbonKernel.FiveClosedCoordinates
import FibonacciRibbonKernel.GesselBesselBridge

namespace FibonacciRibbonKernel

open PowerSeries

noncomputable def pairOneBoundary (degree high : ℕ) : ℚ :=
  reciprocalFactorialInt ((high : ℤ) - 1) *
    reciprocalFactorialInt ((degree : ℤ) - (high : ℤ))

theorem pairOne_summand_eq_boundary_sub
    (degree high : ℕ) (hhigh : high ≤ degree) :
    fiveFactorialScalarRow high 3 *
          fiveFactorialScalarRow (degree - high) 4 -
        fiveFactorialScalarRow high 4 *
          fiveFactorialScalarRow (degree - high) 3 =
      pairOneBoundary degree high - pairOneBoundary degree (high + 1) := by
  unfold fiveFactorialScalarRow pairOneBoundary
  have hcast : ((degree - high : ℕ) : ℤ) =
      (degree : ℤ) - (high : ℤ) := by omega
  change
    reciprocalFactorialInt ((high : ℤ) - 1) *
          reciprocalFactorialInt ((degree - high : ℕ) : ℤ) -
        reciprocalFactorialInt (high : ℤ) *
          reciprocalFactorialInt (((degree - high : ℕ) : ℤ) - 1) =
      reciprocalFactorialInt ((high : ℤ) - 1) *
          reciprocalFactorialInt ((degree : ℤ) - (high : ℤ)) -
        reciprocalFactorialInt (((high + 1 : ℕ) : ℤ) - 1) *
          reciprocalFactorialInt
            ((degree : ℤ) - ((high + 1 : ℕ) : ℤ))
  rw [hcast]
  have hsuccLeft : (((high + 1 : ℕ) : ℤ) - 1) = (high : ℤ) := by omega
  have hsuccRight : (degree : ℤ) - ((high + 1 : ℕ) : ℤ) =
      (degree : ℤ) - (high : ℤ) - 1 := by push_cast; ring
  rw [hsuccLeft, hsuccRight]

theorem pairOneBoundary_degree_succ (degree : ℕ) :
    pairOneBoundary degree (degree + 1) = 0 := by
  unfold pairOneBoundary
  have hnegative : (degree : ℤ) - ((degree + 1 : ℕ) : ℤ) =
      Int.negSucc 0 := by omega
  rw [hnegative, reciprocalFactorialInt_negSucc, mul_zero]

theorem fiveClosedPair_three_four_coeff_boundary (degree : ℕ) :
    PowerSeries.coeff degree (fiveClosedPair 3 4) =
      pairOneBoundary degree (degree / 2 + 1) := by
  rw [fiveClosedPair_coeff_formula]
  have hfilter :
      (Finset.range (degree + 1)).filter
          (fun high => degree - high < high) =
        Finset.Ico (degree / 2 + 1) (degree + 1) := by
    ext high
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [← Finset.sum_filter]
  rw [hfilter]
  have hsummand : ∀ high ∈ Finset.Ico (degree / 2 + 1) (degree + 1),
      fiveFactorialScalarRow high 3 *
            fiveFactorialScalarRow (degree - high) 4 -
          fiveFactorialScalarRow high 4 *
            fiveFactorialScalarRow (degree - high) 3 =
        pairOneBoundary degree high - pairOneBoundary degree (high + 1) := by
    intro high hhigh
    apply pairOne_summand_eq_boundary_sub
    have := (Finset.mem_Ico.mp hhigh).2
    omega
  apply Eq.trans (Finset.sum_congr rfl hsummand)
  have hle : degree / 2 + 1 ≤ degree + 1 := by omega
  rw [show (∑ high ∈ Finset.Ico (degree / 2 + 1) (degree + 1),
      (pairOneBoundary degree high - pairOneBoundary degree (high + 1))) =
      pairOneBoundary degree (degree / 2 + 1) -
        pairOneBoundary degree (degree + 1) by
      simpa only [sub_eq_add_neg, neg_neg, add_comm] using
        (Finset.sum_Ico_sub (fun high => -pairOneBoundary degree high) hle)]
  rw [pairOneBoundary_degree_succ, sub_zero]

theorem pairOneBoundary_odd (index : ℕ) :
    pairOneBoundary (2 * index + 1) ((2 * index + 1) / 2 + 1) =
      1 / ((index.factorial : ℚ) ^ 2) := by
  unfold pairOneBoundary
  rw [show (2 * index + 1) / 2 + 1 = index + 1 by omega]
  rw [show (((index + 1 : ℕ) : ℤ) - 1) = (index : ℤ) by omega,
    show (((2 * index + 1 : ℕ) : ℤ) - ((index + 1 : ℕ) : ℤ)) =
      (index : ℤ) by omega]
  rw [show reciprocalFactorialInt (index : ℤ) =
      ((index.factorial : ℚ) : ℚ)⁻¹ by
        exact reciprocalFactorialInt_ofNat index]
  have hfactorial : (index.factorial : ℚ) ≠ 0 := by positivity
  field_simp

theorem pairOneBoundary_even_succ (index : ℕ) :
    pairOneBoundary (2 * index + 2) ((2 * index + 2) / 2 + 1) =
      1 / ((index.factorial : ℚ) * ((index + 1).factorial : ℚ)) := by
  unfold pairOneBoundary
  rw [show (2 * index + 2) / 2 + 1 = index + 2 by omega]
  rw [show (((index + 2 : ℕ) : ℤ) - 1) = ((index + 1 : ℕ) : ℤ) by omega,
    show (((2 * index + 2 : ℕ) : ℤ) - ((index + 2 : ℕ) : ℤ)) =
      (index : ℤ) by omega]
  rw [show reciprocalFactorialInt ((index + 1 : ℕ) : ℤ) =
      (((index + 1).factorial : ℚ) : ℚ)⁻¹ by
        exact reciprocalFactorialInt_ofNat (index + 1),
    show reciprocalFactorialInt (index : ℤ) =
      ((index.factorial : ℚ) : ℚ)⁻¹ by
        exact reciprocalFactorialInt_ofNat index]
  ring

theorem fiveClosedPair_three_four_eq_bessel :
    fiveClosedPair 3 4 =
      X * (literalBesselJ 0 + literalBesselJ 1) := by
  ext degree
  cases degree with
  | zero =>
      rw [fiveClosedPair_three_four_coeff_boundary]
      norm_num [pairOneBoundary, reciprocalFactorialInt]
  | succ degree =>
      rw [show X = X ^ 1 by simp,
        PowerSeries.coeff_X_pow_mul]
      obtain ⟨index, hdegree | hdegree⟩ := Nat.even_or_odd' degree
      · subst degree
        have hJ0 := literalBesselJ_coeff_of_eq 0 index
        norm_num at hJ0
        rw [fiveClosedPair_three_four_coeff_boundary,
          pairOneBoundary_odd, map_add, hJ0]
        rw [literalBesselJ_coeff_eq_zero 1 (2 * index) (by
          rintro ⟨candidate, heq⟩
          omega)]
        rw [pow_two]
        ring
      · subst degree
        have hJ1 := literalBesselJ_coeff_of_eq 1 index
        rw [fiveClosedPair_three_four_coeff_boundary,
          pairOneBoundary_even_succ, map_add]
        rw [literalBesselJ_coeff_eq_zero 0 (2 * index + 1) (by
          rintro ⟨candidate, heq⟩
          omega)]
        rw [hJ1]
        ring

end FibonacciRibbonKernel
