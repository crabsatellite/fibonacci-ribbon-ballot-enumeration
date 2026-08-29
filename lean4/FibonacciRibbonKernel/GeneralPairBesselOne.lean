import FibonacciRibbonKernel.GeneralPairBoundary
import FibonacciRibbonKernel.GesselBesselBridge

namespace FibonacciRibbonKernel

open PowerSeries

noncomputable def generalPairQOne : ℚ⟦X⟧ :=
  literalBesselJ 0 + literalBesselJ 1

theorem generalPairBoundary_one_odd (index : ℕ) :
    generalPairBoundary 1 (2 * index + 1)
        ((2 * index + 1) / 2 + 1) =
      1 / ((index.factorial : ℚ) ^ 2) := by
  unfold generalPairBoundary
  rw [show (2 * index + 1) / 2 + 1 = index + 1 by omega]
  rw [show (((index + 1 : ℕ) : ℤ) - ((1 : ℕ) : ℤ)) =
      (index : ℤ) by omega,
    show (((2 * index + 1 : ℕ) : ℤ) - ((index + 1 : ℕ) : ℤ)) =
      (index : ℤ) by omega]
  rw [reciprocalFactorialInt_ofNat]
  have hfactorial : (index.factorial : ℚ) ≠ 0 := by positivity
  field_simp

theorem generalPairBoundary_one_even_succ (index : ℕ) :
    generalPairBoundary 1 (2 * index + 2)
        ((2 * index + 2) / 2 + 1) =
      1 / ((index.factorial : ℚ) * ((index + 1).factorial : ℚ)) := by
  unfold generalPairBoundary
  rw [show (2 * index + 2) / 2 + 1 = index + 2 by omega]
  rw [show (((index + 2 : ℕ) : ℤ) - ((1 : ℕ) : ℤ)) =
      ((index + 1 : ℕ) : ℤ) by omega,
    show (((2 * index + 2 : ℕ) : ℤ) - ((index + 2 : ℕ) : ℤ)) =
      (index : ℤ) by omega]
  rw [reciprocalFactorialInt_ofNat, reciprocalFactorialInt_ofNat]
  ring

theorem generalClosedPair_rev_one_coeff_boundary
    {rank : ℕ} (degree : ℕ) (left : Fin (rank + 1))
    (hleft : left.rev.val = 1) :
    PowerSeries.coeff degree
        (generalClosedPair left (Fin.last rank)) =
      generalPairBoundary 1 degree (degree / 2 + 1) := by
  by_cases hzero : degree = 0
  · subst degree
    rw [generalClosedPair_coeff_formula]
    norm_num [generalFactorialScalarRow, generalPairBoundary,
      reciprocalFactorialInt]
  · rw [generalClosedPair_coeff_first_boundaries 1 degree left hleft
      (by omega)]
    have hIco : Finset.Ico (degree / 2 + 1) (degree / 2 + 1 + 1) =
        {degree / 2 + 1} := by
      ext value
      simp
    rw [hIco]
    simp

/-- Uniform right-boundary coordinate: in every dimension, adjacent reversed
columns give exactly `X(J₀+J₁)`. -/
theorem generalClosedPair_rev_one_eq_bessel
    {rank : ℕ} (left : Fin (rank + 1)) (hleft : left.rev.val = 1) :
    generalClosedPair left (Fin.last rank) = X * generalPairQOne := by
  ext degree
  cases degree with
  | zero =>
      rw [generalClosedPair_rev_one_coeff_boundary 0 left hleft]
      norm_num [generalPairBoundary, reciprocalFactorialInt]
  | succ degree =>
      rw [show X = X ^ 1 by simp, PowerSeries.coeff_X_pow_mul]
      obtain ⟨index, hdegree | hdegree⟩ := Nat.even_or_odd' degree
      · subst degree
        have hJ0 := literalBesselJ_coeff_of_eq 0 index
        norm_num at hJ0
        rw [generalClosedPair_rev_one_coeff_boundary _ left hleft,
          generalPairBoundary_one_odd, generalPairQOne, map_add, hJ0]
        rw [literalBesselJ_coeff_eq_zero 1 (2 * index) (by
          rintro ⟨candidate, heq⟩
          omega)]
        rw [pow_two]
        ring
      · subst degree
        have hJ1 := literalBesselJ_coeff_of_eq 1 index
        rw [generalClosedPair_rev_one_coeff_boundary _ left hleft,
          generalPairBoundary_one_even_succ, generalPairQOne, map_add]
        rw [literalBesselJ_coeff_eq_zero 0 (2 * index + 1) (by
          rintro ⟨candidate, heq⟩
          omega), hJ1]
        ring

end FibonacciRibbonKernel
