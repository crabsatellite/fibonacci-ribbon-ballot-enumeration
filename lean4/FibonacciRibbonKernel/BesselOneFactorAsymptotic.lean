import FibonacciRibbonKernel.BesselSignedParity
import FibonacciRibbonKernel.CatalanAsymptotic

namespace FibonacciRibbonKernel

open Filter Asymptotics

theorem besselJ0FactorialCoeffQ_even_eq_centralBinom (half : ℕ) :
    besselJ0FactorialCoeffQ (2 * half) = (Nat.centralBinom half : ℚ) := by
  unfold besselJ0FactorialCoeffQ
  rw [besselJ0_coeff_even]
  have hchoose := Nat.choose_mul_factorial_mul_factorial
    (show half ≤ 2 * half by omega)
  have hsub : 2 * half - half = half := by omega
  rw [hsub] at hchoose
  have hfactorial :
      Nat.centralBinom half * half.factorial * half.factorial =
        (2 * half).factorial := by
    simpa [Nat.centralBinom, mul_assoc] using hchoose
  have hfactorialQ :
      (Nat.centralBinom half : ℚ) * (half.factorial : ℚ) *
          (half.factorial : ℚ) = ((2 * half).factorial : ℚ) := by
    exact_mod_cast hfactorial
  have hhalf : (half.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  nlinarith

theorem besselPlusFactorialCoeffReal_even_eq_centralBinom (half : ℕ) :
    besselPlusFactorialCoeffReal (2 * half) =
      (Nat.centralBinom half : ℝ) := by
  rw [besselPlusFactorialCoeffReal_eq_sum,
    besselJ1FactorialCoeffReal_even, add_zero]
  unfold besselJ0FactorialCoeffReal
  rw [besselJ0FactorialCoeffQ_even_eq_centralBinom]
  norm_num

theorem besselPlusFactorialCoeffReal_odd_eq_half_centralBinom (half : ℕ) :
    besselPlusFactorialCoeffReal (2 * half + 1) =
      (Nat.centralBinom (half + 1) : ℝ) / 2 := by
  rw [besselPlusFactorialCoeffReal_eq_sum,
    besselJ0FactorialCoeffReal_odd, zero_add,
    besselJ1FactorialCoeffReal_eq_half_succ_cosineMoment]
  rw [show 2 * half + 1 + 1 = 2 * (half + 1) by omega]
  rw [← besselJ0FactorialCoeffReal_eq_cosineMoment,
    besselJ0FactorialCoeffReal]
  rw [besselJ0FactorialCoeffQ_even_eq_centralBinom]
  norm_num

noncomputable def besselPlusEvenLeading (half : ℕ) : ℝ :=
  centralBinomialLeadingTerm half

noncomputable def besselPlusOddLeading (half : ℕ) : ℝ :=
  centralBinomialLeadingTerm (half + 1) / 2

theorem besselPlus_even_isEquivalent :
    (fun half : ℕ => besselPlusFactorialCoeffReal (2 * half))
      ~[atTop] besselPlusEvenLeading := by
  have hexact :
      (fun half : ℕ => besselPlusFactorialCoeffReal (2 * half)) =ᶠ[atTop]
        (fun half : ℕ => (Nat.centralBinom half : ℝ)) := by
    filter_upwards with half
    exact besselPlusFactorialCoeffReal_even_eq_centralBinom half
  exact hexact.isEquivalent.trans centralBinomial_isEquivalent_leading

theorem besselPlus_odd_isEquivalent :
    (fun half : ℕ => besselPlusFactorialCoeffReal (2 * half + 1))
      ~[atTop] besselPlusOddLeading := by
  have hexact :
      (fun half : ℕ => besselPlusFactorialCoeffReal (2 * half + 1)) =ᶠ[atTop]
        (fun half : ℕ => (Nat.centralBinom (half + 1) : ℝ) / 2) := by
    filter_upwards with half
    exact besselPlusFactorialCoeffReal_odd_eq_half_centralBinom half
  have hshift := centralBinomial_isEquivalent_leading.comp_tendsto
    (tendsto_add_atTop_nat 1)
  have htwo : (fun _ : ℕ => (2 : ℝ)) ~[atTop] (fun _ : ℕ => (2 : ℝ)) :=
    IsEquivalent.refl
  exact hexact.isEquivalent.trans (hshift.div htwo)

end FibonacciRibbonKernel
