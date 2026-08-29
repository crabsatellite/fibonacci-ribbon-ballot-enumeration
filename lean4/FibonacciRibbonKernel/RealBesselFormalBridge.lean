import FibonacciRibbonKernel.LiteralBesselCosineBridge

namespace FibonacciRibbonKernel

open PowerSeries

noncomputable def realBesselIntegralSeries (order : ℤ) : ℝ⟦X⟧ :=
  PowerSeries.mk fun power =>
    (∫ angle in (0 : ℝ)..Real.pi,
      (2 * Real.cos angle) ^ power *
        Real.cos ((order : ℝ) * angle)) /
      (power.factorial : ℝ)

noncomputable def symmetricLiteralBesselJR (order : ℤ) : ℝ⟦X⟧ :=
  PowerSeries.map (Rat.castHom ℝ) (symmetricLiteralBesselJ order)

@[simp] theorem symmetricLiteralBesselJR_coeff
    (order : ℤ) (power : ℕ) :
    PowerSeries.coeff power (symmetricLiteralBesselJR order) =
      ((PowerSeries.coeff power
        (symmetricLiteralBesselJ order) : ℚ) : ℝ) := by
  simp [symmetricLiteralBesselJR]

@[simp] theorem realBesselIntegralSeries_coeff
    (order : ℤ) (power : ℕ) :
    PowerSeries.coeff power (realBesselIntegralSeries order) =
      (∫ angle in (0 : ℝ)..Real.pi,
        (2 * Real.cos angle) ^ power *
          Real.cos ((order : ℝ) * angle)) /
        (power.factorial : ℝ) := by
  simp [realBesselIntegralSeries]

theorem realBesselIntegralSeries_coeff_eq
    (order : ℤ) (power : ℕ) :
    PowerSeries.coeff power (realBesselIntegralSeries order) =
      Real.pi * PowerSeries.coeff power
        (symmetricLiteralBesselJR order) := by
  have hmoment := integerCosineMoment_eq_literalBesselWalkCoefficient
    order power
  unfold integerCosineMoment literalBesselWalkCoefficient
    factorialScaledCoeffReal factorialScaledCoeffQ at hmoment
  rw [realBesselIntegralSeries_coeff,
    symmetricLiteralBesselJR_coeff]
  have hfactorial : (power.factorial : ℝ) ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  push_cast at hmoment
  field_simp [hpi] at hmoment
  apply (div_eq_iff hfactorial).2
  rw [hmoment]
  ring

theorem realBesselIntegralSeries_eq_literal
    (order : ℤ) :
    realBesselIntegralSeries order =
      PowerSeries.C Real.pi * symmetricLiteralBesselJR order := by
  ext power
  rw [PowerSeries.coeff_C_mul,
    realBesselIntegralSeries_coeff_eq]

theorem symmetricLiteralBesselJR_neg (order : ℤ) :
    symmetricLiteralBesselJR (-order) =
      symmetricLiteralBesselJR order := by
  unfold symmetricLiteralBesselJR symmetricLiteralBesselJ
  rw [Int.natAbs_neg]

end FibonacciRibbonKernel
