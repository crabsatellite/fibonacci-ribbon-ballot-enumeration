import FibonacciRibbonKernel.HeightFourOrdinary
import FibonacciRibbonKernel.StableTransform

namespace FibonacciRibbonKernel

open PowerSeries

theorem substitutionDenominator_derivative_two :
    PowerSeries.derivative ℤ
        (PowerSeries.derivative ℤ substitutionDenominator) =
      -2 * substitutionDenominator ^ 2 +
        8 * X ^ 2 * substitutionDenominator ^ 3 := by
  have hfirst : PowerSeries.derivative ℤ substitutionDenominator =
      (-2 : ℤ) • (X * substitutionDenominator ^ 2) := by
    rw [substitutionDenominator_derivative]
    norm_num
    ring
  have h := congrArg (PowerSeries.derivative ℤ) hfirst
  norm_num at h
  have htwo : PowerSeries.derivative ℤ (2 : ℤ⟦X⟧) = 0 :=
    (PowerSeries.derivative ℤ).map_natCast 2
  conv_rhs at h =>
    rw [htwo, substitutionDenominator_derivative]
  linear_combination h

theorem ribbonSubstitution_derivative_two :
    PowerSeries.derivative ℤ
        (PowerSeries.derivative ℤ ribbonSubstitution) =
      -4 * X * substitutionDenominator ^ 3 * (1 - X ^ 2) -
        2 * X * substitutionDenominator ^ 2 := by
  have h := congrArg (PowerSeries.derivative ℤ)
    ribbonSubstitution_derivative
  simp only [map_sub, Derivation.leibniz, smul_eq_mul,
    PowerSeries.derivative_X, PowerSeries.derivative_pow] at h
  rw [substitutionDenominator_derivative] at h
  norm_num at h
  linear_combination h

theorem heightFour_substituted_ordinary_differential :
    let J0 := PowerSeries.subst ribbonSubstitution
      (unrestrictedGeneratingSeries 3)
    let J1 := PowerSeries.subst ribbonSubstitution
      (PowerSeries.derivative ℤ (unrestrictedGeneratingSeries 3))
    let J2 := PowerSeries.subst ribbonSubstitution
      (PowerSeries.derivative ℤ
        (PowerSeries.derivative ℤ (unrestrictedGeneratingSeries 3)))
    (ribbonSubstitution ^ 2 - PowerSeries.C 16 * ribbonSubstitution ^ 4) * J2 +
      (PowerSeries.C 8 * ribbonSubstitution -
          PowerSeries.C 8 * ribbonSubstitution ^ 2 -
          PowerSeries.C 64 * ribbonSubstitution ^ 3) * J1 +
      (PowerSeries.C 12 - PowerSeries.C 20 * ribbonSubstitution -
          PowerSeries.C 32 * ribbonSubstitution ^ 2) * J0 -
        PowerSeries.C 12 = 0 := by
  let hsubst := ribbonSubstitution_hasSubst
  have h := congrArg (PowerSeries.substAlgHom hsubst)
    unrestrictedGeneratingSeries_three_expanded_differential
  simp only [heightFourOrdinaryExpandedOperator, map_add, map_mul, map_sub,
    map_pow, map_zero, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X hsubst, PowerSeries.subst_C] at h
  simpa only [PowerSeries.C_apply] using h

theorem ribbonGeneratingSeries_three_derivative :
    let J0 := PowerSeries.subst ribbonSubstitution
      (unrestrictedGeneratingSeries 3)
    let J1 := PowerSeries.subst ribbonSubstitution
      (PowerSeries.derivative ℤ (unrestrictedGeneratingSeries 3))
    PowerSeries.derivative ℤ (ribbonGeneratingSeries 3) =
      PowerSeries.derivative ℤ substitutionDenominator * J0 +
        substitutionDenominator *
          (J1 * PowerSeries.derivative ℤ ribbonSubstitution) := by
  have hseries := exact_generating_substitution (rank := 3) (by omega)
  rw [hseries]
  change PowerSeries.derivativeFun
      (substitutionDenominator *
        PowerSeries.subst ribbonSubstitution
          (unrestrictedGeneratingSeries 3)) = _
  rw [PowerSeries.derivativeFun_mul]
  change substitutionDenominator *
        PowerSeries.derivative ℤ
          (PowerSeries.subst ribbonSubstitution
            (unrestrictedGeneratingSeries 3)) +
      PowerSeries.subst ribbonSubstitution
          (unrestrictedGeneratingSeries 3) *
        PowerSeries.derivative ℤ substitutionDenominator = _
  rw [PowerSeries.derivative_subst ℤ ribbonSubstitution_hasSubst]
  ring

theorem ribbonGeneratingSeries_three_derivative_two :
    let J0 := PowerSeries.subst ribbonSubstitution
      (unrestrictedGeneratingSeries 3)
    let J1 := PowerSeries.subst ribbonSubstitution
      (PowerSeries.derivative ℤ (unrestrictedGeneratingSeries 3))
    let J2 := PowerSeries.subst ribbonSubstitution
      (PowerSeries.derivative ℤ
        (PowerSeries.derivative ℤ (unrestrictedGeneratingSeries 3)))
    PowerSeries.derivative ℤ
        (PowerSeries.derivative ℤ (ribbonGeneratingSeries 3)) =
      PowerSeries.derivative ℤ
          (PowerSeries.derivative ℤ substitutionDenominator) * J0 +
        2 * PowerSeries.derivative ℤ substitutionDenominator * J1 *
          PowerSeries.derivative ℤ ribbonSubstitution +
        substitutionDenominator *
          (J2 * (PowerSeries.derivative ℤ ribbonSubstitution) ^ 2 +
            J1 * PowerSeries.derivative ℤ
              (PowerSeries.derivative ℤ ribbonSubstitution)) := by
  have h := congrArg (PowerSeries.derivative ℤ)
    ribbonGeneratingSeries_three_derivative
  dsimp only at h ⊢
  simp only [map_add, Derivation.leibniz, smul_eq_mul,
    PowerSeries.derivative_subst ℤ ribbonSubstitution_hasSubst] at h
  linear_combination h

noncomputable def heightFourRibbonChainOne
    (d J0 J1 : ℤ⟦X⟧) : ℤ⟦X⟧ :=
  (-2 * X * d ^ 2) * J0 + d * J1 * (d ^ 2 * (1 - X ^ 2))

noncomputable def heightFourRibbonChainTwo
    (d J0 J1 J2 : ℤ⟦X⟧) : ℤ⟦X⟧ :=
  (-2 * d ^ 2 + 8 * X ^ 2 * d ^ 3) * J0 +
    2 * (-2 * X * d ^ 2) * J1 * (d ^ 2 * (1 - X ^ 2)) +
    d * (J2 * (d ^ 2 * (1 - X ^ 2)) ^ 2 +
      J1 * (-4 * X * d ^ 3 * (1 - X ^ 2) - 2 * X * d ^ 2))

noncomputable def heightFourSubstitutedRaw
    (d J0 J1 J2 : ℤ⟦X⟧) : ℤ⟦X⟧ :=
  let w := X * d
  (w ^ 2 - 16 * w ^ 4) * J2 +
    (8 * w - 8 * w ^ 2 - 64 * w ^ 3) * J1 +
    (12 - 20 * w - 32 * w ^ 2) * J0 - 12

noncomputable def heightFourRibbonRaw
    (d J0 J1 J2 : ℤ⟦X⟧) : ℤ⟦X⟧ :=
  (X ^ 10 - 14 * X ^ 8 + 14 * X ^ 4 - X ^ 2) *
      heightFourRibbonChainTwo d J0 J1 J2 +
    (-2 * X ^ 9 + 8 * X ^ 8 - 30 * X ^ 7 - 8 * X ^ 6 +
        34 * X ^ 5 - 8 * X ^ 4 + 54 * X ^ 3 + 8 * X ^ 2 - 8 * X) *
      heightFourRibbonChainOne d J0 J1 +
    (2 * X ^ 8 - 4 * X ^ 7 - 14 * X ^ 6 + 28 * X ^ 5 +
        34 * X ^ 4 - 44 * X ^ 3 + 38 * X ^ 2 + 20 * X - 12) *
      (d * J0) +
    12 * (1 - X ^ 2) ^ 3

noncomputable def heightFourRibbonDenominatorCertificate
    (d J0 J1 J2 : ℤ⟦X⟧) : ℤ⟦X⟧ :=
  8 * J0 * d ^ 2 * X ^ 10 - 120 * J0 * d ^ 2 * X ^ 8 +
    120 * J0 * d ^ 2 * X ^ 6 - 8 * J0 * d ^ 2 * X ^ 4 +
    10 * J0 * d * X ^ 8 - 16 * J0 * d * X ^ 7 -
    10 * J0 * d * X ^ 6 + 32 * J0 * d * X ^ 5 -
    34 * J0 * d * X ^ 4 - 16 * J0 * d * X ^ 3 -
    14 * J0 * d * X ^ 2 + 12 * J0 * X ^ 6 - 36 * J0 * X ^ 4 +
    36 * J0 * X ^ 2 - 12 * J0 +
    8 * J1 * d ^ 3 * X ^ 11 - 128 * J1 * d ^ 3 * X ^ 9 +
    240 * J1 * d ^ 3 * X ^ 7 - 128 * J1 * d ^ 3 * X ^ 5 +
    8 * J1 * d ^ 3 * X ^ 3 + 8 * J1 * d ^ 2 * X ^ 9 -
    8 * J1 * d ^ 2 * X ^ 8 - 16 * J1 * d ^ 2 * X ^ 7 +
    24 * J1 * d ^ 2 * X ^ 6 - 24 * J1 * d ^ 2 * X ^ 4 +
    16 * J1 * d ^ 2 * X ^ 3 + 8 * J1 * d ^ 2 * X ^ 2 -
    8 * J1 * d ^ 2 * X + 8 * J1 * d * X ^ 7 -
    24 * J1 * d * X ^ 5 + 24 * J1 * d * X ^ 3 - 8 * J1 * d * X +
    J2 * d ^ 4 * X ^ 12 - 17 * J2 * d ^ 4 * X ^ 10 +
    46 * J2 * d ^ 4 * X ^ 8 - 46 * J2 * d ^ 4 * X ^ 6 +
    17 * J2 * d ^ 4 * X ^ 4 - J2 * d ^ 4 * X ^ 2 +
    J2 * d ^ 3 * X ^ 10 - 2 * J2 * d ^ 3 * X ^ 8 +
    2 * J2 * d ^ 3 * X ^ 4 - J2 * d ^ 3 * X ^ 2 +
    J2 * d ^ 2 * X ^ 8 - 3 * J2 * d ^ 2 * X ^ 6 +
    3 * J2 * d ^ 2 * X ^ 4 - J2 * d ^ 2 * X ^ 2

theorem heightFourRibbon_algebra_certificate
    (d J0 J1 J2 : ℤ⟦X⟧) :
    heightFourRibbonRaw d J0 J1 J2 =
      (X ^ 2 - 1) ^ 3 * heightFourSubstitutedRaw d J0 J1 J2 +
        heightFourRibbonDenominatorCertificate d J0 J1 J2 *
          (d * (1 + X ^ 2) - 1) := by
  unfold heightFourRibbonRaw heightFourRibbonChainOne
  unfold heightFourRibbonChainTwo heightFourSubstitutedRaw
  unfold heightFourRibbonDenominatorCertificate
  ring

noncomputable def heightFourRibbonOrdinaryOperator
    (series : ℤ⟦X⟧) : ℤ⟦X⟧ :=
  (X ^ 10 - 14 * X ^ 8 + 14 * X ^ 4 - X ^ 2) *
      PowerSeries.derivative ℤ (PowerSeries.derivative ℤ series) +
    (-2 * X ^ 9 + 8 * X ^ 8 - 30 * X ^ 7 - 8 * X ^ 6 +
        34 * X ^ 5 - 8 * X ^ 4 + 54 * X ^ 3 + 8 * X ^ 2 - 8 * X) *
      PowerSeries.derivative ℤ series +
    (2 * X ^ 8 - 4 * X ^ 7 - 14 * X ^ 6 + 28 * X ^ 5 +
        34 * X ^ 4 - 44 * X ^ 3 + 38 * X ^ 2 + 20 * X - 12) *
      series +
    12 * (1 - X ^ 2) ^ 3

/-- Explicit inhomogeneous polynomial ODE for the actual four-letter ribbon
OGF after the manuscript substitution. -/
theorem ribbonGeneratingSeries_three_differential :
    heightFourRibbonOrdinaryOperator (ribbonGeneratingSeries 3) = 0 := by
  let d := substitutionDenominator
  let J0 := PowerSeries.subst ribbonSubstitution
    (unrestrictedGeneratingSeries 3)
  let J1 := PowerSeries.subst ribbonSubstitution
    (PowerSeries.derivative ℤ (unrestrictedGeneratingSeries 3))
  let J2 := PowerSeries.subst ribbonSubstitution
    (PowerSeries.derivative ℤ
      (PowerSeries.derivative ℤ (unrestrictedGeneratingSeries 3)))
  have hsub : heightFourSubstitutedRaw d J0 J1 J2 = 0 := by
    simpa [heightFourSubstitutedRaw, d, J0, J1, J2, ribbonSubstitution] using
      heightFour_substituted_ordinary_differential
  have hden : d * (1 + X ^ 2) - 1 = 0 := by
    exact sub_eq_zero.mpr substitutionDenominator_mul_one_add_X_sq
  have hraw : heightFourRibbonRaw d J0 J1 J2 = 0 := by
    rw [heightFourRibbon_algebra_certificate, hsub, hden]
    ring
  unfold heightFourRibbonOrdinaryOperator
  rw [ribbonGeneratingSeries_three_derivative_two,
    ribbonGeneratingSeries_three_derivative,
    exact_generating_substitution (rank := 3) (by omega),
    substitutionDenominator_derivative_two,
    substitutionDenominator_derivative,
    ribbonSubstitution_derivative_two,
    ribbonSubstitution_derivative]
  unfold heightFourRibbonRaw heightFourRibbonChainOne
    heightFourRibbonChainTwo at hraw
  dsimp only [d, J0, J1, J2] at hraw
  linear_combination hraw

end FibonacciRibbonKernel
