import FibonacciRibbonKernel.CosineCubeIntegralIdentity
import FibonacciRibbonKernel.FibonacciKernelSeries

namespace FibonacciRibbonKernel

open PowerSeries

noncomputable def ribbonSubstitutionR : ℝ⟦X⟧ :=
  PowerSeries.map (Rat.castHom ℝ) ribbonSubstitutionQ

noncomputable def ribbonInverseQuadraticR : ℝ⟦X⟧ :=
  PowerSeries.map (Rat.castHom ℝ) ribbonInverseQuadraticQ

noncomputable def geometricScaleSeriesR (scale : ℝ) : ℝ⟦X⟧ :=
  PowerSeries.mk fun power => scale ^ power

noncomputable def fibonacciScaleSeriesR (scale : ℝ) : ℝ⟦X⟧ :=
  PowerSeries.mk (fibonacciScaleKernel scale)

noncomputable def fibonacciScaleDenominatorR (scale : ℝ) : ℝ⟦X⟧ :=
  1 - PowerSeries.C scale * PowerSeries.X + PowerSeries.X ^ 2

@[simp] theorem geometricScaleSeriesR_coeff (scale : ℝ) (power : ℕ) :
    PowerSeries.coeff power (geometricScaleSeriesR scale) = scale ^ power := by
  simp [geometricScaleSeriesR]

@[simp] theorem fibonacciScaleSeriesR_coeff (scale : ℝ) (power : ℕ) :
    PowerSeries.coeff power (fibonacciScaleSeriesR scale) =
      fibonacciScaleKernel scale power := by
  simp [fibonacciScaleSeriesR]

theorem coeff_X_mul_seriesR (series : ℝ⟦X⟧) (power : ℕ) :
    PowerSeries.coeff power (PowerSeries.X * series) =
      if 1 ≤ power then PowerSeries.coeff (power - 1) series else 0 := by
  rw [show (PowerSeries.X : ℝ⟦X⟧) = PowerSeries.X ^ 1 by simp,
    PowerSeries.coeff_X_pow_mul']

theorem ribbonSubstitutionR_eq :
    ribbonSubstitutionR = PowerSeries.X * ribbonInverseQuadraticR := by
  unfold ribbonSubstitutionR ribbonInverseQuadraticR
  rw [ribbonSubstitutionQ_eq, map_mul, PowerSeries.map_X]

theorem ribbonInverseQuadraticR_mul_plus :
    ribbonInverseQuadraticR * (1 + PowerSeries.X ^ 2) = 1 := by
  have hmapped := congrArg (PowerSeries.map (Rat.castHom ℝ))
    ribbonInverseQuadraticQ_mul_plus
  simpa [ribbonInverseQuadraticR, ribbonQuadraticPlus,
    map_mul, map_add, map_pow] using hmapped

theorem ribbonSubstitutionR_constantCoeff :
    PowerSeries.constantCoeff ribbonSubstitutionR = 0 := by
  rw [ribbonSubstitutionR_eq]
  simp

theorem ribbonSubstitutionR_hasSubst :
    PowerSeries.HasSubst ribbonSubstitutionR :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    ribbonSubstitutionR_constantCoeff

theorem fibonacciScaleDenominatorR_mul_series (scale : ℝ) :
    fibonacciScaleDenominatorR scale * fibonacciScaleSeriesR scale = 1 := by
  have hexpand :
      fibonacciScaleDenominatorR scale * fibonacciScaleSeriesR scale =
        fibonacciScaleSeriesR scale -
            PowerSeries.C scale *
              (PowerSeries.X * fibonacciScaleSeriesR scale) +
          PowerSeries.X ^ 2 * fibonacciScaleSeriesR scale := by
    unfold fibonacciScaleDenominatorR
    ring
  rw [hexpand]
  ext power
  induction power using Nat.twoStepInduction with
  | zero => simp [fibonacciScaleSeriesR]
  | one =>
      simp [fibonacciScaleSeriesR, PowerSeries.coeff_X_pow_mul']
  | more power _hzero _hone =>
      rw [map_add, map_sub, fibonacciScaleSeriesR_coeff,
        PowerSeries.coeff_C_mul, coeff_X_mul_seriesR,
        PowerSeries.coeff_X_pow_mul']
      simp only [if_pos (by omega : 1 ≤ power + 2),
        if_pos (by omega : 2 ≤ power + 2), PowerSeries.coeff_one]
      rw [show power + 2 - 1 = power + 1 by omega,
        show power + 2 - 2 = power by omega,
        fibonacciScaleSeriesR_coeff, fibonacciScaleSeriesR_coeff,
        fibonacciScaleKernel_succ_succ,
        if_neg (by omega : power + 2 ≠ 0)]
      ring

theorem geometricScaleDenominatorR_mul_series (scale : ℝ) :
    (1 - PowerSeries.C scale * PowerSeries.X) *
        geometricScaleSeriesR scale = 1 := by
  have hexpand :
      (1 - PowerSeries.C scale * PowerSeries.X) *
          geometricScaleSeriesR scale =
        geometricScaleSeriesR scale -
          PowerSeries.C scale *
            (PowerSeries.X * geometricScaleSeriesR scale) := by ring
  rw [hexpand]
  ext power
  cases power with
  | zero => simp [geometricScaleSeriesR]
  | succ power =>
      rw [map_sub, geometricScaleSeriesR_coeff,
        PowerSeries.coeff_C_mul, coeff_X_mul_seriesR,
        if_pos (by omega : 1 ≤ power + 1)]
      rw [PowerSeries.coeff_one, if_neg (by omega : power + 1 ≠ 0),
        show power + 1 - 1 = power by omega,
        geometricScaleSeriesR_coeff, pow_succ]
      ring

theorem subst_geometricScaleSeriesR_inverse (scale : ℝ) :
    (1 - PowerSeries.C scale * ribbonSubstitutionR) *
        PowerSeries.subst ribbonSubstitutionR (geometricScaleSeriesR scale) = 1 := by
  have hmapped := congrArg (PowerSeries.subst ribbonSubstitutionR)
    (geometricScaleDenominatorR_mul_series scale)
  rw [PowerSeries.subst_mul ribbonSubstitutionR_hasSubst,
    PowerSeries.subst_sub ribbonSubstitutionR_hasSubst,
    PowerSeries.subst_mul ribbonSubstitutionR_hasSubst,
    PowerSeries.subst_C,
    PowerSeries.subst_X ribbonSubstitutionR_hasSubst] at hmapped
  have hone : PowerSeries.subst ribbonSubstitutionR (1 : ℝ⟦X⟧) = 1 := by
    change PowerSeries.subst ribbonSubstitutionR (PowerSeries.C 1) = 1
    rw [PowerSeries.subst_C]
    rfl
  rw [hone] at hmapped
  exact hmapped

theorem fibonacciScaleDenominatorR_mul_prefactor (scale : ℝ) :
    fibonacciScaleDenominatorR scale * ribbonInverseQuadraticR =
      1 - PowerSeries.C scale * ribbonSubstitutionR := by
  unfold fibonacciScaleDenominatorR
  rw [ribbonSubstitutionR_eq]
  have hinverse := ribbonInverseQuadraticR_mul_plus
  linear_combination hinverse

theorem ribbonTransform_geometricScaleSeriesR (scale : ℝ) :
    ribbonInverseQuadraticR *
        PowerSeries.subst ribbonSubstitutionR (geometricScaleSeriesR scale) =
      fibonacciScaleSeriesR scale := by
  let transformed := ribbonInverseQuadraticR *
    PowerSeries.subst ribbonSubstitutionR (geometricScaleSeriesR scale)
  have htransformed : fibonacciScaleDenominatorR scale * transformed = 1 := by
    dsimp only [transformed]
    rw [← mul_assoc, fibonacciScaleDenominatorR_mul_prefactor]
    exact subst_geometricScaleSeriesR_inverse scale
  have hfibonacci := fibonacciScaleDenominatorR_mul_series scale
  calc
    transformed = transformed * 1 := by ring
    _ = transformed *
        (fibonacciScaleDenominatorR scale * fibonacciScaleSeriesR scale) := by
      rw [hfibonacci]
    _ = (fibonacciScaleDenominatorR scale * transformed) *
        fibonacciScaleSeriesR scale := by ring
    _ = fibonacciScaleSeriesR scale := by rw [htransformed, one_mul]

end FibonacciRibbonKernel
