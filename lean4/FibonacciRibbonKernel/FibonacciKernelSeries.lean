import FibonacciRibbonKernel.FibonacciScaleKernel
import FibonacciRibbonKernel.RibbonRationalChain

namespace FibonacciRibbonKernel

open PowerSeries

def fibonacciScaleKernelQ (scale : ℚ) : ℕ → ℚ
  | 0 => 1
  | 1 => scale
  | power + 2 =>
      scale * fibonacciScaleKernelQ scale (power + 1) -
        fibonacciScaleKernelQ scale power

noncomputable def fibonacciScaleSeriesQ (scale : ℚ) : ℚ⟦X⟧ :=
  PowerSeries.mk (fibonacciScaleKernelQ scale)

noncomputable def geometricScaleSeriesQ (scale : ℚ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun power => scale ^ power

noncomputable def fibonacciScaleDenominatorQ (scale : ℚ) : ℚ⟦X⟧ :=
  1 - PowerSeries.C scale * PowerSeries.X + PowerSeries.X ^ 2

@[simp] theorem fibonacciScaleSeriesQ_coeff (scale : ℚ) (power : ℕ) :
    PowerSeries.coeff power (fibonacciScaleSeriesQ scale) =
      fibonacciScaleKernelQ scale power := by
  simp [fibonacciScaleSeriesQ]

@[simp] theorem geometricScaleSeriesQ_coeff (scale : ℚ) (power : ℕ) :
    PowerSeries.coeff power (geometricScaleSeriesQ scale) = scale ^ power := by
  simp [geometricScaleSeriesQ]

theorem coeff_X_mul_series (series : ℚ⟦X⟧) (power : ℕ) :
    PowerSeries.coeff power (PowerSeries.X * series) =
      if 1 ≤ power then PowerSeries.coeff (power - 1) series else 0 := by
  rw [show (PowerSeries.X : ℚ⟦X⟧) = PowerSeries.X ^ 1 by simp,
    PowerSeries.coeff_X_pow_mul']

theorem fibonacciScaleDenominatorQ_mul_series (scale : ℚ) :
    fibonacciScaleDenominatorQ scale * fibonacciScaleSeriesQ scale = 1 := by
  have hexpand :
      fibonacciScaleDenominatorQ scale * fibonacciScaleSeriesQ scale =
        fibonacciScaleSeriesQ scale -
            PowerSeries.C scale *
              (PowerSeries.X * fibonacciScaleSeriesQ scale) +
          PowerSeries.X ^ 2 * fibonacciScaleSeriesQ scale := by
    unfold fibonacciScaleDenominatorQ
    ring
  rw [hexpand]
  ext power
  induction power using Nat.twoStepInduction with
  | zero =>
      simp [fibonacciScaleSeriesQ, fibonacciScaleKernelQ]
  | one =>
      simp [fibonacciScaleSeriesQ, fibonacciScaleKernelQ,
        PowerSeries.coeff_X_pow_mul']
  | more power _hzero _hone =>
      rw [map_add, map_sub, fibonacciScaleSeriesQ_coeff,
        PowerSeries.coeff_C_mul]
      rw [coeff_X_mul_series, PowerSeries.coeff_X_pow_mul']
      simp only [if_pos (by omega : 1 ≤ power + 2),
        if_pos (by omega : 2 ≤ power + 2),
        PowerSeries.coeff_one]
      rw [show power + 2 - 1 = power + 1 by omega,
        show power + 2 - 2 = power by omega,
        fibonacciScaleSeriesQ_coeff, fibonacciScaleSeriesQ_coeff,
        fibonacciScaleKernelQ]
      rw [if_neg (by omega : power + 2 ≠ 0)]
      ring

theorem geometricScaleDenominatorQ_mul_series (scale : ℚ) :
    (1 - PowerSeries.C scale * PowerSeries.X) *
        geometricScaleSeriesQ scale = 1 := by
  have hexpand :
      (1 - PowerSeries.C scale * PowerSeries.X) *
          geometricScaleSeriesQ scale =
        geometricScaleSeriesQ scale -
          PowerSeries.C scale *
            (PowerSeries.X * geometricScaleSeriesQ scale) := by ring
  rw [hexpand]
  ext power
  cases power with
  | zero => simp [geometricScaleSeriesQ]
  | succ power =>
      rw [map_sub, geometricScaleSeriesQ_coeff,
        PowerSeries.coeff_C_mul]
      rw [coeff_X_mul_series]
      rw [if_pos (by omega : 1 ≤ power + 1)]
      rw [PowerSeries.coeff_one,
        if_neg (by omega : power + 1 ≠ 0)]
      rw [show power + 1 - 1 = power by omega,
        geometricScaleSeriesQ_coeff,
        pow_succ]
      ring

theorem subst_geometricScaleSeriesQ_inverse (scale : ℚ) :
    (1 - PowerSeries.C scale * ribbonSubstitutionQ) *
        PowerSeries.subst ribbonSubstitutionQ (geometricScaleSeriesQ scale) = 1 := by
  have hmapped := congrArg (PowerSeries.subst ribbonSubstitutionQ)
    (geometricScaleDenominatorQ_mul_series scale)
  rw [PowerSeries.subst_mul ribbonSubstitutionQ_hasSubst] at hmapped
  rw [PowerSeries.subst_sub ribbonSubstitutionQ_hasSubst] at hmapped
  rw [PowerSeries.subst_mul ribbonSubstitutionQ_hasSubst] at hmapped
  rw [PowerSeries.subst_C,
    PowerSeries.subst_X ribbonSubstitutionQ_hasSubst] at hmapped
  have hone : PowerSeries.subst ribbonSubstitutionQ (1 : ℚ⟦X⟧) = 1 := by
    change PowerSeries.subst ribbonSubstitutionQ (PowerSeries.C 1) = 1
    rw [PowerSeries.subst_C]
    rfl
  rw [hone] at hmapped
  exact hmapped

theorem fibonacciScaleDenominatorQ_mul_prefactor (scale : ℚ) :
    fibonacciScaleDenominatorQ scale * ribbonInverseQuadraticQ =
      1 - PowerSeries.C scale * ribbonSubstitutionQ := by
  unfold fibonacciScaleDenominatorQ
  rw [ribbonSubstitutionQ_eq]
  have hinverse := ribbonInverseQuadraticQ_mul_plus
  have hplus : (ribbonQuadraticPlus : ℚ⟦X⟧) = 1 + PowerSeries.X ^ 2 := by
    simp [ribbonQuadraticPlus]
  rw [hplus] at hinverse
  linear_combination hinverse

theorem ribbonTransform_geometricScaleSeriesQ (scale : ℚ) :
    ribbonInverseQuadraticQ *
        PowerSeries.subst ribbonSubstitutionQ (geometricScaleSeriesQ scale) =
      fibonacciScaleSeriesQ scale := by
  let transformed := ribbonInverseQuadraticQ *
    PowerSeries.subst ribbonSubstitutionQ (geometricScaleSeriesQ scale)
  have htransformed : fibonacciScaleDenominatorQ scale * transformed = 1 := by
    dsimp only [transformed]
    rw [← mul_assoc, fibonacciScaleDenominatorQ_mul_prefactor]
    exact subst_geometricScaleSeriesQ_inverse scale
  have hfibonacci := fibonacciScaleDenominatorQ_mul_series scale
  calc
    transformed = transformed * 1 := by ring
    _ = transformed *
        (fibonacciScaleDenominatorQ scale * fibonacciScaleSeriesQ scale) := by
      rw [hfibonacci]
    _ = (fibonacciScaleDenominatorQ scale * transformed) *
        fibonacciScaleSeriesQ scale := by ring
    _ = fibonacciScaleSeriesQ scale := by rw [htransformed, one_mul]

end FibonacciRibbonKernel
