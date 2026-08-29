import FibonacciRibbonKernel.PowerLogModels
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Analysis.SpecialFunctions.Choose

namespace FibonacciRibbonKernel

open PowerSeries
open Filter Asymptotics

/-!
# Coefficients of the integral power--logarithm model

For `index > order`, the coefficient of
`(1-scale*X)^order log(1-scale*X)` is exactly

`(-1)^(order+1) order! scale^index / index.descFactorial (order+1)`.

This exact formula covers the logarithmic cases of the manuscript transfer
theorem and exposes the required `index^(-(order+1))` decay without an
external singularity-analysis axiom.
-/

noncomputable def integerPowerLogClosedCoefficient
    (order : ℕ) (scale : ℝ) (index : ℕ) : ℝ :=
  (-1 : ℝ) ^ (order + 1) * (order.factorial : ℝ) * scale ^ index /
    (index.descFactorial (order + 1) : ℝ)

noncomputable def integerPowerLogLeadingCoefficient
    (order : ℕ) (scale : ℝ) (index : ℕ) : ℝ :=
  (-1 : ℝ) ^ (order + 1) * (order.factorial : ℝ) * scale ^ index /
    (index : ℝ) ^ (order + 1)

noncomputable def integerPowerLogRpowLeadingCoefficient
    (order : ℕ) (scale : ℝ) (index : ℕ) : ℝ :=
  (-1 : ℝ) ^ (order + 1) * (order.factorial : ℝ) * scale ^ index *
    (index : ℝ) ^ (-(order + 1 : ℕ) : ℝ)

theorem integerPowerLogClosedCoefficient_zero
    (scale : ℝ) (index : ℕ) (_hindex : 0 < index) :
    integerPowerLogClosedCoefficient 0 scale index =
      -(scale ^ index / (index : ℝ)) := by
  unfold integerPowerLogClosedCoefficient
  rw [Nat.descFactorial_one]
  norm_num
  ring

theorem integerPowerLogSeries_coeff_closed
    (order : ℕ) (scale : ℝ) (index : ℕ) (hindex : order < index) :
    PowerSeries.coeff index (integerPowerLogSeries order scale) =
      integerPowerLogClosedCoefficient order scale index := by
  induction order generalizing index with
  | zero =>
      rw [integerPowerLogSeries_zero]
      rw [formalLogOneSub, PowerSeries.coeff_mk, if_neg (by omega)]
      exact (integerPowerLogClosedCoefficient_zero scale index hindex).symm
  | succ order ih =>
      let predecessor := index - 1
      have hindexEq : predecessor + 1 = index := by
        dsimp only [predecessor]
        omega
      have hpredBound : order < predecessor := by
        dsimp only [predecessor]
        omega
      rw [← hindexEq,
        integerPowerLogSeries_coeff_succ_order order predecessor scale]
      rw [ih (predecessor + 1) (by omega), ih predecessor hpredBound]
      rw [hindexEq]
      have hbaseBound : order ≤ predecessor := by omega
      have hdfCurrent :
          index.descFactorial (order + 1) =
            index * predecessor.descFactorial order := by
        have h := Nat.succ_descFactorial_succ predecessor order
        simpa [hindexEq] using h
      have hdfPred :
          predecessor.descFactorial (order + 1) =
            (predecessor - order) * predecessor.descFactorial order :=
        Nat.descFactorial_succ predecessor order
      have hdfNext :
          index.descFactorial (order + 2) =
            index * predecessor.descFactorial (order + 1) := by
        have h := Nat.succ_descFactorial_succ predecessor (order + 1)
        simpa [hindexEq] using h
      have hdfBaseNe : predecessor.descFactorial order ≠ 0 := by
        intro hzero
        have hlt := Nat.descFactorial_eq_zero_iff_lt.mp hzero
        omega
      have hindexNatNe : index ≠ 0 := by omega
      have hindexNe : (index : ℝ) ≠ 0 := by
        exact_mod_cast hindexNatNe
      have hsubReal : (order : ℝ) < predecessor := by
        exact_mod_cast hpredBound
      have hsubRealNe : (predecessor : ℝ) - order ≠ 0 :=
        sub_ne_zero.mpr (ne_of_gt hsubReal)
      have hdfBaseRealNe :
          (predecessor.descFactorial order : ℝ) ≠ 0 := by
        exact_mod_cast hdfBaseNe
      unfold integerPowerLogClosedCoefficient
      rw [hdfCurrent, hdfNext, hdfPred, Nat.factorial_succ]
      push_cast
      rw [show scale ^ index = scale ^ predecessor * scale by
        rw [← hindexEq, pow_succ]]
      have hcastSub :
          ((predecessor - order : ℕ) : ℝ) =
            (predecessor : ℝ) - order := by
        exact_mod_cast (Nat.cast_sub hbaseBound :
          ((predecessor - order : ℕ) : ℝ) = predecessor - order)
      rw [hcastSub]
      have hindexCast : (index : ℝ) = predecessor + 1 := by
        exact_mod_cast hindexEq.symm
      rw [hindexCast]
      field_simp [hdfBaseRealNe, hindexNe, hsubRealNe]
      ring

theorem integerPowerLogClosedCoefficient_isEquivalent_leading
    (order : ℕ) (scale : ℝ) :
    integerPowerLogClosedCoefficient order scale ~[atTop]
      integerPowerLogLeadingCoefficient order scale := by
  unfold integerPowerLogClosedCoefficient integerPowerLogLeadingCoefficient
  exact IsEquivalent.refl.div (isEquivalent_descFactorial (order + 1))

theorem integerPowerLogLeadingCoefficient_eventuallyEq_rpow
    (order : ℕ) (scale : ℝ) :
    Filter.EventuallyEq Filter.atTop
      (integerPowerLogLeadingCoefficient order scale)
      (integerPowerLogRpowLeadingCoefficient order scale) := by
  filter_upwards [Filter.eventually_ne_atTop 0] with index hindex
  have hindexNonneg : (0 : ℝ) ≤ index := by positivity
  unfold integerPowerLogLeadingCoefficient
  unfold integerPowerLogRpowLeadingCoefficient
  rw [Real.rpow_neg hindexNonneg, Real.rpow_natCast]
  ring

theorem integerPowerLogClosedCoefficient_isEquivalent_rpow
    (order : ℕ) (scale : ℝ) :
    integerPowerLogClosedCoefficient order scale ~[atTop]
      integerPowerLogRpowLeadingCoefficient order scale :=
  (integerPowerLogClosedCoefficient_isEquivalent_leading order scale).trans
    (integerPowerLogLeadingCoefficient_eventuallyEq_rpow order scale).isEquivalent

end FibonacciRibbonKernel
