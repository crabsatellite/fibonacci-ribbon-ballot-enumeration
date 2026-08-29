import FibonacciRibbonKernel.FixedRankSingularityGeometry
import Mathlib.RingTheory.PowerSeries.Binomial

namespace FibonacciRibbonKernel

open PowerSeries

/-!
# Exact formal power--logarithm models

The regular-singular systems in the fixed-rank proof produce two kinds of
leading terms.  A half-integral exponent is represented by a binomial series;
an integral exponent is represented by a polynomial times a logarithm.  This
file defines both carriers as literal real formal power series and proves the
coefficient recurrences that will be used by the transfer layer.
-/

/-- Formal series for `log (1 - scale * X)`, with zero constant term. -/
noncomputable def formalLogOneSub (scale : ℝ) : ℝ⟦X⟧ :=
  PowerSeries.mk fun index =>
    if index = 0 then 0 else -(scale ^ index / (index : ℝ))

@[simp] theorem formalLogOneSub_coeff_zero (scale : ℝ) :
    PowerSeries.coeff 0 (formalLogOneSub scale) = 0 := by
  simp [formalLogOneSub]

@[simp] theorem formalLogOneSub_coeff_succ (scale : ℝ) (index : ℕ) :
    PowerSeries.coeff (index + 1) (formalLogOneSub scale) =
      -(scale ^ (index + 1) / (index + 1 : ℝ)) := by
  simp [formalLogOneSub]

/-- Literal formal carrier for `(1 - scale * X)^exponent`. -/
noncomputable def rescaledBinomialSeries
    (exponent scale : ℝ) : ℝ⟦X⟧ :=
  PowerSeries.rescale (-scale) (PowerSeries.binomialSeries ℝ exponent)

@[simp] theorem rescaledBinomialSeries_coeff
    (exponent scale : ℝ) (index : ℕ) :
    PowerSeries.coeff index (rescaledBinomialSeries exponent scale) =
      (-scale) ^ index * Ring.choose exponent index := by
  simp [rescaledBinomialSeries, PowerSeries.coeff_rescale]

theorem rescaledBinomialSeries_add
    (left right scale : ℝ) :
    rescaledBinomialSeries (left + right) scale =
      rescaledBinomialSeries left scale *
        rescaledBinomialSeries right scale := by
  unfold rescaledBinomialSeries
  rw [PowerSeries.binomialSeries_add, map_mul]

theorem rescaledBinomialSeries_one (scale : ℝ) :
    rescaledBinomialSeries 1 scale =
      1 - PowerSeries.C scale * PowerSeries.X := by
  unfold rescaledBinomialSeries
  rw [show (1 : ℝ) = (1 : ℕ) by norm_num,
    PowerSeries.binomialSeries_nat]
  simp [map_add, PowerSeries.rescale_X]
  ring

theorem coeff_C_mul_X_mul
    (scale : ℝ) (series : ℝ⟦X⟧) (index : ℕ) :
    PowerSeries.coeff (index + 1)
        (PowerSeries.C scale * PowerSeries.X * series) =
      scale * PowerSeries.coeff index series := by
  rw [mul_assoc, PowerSeries.coeff_C_mul]
  simp

/-- Half-integral singular model `(1 - scale*X)^(order-1/2)`. -/
noncomputable def halfPowerSeries (order : ℕ) (scale : ℝ) : ℝ⟦X⟧ :=
  rescaledBinomialSeries ((order : ℝ) - 1 / 2) scale

@[simp] theorem halfPowerSeries_coeff
    (order : ℕ) (scale : ℝ) (index : ℕ) :
    PowerSeries.coeff index (halfPowerSeries order scale) =
      (-scale) ^ index *
        Ring.choose ((order : ℝ) - 1 / 2) index := by
  simp [halfPowerSeries]

theorem halfPowerSeries_succ (order : ℕ) (scale : ℝ) :
    halfPowerSeries (order + 1) scale =
      (1 - PowerSeries.C scale * PowerSeries.X) *
        halfPowerSeries order scale := by
  have hexponent : (((order + 1 : ℕ) : ℝ) - 1 / 2) =
      1 + ((order : ℝ) - 1 / 2) := by
    push_cast
    ring
  rw [halfPowerSeries, halfPowerSeries, hexponent,
    rescaledBinomialSeries_add, rescaledBinomialSeries_one]

theorem halfPowerSeries_coeff_succ_order
    (order index : ℕ) (scale : ℝ) :
    PowerSeries.coeff (index + 1) (halfPowerSeries (order + 1) scale) =
      PowerSeries.coeff (index + 1) (halfPowerSeries order scale) -
        scale * PowerSeries.coeff index (halfPowerSeries order scale) := by
  rw [halfPowerSeries_succ]
  ring_nf
  rw [map_add, map_neg, show 1 + index = index + 1 by omega,
    coeff_C_mul_X_mul]
  ring

/-- Integral singular model `(1-scale*X)^order log(1-scale*X)`. -/
noncomputable def integerPowerLogSeries
    (order : ℕ) (scale : ℝ) : ℝ⟦X⟧ :=
  (1 - PowerSeries.C scale * PowerSeries.X) ^ order *
    formalLogOneSub scale

theorem integerPowerLogSeries_zero (scale : ℝ) :
    integerPowerLogSeries 0 scale = formalLogOneSub scale := by
  simp [integerPowerLogSeries]

theorem integerPowerLogSeries_succ (order : ℕ) (scale : ℝ) :
    integerPowerLogSeries (order + 1) scale =
      (1 - PowerSeries.C scale * PowerSeries.X) *
        integerPowerLogSeries order scale := by
  unfold integerPowerLogSeries
  rw [pow_succ']
  ring

theorem integerPowerLogSeries_coeff_succ_order
    (order index : ℕ) (scale : ℝ) :
    PowerSeries.coeff (index + 1)
        (integerPowerLogSeries (order + 1) scale) =
      PowerSeries.coeff (index + 1)
          (integerPowerLogSeries order scale) -
        scale * PowerSeries.coeff index
          (integerPowerLogSeries order scale) := by
  rw [integerPowerLogSeries_succ]
  ring_nf
  rw [map_add, map_neg, show 1 + index = index + 1 by omega,
    coeff_C_mul_X_mul]
  ring

end FibonacciRibbonKernel
