import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set

noncomputable def regevRealScaleGaussianReal
    (coefficient scale x : ℝ) : ℝ :=
  Real.exp (-coefficient * (x / scale) ^ 2)

noncomputable def regevRealScaleGaussianLine
    (coefficient scale : ℝ) (index : ℤ) : ℝ :=
  regevRealScaleGaussianReal coefficient scale index

theorem regevRealScaleGaussianReal_nonneg
    (coefficient scale x : ℝ) :
    0 ≤ regevRealScaleGaussianReal coefficient scale x :=
  (Real.exp_pos _).le

theorem regevRealScaleGaussianReal_neg
    (coefficient scale x : ℝ) :
    regevRealScaleGaussianReal coefficient scale (-x) =
      regevRealScaleGaussianReal coefficient scale x := by
  unfold regevRealScaleGaussianReal
  apply congrArg Real.exp
  ring

theorem antitoneOn_regevRealScaleGaussianReal
    {coefficient scale : ℝ} (hcoefficient : 0 < coefficient)
    (hscale : 0 < scale) :
    AntitoneOn (regevRealScaleGaussianReal coefficient scale) (Ici 0) := by
  intro x hx y hy hxy
  apply Real.exp_le_exp.mpr
  have hxdiv : 0 ≤ x / scale := div_nonneg hx hscale.le
  have hydiv : 0 ≤ y / scale := div_nonneg hy hscale.le
  have hdiv : x / scale ≤ y / scale :=
    (div_le_div_iff_of_pos_right hscale).2 hxy
  have hsquare : (x / scale) ^ 2 ≤ (y / scale) ^ 2 := by
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsquare hcoefficient.le]

theorem integrable_regevRealScaleGaussianReal
    {coefficient scale : ℝ} (hcoefficient : 0 < coefficient)
    (hscale : 0 < scale) :
    Integrable (regevRealScaleGaussianReal coefficient scale) :=
  (integrable_exp_neg_mul_sq hcoefficient).comp_div hscale.ne'

theorem summable_nat_regevRealScaleGaussianReal
    {coefficient scale : ℝ} (hcoefficient : 0 < coefficient)
    (hscale : 0 < scale) :
    Summable (fun index : ℕ =>
      regevRealScaleGaussianReal coefficient scale index) :=
  (antitoneOn_regevRealScaleGaussianReal hcoefficient hscale).summable_of_integrableOn_Ioi_zero
      (integrable_regevRealScaleGaussianReal hcoefficient hscale).integrableOn
      (fun _ _ => regevRealScaleGaussianReal_nonneg coefficient scale _)

theorem summable_regevRealScaleGaussianLine
    {coefficient scale : ℝ} (hcoefficient : 0 < coefficient)
    (hscale : 0 < scale) :
    Summable (regevRealScaleGaussianLine coefficient scale) := by
  have hnat := summable_nat_regevRealScaleGaussianReal hcoefficient hscale
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa [regevRealScaleGaussianLine] using hnat
  · refine hnat.congr (fun index => ?_)
    simpa [regevRealScaleGaussianLine] using
      (regevRealScaleGaussianReal_neg coefficient scale (index : ℝ)).symm

theorem regevRealScaleGaussianLine_total_bound
    {coefficient scale : ℝ} (hcoefficient : 0 < coefficient)
    (hscale : 1 ≤ scale) :
    (∑' index : ℤ, regevRealScaleGaussianLine coefficient scale index) /
        scale ≤ 2 + 2 * Real.sqrt (Real.pi / coefficient) := by
  let sampled := regevRealScaleGaussianReal coefficient scale
  have hscalePos : 0 < scale := zero_lt_one.trans_le hscale
  have hanti : AntitoneOn sampled (Ici 0) :=
    antitoneOn_regevRealScaleGaussianReal hcoefficient hscalePos
  have hintegrable : Integrable sampled :=
    integrable_regevRealScaleGaussianReal hcoefficient hscalePos
  have hnat : Summable (fun index : ℕ => sampled index) :=
    summable_nat_regevRealScaleGaussianReal hcoefficient hscalePos
  have hnatBound := hanti.tsum_le_integral hintegrable.integrableOn
    (fun _ _ => regevRealScaleGaussianReal_nonneg coefficient scale _)
  have hwholeIntegral :
      (∫ x : ℝ, sampled x) =
        scale * Real.sqrt (Real.pi / coefficient) := by
    have hscaleIntegral := Measure.integral_comp_div
      (fun x : ℝ => Real.exp (-coefficient * x ^ 2)) scale
    rw [integral_gaussian coefficient] at hscaleIntegral
    simpa [sampled, regevRealScaleGaussianReal, abs_of_pos hscalePos,
      smul_eq_mul] using hscaleIntegral
  have hhalfIntegral :
      (∫ x in Ioi (0 : ℝ), sampled x) ≤
        scale * Real.sqrt (Real.pi / coefficient) := by
    rw [← hwholeIntegral]
    exact setIntegral_le_integral hintegrable
      (Eventually.of_forall fun _ =>
        regevRealScaleGaussianReal_nonneg coefficient scale _)
  have hnatCoarse :
      (∑' index : ℕ, sampled index) ≤
        1 + scale * Real.sqrt (Real.pi / coefficient) := by
    calc
      (∑' index : ℕ, sampled index) ≤
          sampled 0 + ∫ x in Ioi (0 : ℝ), sampled x := hnatBound
      _ ≤ 1 + scale * Real.sqrt (Real.pi / coefficient) := by
        simpa [sampled, regevRealScaleGaussianReal] using
          add_le_add_left hhalfIntegral 1
  have hnegative : Summable (fun index : ℕ =>
      regevRealScaleGaussianLine coefficient scale (-index)) := by
    refine hnat.congr (fun index => ?_)
    simpa [sampled, regevRealScaleGaussianLine] using
      (regevRealScaleGaussianReal_neg coefficient scale (index : ℝ)).symm
  have hintEq := Summable.tsum_of_nat_of_neg hnat hnegative
  have hpositiveFunction :
      (fun index : ℕ => regevRealScaleGaussianLine coefficient scale index) =
        (fun index : ℕ => sampled index) := by rfl
  have hnegativeFunction :
      (fun index : ℕ => regevRealScaleGaussianLine coefficient scale (-index)) =
        (fun index : ℕ => sampled index) := by
    funext index
    simpa [sampled, regevRealScaleGaussianLine] using
      regevRealScaleGaussianReal_neg coefficient scale (index : ℝ)
  have hlineEq :
      (∑' index : ℤ, regevRealScaleGaussianLine coefficient scale index) =
        2 * ∑' index : ℕ, sampled index - 1 := by
    rw [hpositiveFunction, hnegativeFunction] at hintEq
    calc
      _ = (∑' index : ℕ, sampled index) +
          (∑' index : ℕ, sampled index) -
            regevRealScaleGaussianLine coefficient scale 0 := hintEq
      _ = _ := by
        rw [show regevRealScaleGaussianLine coefficient scale 0 = 1 by
          simp [regevRealScaleGaussianLine, regevRealScaleGaussianReal]]
        ring
  have hlineCoarse :
      (∑' index : ℤ, regevRealScaleGaussianLine coefficient scale index) ≤
        2 * (1 + scale * Real.sqrt (Real.pi / coefficient)) := by
    rw [hlineEq]
    nlinarith
  rw [div_le_iff₀ hscalePos]
  calc
    _ ≤ 2 * (1 + scale * Real.sqrt (Real.pi / coefficient)) := hlineCoarse
    _ ≤ (2 + 2 * Real.sqrt (Real.pi / coefficient)) * scale := by
      nlinarith [Real.sqrt_nonneg (Real.pi / coefficient)]

end FibonacciRibbonKernel
