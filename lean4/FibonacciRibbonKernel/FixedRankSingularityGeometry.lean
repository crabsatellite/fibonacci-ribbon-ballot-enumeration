import FibonacciRibbonKernel.FixedRankLocalGeometry

namespace FibonacciRibbonKernel

/-!
# Separation of the fixed-rank Bessel singular scales

This file formalizes the real-algebraic radius comparison used in the proof of
`thm:fixed-rank-asymptotic`.  For a positive scale `s >= 2`, the closest
solution of `z / (1 + z^2) = 1 / s` is

`(s - sqrt (s^2 - 4)) / 2 = 2 / (s + sqrt (s^2 - 4))`.

The latter expression makes the strict separation from the leading rank scale
transparent.  Scales of absolute value at most two have preimage radius one;
the leading radius is strictly smaller than one for every alphabet size at
least three.
-/

/-- Smaller positive preimage of `1 / scale` under `z / (1 + z^2)`. -/
noncomputable def positiveScalePreimage (scale : ℝ) : ℝ :=
  (scale - Real.sqrt (scale ^ 2 - 4)) / 2

/-- Radius of the closest preimage associated with an absolute Bessel scale. -/
noncomputable def besselScalePreimageRadius (scale : ℝ) : ℝ :=
  if 2 ≤ scale then positiveScalePreimage scale else 1

theorem positiveScalePreimage_eq_two_div
    {scale : ℝ} (hscale : 2 ≤ scale) :
    positiveScalePreimage scale =
      2 / (scale + Real.sqrt (scale ^ 2 - 4)) := by
  have hdisc : 0 ≤ scale ^ 2 - 4 := by nlinarith
  have hsqrtSq : (Real.sqrt (scale ^ 2 - 4)) ^ 2 = scale ^ 2 - 4 :=
    Real.sq_sqrt hdisc
  have hdenomPos : 0 < scale + Real.sqrt (scale ^ 2 - 4) := by
    positivity
  rw [positiveScalePreimage]
  field_simp
  nlinarith

theorem positiveScalePreimage_pos
    {scale : ℝ} (hscale : 2 ≤ scale) :
    0 < positiveScalePreimage scale := by
  rw [positiveScalePreimage_eq_two_div hscale]
  positivity

theorem positiveScalePreimage_le_one
    {scale : ℝ} (hscale : 2 ≤ scale) :
    positiveScalePreimage scale ≤ 1 := by
  rw [positiveScalePreimage_eq_two_div hscale]
  have hsqrtNonneg : 0 ≤ Real.sqrt (scale ^ 2 - 4) := Real.sqrt_nonneg _
  have hdenomPos : 0 < scale + Real.sqrt (scale ^ 2 - 4) := by
    positivity
  apply (div_le_one hdenomPos).2
  linarith

/-- The positive preimage is a root of the literal pullback quadratic. -/
theorem positiveScalePreimage_quadratic
    {scale : ℝ} (hscale : 2 ≤ scale) :
    positiveScalePreimage scale ^ 2 -
        scale * positiveScalePreimage scale + 1 = 0 := by
  have hdisc : 0 ≤ scale ^ 2 - 4 := by nlinarith
  have hsqrtSq : (Real.sqrt (scale ^ 2 - 4)) ^ 2 = scale ^ 2 - 4 :=
    Real.sq_sqrt hdisc
  rw [positiveScalePreimage]
  nlinarith

/-- The second real root of the pullback quadratic. -/
noncomputable def largeScalePreimage (scale : ℝ) : ℝ :=
  (scale + Real.sqrt (scale ^ 2 - 4)) / 2

theorem positiveScalePreimage_mul_largeScalePreimage
    {scale : ℝ} (hscale : 2 ≤ scale) :
    positiveScalePreimage scale * largeScalePreimage scale = 1 := by
  have hdisc : 0 ≤ scale ^ 2 - 4 := by nlinarith
  have hsqrtSq : (Real.sqrt (scale ^ 2 - 4)) ^ 2 = scale ^ 2 - 4 :=
    Real.sq_sqrt hdisc
  rw [positiveScalePreimage, largeScalePreimage]
  nlinarith

/-- One of the two complex pullback roots when the absolute scale is below
two.  The other root is its conjugate. -/
noncomputable def unitCircleScalePreimage (scale : ℝ) : ℂ :=
  (scale / 2 : ℝ) +
    (Real.sqrt (4 - scale ^ 2) / 2 : ℝ) * Complex.I

theorem unitCircleScalePreimage_re (scale : ℝ) :
    (unitCircleScalePreimage scale).re = scale / 2 := by
  simp [unitCircleScalePreimage]

theorem unitCircleScalePreimage_im (scale : ℝ) :
    (unitCircleScalePreimage scale).im =
      Real.sqrt (4 - scale ^ 2) / 2 := by
  simp [unitCircleScalePreimage]

theorem unitCircleScalePreimage_norm
    {scale : ℝ} (hscale : |scale| ≤ 2) :
    ‖unitCircleScalePreimage scale‖ = 1 := by
  have hdisc : 0 ≤ 4 - scale ^ 2 := by
    have habsSq : |scale| ^ 2 ≤ (2 : ℝ) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg scale) (by norm_num)).2 hscale
    norm_num [sq_abs] at habsSq
    linarith
  have hsqrtSq : (Real.sqrt (4 - scale ^ 2)) ^ 2 = 4 - scale ^ 2 :=
    Real.sq_sqrt hdisc
  rw [Complex.norm_def, Complex.normSq_apply,
    unitCircleScalePreimage_re, unitCircleScalePreimage_im]
  have hinside :
      scale / 2 * (scale / 2) +
          (Real.sqrt (4 - scale ^ 2) / 2) *
            (Real.sqrt (4 - scale ^ 2) / 2) = 1 := by
    nlinarith
  rw [hinside, Real.sqrt_one]

theorem unitCircleScalePreimage_quadratic
    {scale : ℝ} (hscale : |scale| ≤ 2) :
    unitCircleScalePreimage scale ^ 2 -
        (scale : ℂ) * unitCircleScalePreimage scale + 1 = 0 := by
  have hdisc : 0 ≤ 4 - scale ^ 2 := by
    have habsSq : |scale| ^ 2 ≤ (2 : ℝ) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg scale) (by norm_num)).2 hscale
    norm_num [sq_abs] at habsSq
    linarith
  have hsqrtSq : (Real.sqrt (4 - scale ^ 2)) ^ 2 = 4 - scale ^ 2 :=
    Real.sq_sqrt hdisc
  have hsqrtSqMul :
      Real.sqrt (4 - scale * scale) ^ 2 = 4 - scale * scale := by
    simpa [pow_two] using hsqrtSq
  apply Complex.ext
  · simp [unitCircleScalePreimage, pow_two]
    nlinarith [hsqrtSqMul]
  · simp [unitCircleScalePreimage, pow_two]
    ring

theorem positiveScalePreimage_strictAnti
    {small large : ℝ} (hsmall : 2 ≤ small) (hlt : small < large) :
    positiveScalePreimage large < positiveScalePreimage small := by
  have hlarge : 2 ≤ large := hsmall.trans hlt.le
  rw [positiveScalePreimage_eq_two_div hsmall,
    positiveScalePreimage_eq_two_div hlarge]
  have hsmallNonneg : 0 ≤ small := by linarith
  have hsq : small ^ 2 < large ^ 2 := by nlinarith
  have hsqrt : Real.sqrt (small ^ 2 - 4) <
      Real.sqrt (large ^ 2 - 4) := by
    exact Real.sqrt_lt_sqrt (by nlinarith)
      (sub_lt_sub_right hsq 4)
  have hdenom :
      small + Real.sqrt (small ^ 2 - 4) <
        large + Real.sqrt (large ^ 2 - 4) := by linarith
  have hsmallDenomPos :
      0 < small + Real.sqrt (small ^ 2 - 4) := by positivity
  have hlargeDenomPos :
      0 < large + Real.sqrt (large ^ 2 - 4) := by positivity
  have hreciprocal := one_div_lt_one_div_of_lt hsmallDenomPos hdenom
  have hmul := mul_lt_mul_of_pos_left hreciprocal
    (show (0 : ℝ) < 2 by norm_num)
  simpa [div_eq_mul_inv] using hmul

theorem positiveScalePreimage_natCast
    (alphabetSize : ℕ) :
    positiveScalePreimage (alphabetSize : ℝ) =
      fixedRankPreimage alphabetSize := by
  rfl

theorem besselScalePreimageRadius_natCast
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    besselScalePreimageRadius (alphabetSize : ℝ) =
      fixedRankPreimage alphabetSize := by
  rw [besselScalePreimageRadius, if_pos]
  · exact positiveScalePreimage_natCast alphabetSize
  · exact_mod_cast (show 2 ≤ alphabetSize by omega)

theorem fixedRankPreimage_lt_one
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    fixedRankPreimage alphabetSize < 1 := by
  rw [← positiveScalePreimage_natCast alphabetSize,
    positiveScalePreimage_eq_two_div (by exact_mod_cast (show 2 ≤ alphabetSize by omega))]
  have hn : (3 : ℝ) ≤ alphabetSize := by exact_mod_cast hsize
  have hsqrtPos : 0 <
      Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4) :=
    fixedRank_sqrt_pos alphabetSize hsize
  have hdenomPos :
      0 < (alphabetSize : ℝ) +
        Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4) := by positivity
  apply (div_lt_one hdenomPos).2
  linarith

/-- Every strictly smaller scale of absolute value at least two has a strictly
larger closest preimage radius than the leading scale. -/
theorem lowerBesselScale_preimageRadius_gt
    (alphabetSize : ℕ)
    {scale : ℝ} (hscale : 2 ≤ scale)
    (hlower : scale < alphabetSize) :
    fixedRankPreimage alphabetSize < besselScalePreimageRadius scale := by
  rw [besselScalePreimageRadius, if_pos hscale,
    ← positiveScalePreimage_natCast alphabetSize]
  exact positiveScalePreimage_strictAnti hscale hlower

/-- Scales of absolute value below two have closest preimages on the unit
circle, hence also lie strictly outside the leading fixed-rank radius. -/
theorem smallBesselScale_preimageRadius_gt
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize)
    {scale : ℝ} (hscale : scale < 2) :
    fixedRankPreimage alphabetSize < besselScalePreimageRadius scale := by
  rw [besselScalePreimageRadius, if_neg (not_le.mpr hscale)]
  exact fixedRankPreimage_lt_one alphabetSize hsize

/-- Uniform scale-separation statement in the precise piecewise radius used by
the manuscript argument. -/
theorem lowerBesselScale_all_preimageRadius_gt
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize)
    {scale : ℝ}
    (hlower : scale < alphabetSize) :
    fixedRankPreimage alphabetSize < besselScalePreimageRadius scale := by
  by_cases htwo : 2 ≤ scale
  · exact lowerBesselScale_preimageRadius_gt alphabetSize htwo hlower
  · exact smallBesselScale_preimageRadius_gt alphabetSize hsize
      (lt_of_not_ge htwo)

/-- Exact factorization of the pulled-back leading singular factor.  This is
the algebraic identity behind the local power--logarithm transfer. -/
theorem one_sub_size_mul_ribbonSubstitutionReal
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) (z : ℝ) :
    1 - (alphabetSize : ℝ) * ribbonSubstitutionReal z =
      ((1 - fixedRankGrowth alphabetSize * z) *
        (1 - fixedRankPreimage alphabetSize * z)) /
          (1 + z ^ 2) := by
  have hsum := fixedRankGrowth_add_preimage alphabetSize
  have hmul := fixedRankGrowth_mul_preimage alphabetSize hsize
  have hdenom : 1 + z ^ 2 ≠ 0 := by positivity
  rw [ribbonSubstitutionReal]
  field_simp
  rw [← hsum]
  linear_combination -z ^ 2 * hmul

theorem ribbonSubstitutionReal_neg_fixedRankPreimage
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    ribbonSubstitutionReal (-fixedRankPreimage alphabetSize) =
      -(1 / alphabetSize) := by
  rw [ribbonSubstitutionReal]
  have hpositive := ribbonSubstitutionReal_fixedRankPreimage alphabetSize hsize
  rw [ribbonSubstitutionReal] at hpositive
  change (-fixedRankPreimage alphabetSize) /
      (1 + (-fixedRankPreimage alphabetSize) ^ 2) =
        -(1 / (alphabetSize : ℝ))
  rw [neg_sq, neg_div]
  exact congrArg Neg.neg hpositive

theorem ribbonPrefactorReal_neg_fixedRankPreimage
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    ribbonPrefactorReal (-fixedRankPreimage alphabetSize) =
      fixedRankGrowth alphabetSize / alphabetSize := by
  simpa [ribbonPrefactorReal] using
    ribbonPrefactorReal_fixedRankPreimage alphabetSize hsize

theorem ribbonSubstitutionDerivativeReal_neg_fixedRankPreimage
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    (-fixedRankPreimage alphabetSize) *
          ribbonSubstitutionDerivativeReal (-fixedRankPreimage alphabetSize) /
        (-(1 / alphabetSize)) =
      Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4) / alphabetSize := by
  simpa [ribbonSubstitutionDerivativeReal] using
    ribbonSubstitutionDerivativeReal_fixedRankPreimage alphabetSize hsize

end FibonacciRibbonKernel
