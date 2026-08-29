import FibonacciRibbonKernel.RegevQuadraticFullSum
import Mathlib.MeasureTheory.Integral.Pi

namespace FibonacciRibbonKernel

open MeasureTheory
open scoped Classical

theorem abs_regevVandermonde_le_coordinatePairEnvelope
    (rank : ℕ) (coordinates : Fin rank → ℝ) :
    |regevVandermonde rank coordinates| ≤
      regevCoordinatePairEnvelope rank coordinates := by
  unfold regevVandermonde regevCoordinatePairEnvelope
  rw [Finset.abs_prod]
  apply Finset.prod_le_prod
  · intro row hrow
    positivity
  · intro row hrow
    rw [Finset.abs_prod]
    apply Finset.prod_le_prod
    · intro next hnext
      positivity
    · intro next hnext
      calc
        |tracelessExtend coordinates row -
            tracelessExtend coordinates next| ≤
          |tracelessExtend coordinates row| +
            |tracelessExtend coordinates next| := by
          simpa only [Real.norm_eq_abs] using
            norm_sub_le (tracelessExtend coordinates row)
              (tracelessExtend coordinates next)
        _ ≤ |tracelessExtend coordinates row| +
            |tracelessExtend coordinates next| +
            (rank : ℝ) * (rank + 1 : ℕ) := by
          apply le_add_of_nonneg_right
          exact mul_nonneg (show (0 : ℝ) ≤ rank by positivity)
            (show (0 : ℝ) ≤ (rank + 1 : ℕ) by positivity)

theorem one_le_regevCoordinateRowEnvelope
    (rank : ℕ) (coordinates : Fin rank → ℝ) :
    1 ≤ regevCoordinateRowEnvelope rank coordinates := by
  unfold regevCoordinateRowEnvelope
  apply Finset.one_le_prod
  intro row hrow
  have hoffset : (0 : ℝ) ≤ row.rev.val := Nat.cast_nonneg _
  nlinarith [abs_nonneg (tracelessExtend coordinates row)]

theorem regevGaussianKernel_le_coordinateGaussian
    (rank : ℕ) (coordinates : Fin rank → ℝ) :
    regevGaussianKernel rank coordinates ≤
      Real.exp (-(∑ row : Fin (rank + 1),
        tracelessExtend coordinates row ^ 2 /
          (2 * regevEntropyDenominator rank))) := by
  unfold regevGaussianKernel
  apply Real.exp_le_exp.mpr
  have hdenominatorPos : 0 < regevEntropyDenominator rank := by
    unfold regevEntropyDenominator
    positivity
  have hdenominatorOne : 1 ≤ regevEntropyDenominator rank := by
    unfold regevEntropyDenominator
    have hdimension : (0 : ℝ) ≤ (rank + 1 : ℕ) := Nat.cast_nonneg _
    have hstaircase : (0 : ℝ) ≤ (staircaseWeight rank + 1 : ℕ) :=
      Nat.cast_nonneg _
    nlinarith [mul_nonneg hdimension hstaircase]
  have hsum :
      (∑ row : Fin (rank + 1),
        tracelessExtend coordinates row ^ 2 /
          (2 * regevEntropyDenominator rank)) ≤
      ∑ row : Fin (rank + 1),
        tracelessExtend coordinates row ^ 2 / 2 := by
    apply Finset.sum_le_sum
    intro row hrow
    apply div_le_div_of_nonneg_left (sq_nonneg _)
    · norm_num
    · nlinarith
  linarith

theorem one_le_regevEntropyPrefactor (rank : ℕ) :
    1 ≤ Real.exp
      (regevEntropyOffset rank / regevEntropyDenominator rank) := by
  apply Real.one_le_exp
  apply div_nonneg
  · unfold regevEntropyOffset
    positivity
  · unfold regevEntropyDenominator
    positivity

theorem abs_regevLocalIntegrand_le_coordinateDominatingKernel
    (rank : ℕ) (coordinates : Fin rank → ℝ) :
    |regevLocalIntegrand rank coordinates| ≤
      (1 / Real.sqrt (2 * Real.pi)) ^ (rank + 1) *
        regevCoordinateDominatingKernel rank coordinates := by
  let prefactor := (1 / Real.sqrt (2 * Real.pi)) ^ (rank + 1)
  let weakGaussian := Real.exp (-(∑ row : Fin (rank + 1),
    tracelessExtend coordinates row ^ 2 /
      (2 * regevEntropyDenominator rank)))
  have hprefactorNonneg : 0 ≤ prefactor := by
    dsimp only [prefactor]
    positivity
  have hgaussianNonneg : 0 ≤ regevGaussianKernel rank coordinates := by
    unfold regevGaussianKernel
    positivity
  have hpairNonneg : 0 ≤ regevCoordinatePairEnvelope rank coordinates := by
    unfold regevCoordinatePairEnvelope
    positivity
  have hweakNonneg : 0 ≤ weakGaussian := (Real.exp_pos _).le
  have hleadingOne : 1 ≤
      Real.exp (regevEntropyOffset rank / regevEntropyDenominator rank) *
        regevCoordinateRowEnvelope rank coordinates :=
    one_le_mul_of_one_le_of_one_le
      (one_le_regevEntropyPrefactor rank)
      (one_le_regevCoordinateRowEnvelope rank coordinates)
  have hcore :
      regevGaussianKernel rank coordinates *
          |regevVandermonde rank coordinates| ≤
        Real.exp (regevEntropyOffset rank / regevEntropyDenominator rank) *
          regevCoordinateRowEnvelope rank coordinates *
          regevCoordinatePairEnvelope rank coordinates * weakGaussian := by
    calc
      regevGaussianKernel rank coordinates *
          |regevVandermonde rank coordinates| ≤
        weakGaussian * regevCoordinatePairEnvelope rank coordinates :=
      mul_le_mul
        (regevGaussianKernel_le_coordinateGaussian rank coordinates)
        (abs_regevVandermonde_le_coordinatePairEnvelope rank coordinates)
        (abs_nonneg _) hweakNonneg
      _ ≤ (Real.exp (regevEntropyOffset rank /
            regevEntropyDenominator rank) *
          regevCoordinateRowEnvelope rank coordinates) *
          (weakGaussian * regevCoordinatePairEnvelope rank coordinates) := by
        apply le_mul_of_one_le_left
        · exact mul_nonneg hweakNonneg hpairNonneg
        · exact hleadingOne
      _ = _ := by ring
  unfold regevLocalIntegrand regevCoordinateDominatingKernel
  change |prefactor * regevGaussianKernel rank coordinates *
      regevVandermonde rank coordinates| ≤
    prefactor *
      (Real.exp (regevEntropyOffset rank / regevEntropyDenominator rank) *
        regevCoordinateRowEnvelope rank coordinates *
        regevCoordinatePairEnvelope rank coordinates * weakGaussian)
  rw [abs_mul, abs_mul, abs_of_nonneg hprefactorNonneg,
    abs_of_nonneg hgaussianNonneg]
  calc
    prefactor * regevGaussianKernel rank coordinates *
        |regevVandermonde rank coordinates| =
      prefactor * (regevGaussianKernel rank coordinates *
        |regevVandermonde rank coordinates|) := by ring
    _ ≤ prefactor *
        (Real.exp (regevEntropyOffset rank / regevEntropyDenominator rank) *
          regevCoordinateRowEnvelope rank coordinates *
          regevCoordinatePairEnvelope rank coordinates * weakGaussian) :=
      mul_le_mul_of_nonneg_left hcore hprefactorNonneg

theorem integrable_regevCoordinateSeparableGaussian (rank : ℕ) :
    Integrable (regevCoordinateSeparableGaussian rank) := by
  unfold regevCoordinateSeparableGaussian
  have hcoefficient : 0 < regevCoordinateGaussianCoefficient rank / 2 := by
    positivity [regevCoordinateGaussianCoefficient_pos rank]
  rw [volume_pi]
  exact Integrable.fintype_prod
    (μ := fun _ : Fin rank => (volume : Measure ℝ))
    (f := fun _ : Fin rank => fun value : ℝ =>
      Real.exp (-(regevCoordinateGaussianCoefficient rank / 2) * value ^ 2))
    (fun _ => integrable_exp_neg_mul_sq hcoefficient)

/-- The limiting Regev local integrand is genuinely Bochner integrable on the
full traceless chart. -/
theorem integrable_regevLocalIntegrand (rank : ℕ) :
    Integrable (regevLocalIntegrand rank) := by
  let constant := (1 / Real.sqrt (2 * Real.pi)) ^ (rank + 1) *
    regevCoordinateAbsorptionConstant rank
  have hmajorant : Integrable (fun coordinates : Fin rank → ℝ =>
      constant * regevCoordinateSeparableGaussian rank coordinates) :=
    (integrable_regevCoordinateSeparableGaussian rank).const_mul constant
  apply Integrable.mono' hmajorant
  · exact (continuous_regevLocalIntegrand rank).aestronglyMeasurable
  · filter_upwards with coordinates
    rw [Real.norm_eq_abs]
    calc
      |regevLocalIntegrand rank coordinates| ≤
          (1 / Real.sqrt (2 * Real.pi)) ^ (rank + 1) *
            regevCoordinateDominatingKernel rank coordinates :=
        abs_regevLocalIntegrand_le_coordinateDominatingKernel rank coordinates
      _ ≤ (1 / Real.sqrt (2 * Real.pi)) ^ (rank + 1) *
          (regevCoordinateAbsorptionConstant rank *
            regevCoordinateSeparableGaussian rank coordinates) := by
        exact mul_le_mul_of_nonneg_left
          (regevCoordinateDominatingKernel_le_separableGaussian rank coordinates)
          (by positivity)
      _ = constant * regevCoordinateSeparableGaussian rank coordinates := by
        dsimp only [constant]
        ring

end FibonacciRibbonKernel
