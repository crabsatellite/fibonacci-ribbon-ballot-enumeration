import FibonacciRibbonKernel.RegevMehtaCenterGeometry
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped Classical

noncomputable def centeredMehtaChamberIntegral (rank : ℕ) : ℝ :=
  ∫ input in (regevChamber rank) ×ˢ (Set.univ : Set ℝ),
    standardMehtaIntegrand (rank + 1)
      (mehtaCenterTransform rank input)
    ∂((volume : Measure (Fin rank → ℝ)).prod volume)

theorem centerGaussianIntegral (rank : ℕ) :
    (∫ center : ℝ,
      Real.exp (-((rank + 1 : ℕ) : ℝ) * center ^ 2 / 2)) =
      Real.sqrt (2 * Real.pi / ((rank + 1 : ℕ) : ℝ)) := by
  rw [show (fun center : ℝ =>
      Real.exp (-((rank + 1 : ℕ) : ℝ) * center ^ 2 / 2)) =
    fun center : ℝ =>
      Real.exp (-(((rank + 1 : ℕ) : ℝ) / 2) * center ^ 2) by
    funext center
    congr 1
    ring]
  rw [integral_gaussian]
  congr 1
  have hdimension : (((rank + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp

theorem centeredMehtaChamberIntegral_eq (rank : ℕ) :
    centeredMehtaChamberIntegral rank =
      Real.sqrt (2 * Real.pi / ((rank + 1 : ℕ) : ℝ)) *
        tracelessMehtaChamberIntegral rank := by
  unfold centeredMehtaChamberIntegral
  have hdomain : MeasurableSet
      ((regevChamber rank) ×ˢ (Set.univ : Set ℝ)) :=
    (regevChamber_isClosed rank).measurableSet.prod MeasurableSet.univ
  rw [show (∫ input in (regevChamber rank) ×ˢ (Set.univ : Set ℝ),
      standardMehtaIntegrand (rank + 1)
        (mehtaCenterTransform rank input)
      ∂((volume : Measure (Fin rank → ℝ)).prod volume)) =
    ∫ input in (regevChamber rank) ×ˢ (Set.univ : Set ℝ),
      (regevGaussianKernel rank input.1 *
        regevVandermonde rank input.1) *
        Real.exp (-((rank + 1 : ℕ) : ℝ) * input.2 ^ 2 / 2)
      ∂((volume : Measure (Fin rank → ℝ)).prod volume) by
    apply setIntegral_congr_fun hdomain
    intro input hinput
    have hchamber : input.1 ∈ regevChamber rank := hinput.1
    change standardMehtaIntegrand (rank + 1)
        (mehtaCenterTransform rank input) = _
    rw [standardMehtaIntegrand_center rank input hchamber]
    ring]
  rw [setIntegral_prod_mul
    (μ := (volume : Measure (Fin rank → ℝ)))
    (ν := (volume : Measure ℝ))
    (fun coordinates => regevGaussianKernel rank coordinates *
      regevVandermonde rank coordinates)
    (fun center => Real.exp
      (-((rank + 1 : ℕ) : ℝ) * center ^ 2 / 2))
    (regevChamber rank) Set.univ]
  rw [setIntegral_univ, centerGaussianIntegral]
  unfold tracelessMehtaChamberIntegral
  ring

end FibonacciRibbonKernel
