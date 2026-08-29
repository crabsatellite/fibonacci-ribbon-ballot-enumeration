import FibonacciRibbonKernel.AndreiefWeightedIdentity

namespace FibonacciRibbonKernel

open MeasureTheory
open scoped BigOperators

noncomputable def oddAndreiefExponentialFactor
    (dimension : ℕ) (parameter angle : ℝ) : ℝ :=
  Real.exp (parameter *
    (1 / (2 * dimension : ℝ) + Real.cos angle))

noncomputable def oddWeylExponentialIntegral
    (dimension : ℕ) (parameter : ℝ) : ℝ :=
  ∫ angles : Fin dimension → ℝ,
    Real.exp (parameter * oddCosineCubeScale angles) *
      oddWeylAngleWeight dimension angles
    ∂cosineCubeProductMeasure dimension

theorem continuous_oddAndreiefExponentialFactor
    (dimension : ℕ) (parameter : ℝ) :
    Continuous (oddAndreiefExponentialFactor dimension parameter) := by
  unfold oddAndreiefExponentialFactor
  fun_prop

theorem andreiefWeightProduct_oddExponential
    {dimension : ℕ} (hdimension : 1 ≤ dimension)
    (parameter : ℝ) (angles : Fin dimension → ℝ) :
    andreiefWeightProduct
        (oddAndreiefExponentialFactor dimension parameter) angles =
      Real.exp (parameter * oddCosineCubeScale angles) := by
  unfold andreiefWeightProduct oddAndreiefExponentialFactor
  have hterm : ∀ index : Fin dimension,
      Real.exp
          (parameter * (1 / (2 * (dimension : ℝ)) +
            Real.cos (angles index))) ^ 2 =
        Real.exp
          (2 * parameter * (1 / (2 * (dimension : ℝ)) +
            Real.cos (angles index))) := by
    intro index
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simp_rw [hterm]
  rw [← Real.exp_sum]
  congr 1
  unfold oddCosineCubeScale cosineCubeScale
  have hdimensionNe : (dimension : ℝ) ≠ 0 := by positivity
  have hconstant :
      (∑ _index : Fin dimension,
        2 * parameter * (1 / (2 * (dimension : ℝ)))) = parameter := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  rw [show (fun index : Fin dimension =>
      2 * parameter * (1 / (2 * (dimension : ℝ)) +
        Real.cos (angles index))) =
      fun index =>
        2 * parameter * (1 / (2 * (dimension : ℝ))) +
          2 * parameter * Real.cos (angles index) by
    funext index
    ring]
  rw [Finset.sum_add_distrib, hconstant, ← Finset.mul_sum]
  ring

theorem oddWeylExponentialIntegral_andreief
    {dimension : ℕ} (hdimension : 1 ≤ dimension)
    (parameter : ℝ) :
    (2 : ℝ) ^ (dimension * (dimension + 1)) *
        oddWeylExponentialIntegral dimension parameter =
      (dimension.factorial : ℝ) *
        (andreiefMomentMatrix
          (andreiefWeightedBasis
            (oddAndreiefBasis (dimension := dimension))
            (oddAndreiefExponentialFactor dimension parameter))).det := by
  have handreief := andreief_weighted_identity
    (oddAndreiefBasis (dimension := dimension))
    (oddAndreiefExponentialFactor dimension parameter)
    (fun index => continuous_oddAndreiefBasis index)
    (continuous_oddAndreiefExponentialFactor dimension parameter)
  rw [show (fun angles : Fin dimension → ℝ =>
      andreiefWeightProduct
          (oddAndreiefExponentialFactor dimension parameter) angles *
        (andreiefEvaluationMatrix oddAndreiefBasis angles).det ^ 2) =
      fun angles =>
        (2 : ℝ) ^ (dimension * (dimension + 1)) *
          (Real.exp (parameter * oddCosineCubeScale angles) *
            oddWeylAngleWeight dimension angles) by
    funext angles
    rw [andreiefWeightProduct_oddExponential hdimension,
      andreiefEvaluationMatrix_oddBasis,
      det_oddTrigEvaluationMatrix_sq,
      oddWeylAngleWeightIoi_eq]
    ring] at handreief
  unfold oddWeylExponentialIntegral
  rw [integral_const_mul] at handreief
  exact handreief

end FibonacciRibbonKernel
