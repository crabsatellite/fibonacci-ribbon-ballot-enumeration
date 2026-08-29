import FibonacciRibbonKernel.OddWeylNormalization

namespace FibonacciRibbonKernel

open MeasureTheory
open scoped BigOperators

noncomputable def andreiefWeightedBasis
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (factor : ℝ → ℝ) (index : Fin dimension) (value : ℝ) : ℝ :=
  basis index value * factor value

noncomputable def andreiefWeightProduct
    {dimension : ℕ} (factor : ℝ → ℝ)
    (angles : Fin dimension → ℝ) : ℝ :=
  ∏ index, factor (angles index) ^ 2

theorem andreiefWeightedEvaluationMatrix_factorization
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (factor : ℝ → ℝ) (angles : Fin dimension → ℝ) :
    andreiefEvaluationMatrix (andreiefWeightedBasis basis factor) angles =
      Matrix.diagonal (fun index => factor (angles index)) *
        andreiefEvaluationMatrix basis angles := by
  ext row column
  rw [Matrix.diagonal_mul]
  unfold andreiefEvaluationMatrix andreiefWeightedBasis
  ring

theorem andreiefWeightedEvaluationDet
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (factor : ℝ → ℝ) (angles : Fin dimension → ℝ) :
    (andreiefEvaluationMatrix
      (andreiefWeightedBasis basis factor) angles).det =
      (∏ index, factor (angles index)) *
        (andreiefEvaluationMatrix basis angles).det := by
  rw [andreiefWeightedEvaluationMatrix_factorization,
    Matrix.det_mul, Matrix.det_diagonal]

theorem andreiefWeightedEvaluationDet_sq
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (factor : ℝ → ℝ) (angles : Fin dimension → ℝ) :
    (andreiefEvaluationMatrix
      (andreiefWeightedBasis basis factor) angles).det ^ 2 =
      andreiefWeightProduct factor angles *
        (andreiefEvaluationMatrix basis angles).det ^ 2 := by
  rw [andreiefWeightedEvaluationDet, mul_pow]
  unfold andreiefWeightProduct
  congr 1
  symm
  simpa using Finset.prod_pow (Finset.univ : Finset (Fin dimension))
    2 (fun index => factor (angles index))

theorem continuous_andreiefWeightedBasis
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (factor : ℝ → ℝ)
    (hbasis : ∀ index, Continuous (basis index))
    (hfactor : Continuous factor)
    (index : Fin dimension) :
    Continuous (andreiefWeightedBasis basis factor index) := by
  unfold andreiefWeightedBasis
  exact (hbasis index).mul hfactor

theorem andreief_weighted_identity
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (factor : ℝ → ℝ)
    (hbasis : ∀ index, Continuous (basis index))
    (hfactor : Continuous factor) :
    (∫ angles : Fin dimension → ℝ,
      andreiefWeightProduct factor angles *
        (andreiefEvaluationMatrix basis angles).det ^ 2
      ∂cosineCubeProductMeasure dimension) =
      (dimension.factorial : ℝ) *
        (andreiefMomentMatrix
          (andreiefWeightedBasis basis factor)).det := by
  have h := andreief_identity
    (andreiefWeightedBasis basis factor)
    (continuous_andreiefWeightedBasis basis factor hbasis hfactor)
  rw [show (fun angles : Fin dimension → ℝ =>
      (andreiefEvaluationMatrix
        (andreiefWeightedBasis basis factor) angles).det ^ 2) =
      fun angles => andreiefWeightProduct factor angles *
        (andreiefEvaluationMatrix basis angles).det ^ 2 by
    funext angles
    exact andreiefWeightedEvaluationDet_sq basis factor angles] at h
  exact h

end FibonacciRibbonKernel
