import FibonacciRibbonKernel.OddWeylDeterminant

namespace FibonacciRibbonKernel

open MeasureTheory
open scoped BigOperators

noncomputable def andreiefEvaluationMatrix
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (angles : Fin dimension → ℝ) : Matrix (Fin dimension) (Fin dimension) ℝ :=
  fun row column => basis column (angles row)

noncomputable def andreiefMomentMatrix
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ) :
    Matrix (Fin dimension) (Fin dimension) ℝ :=
  fun row column => ∫ angle : ℝ,
    basis row angle * basis column angle ∂cosineIntervalMeasure

noncomputable def andreiefDiagonalProduct
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (angles : Fin dimension → ℝ) : ℝ :=
  ∏ index, basis index (angles index)

noncomputable def andreiefPermutationProduct
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (permutation : Equiv.Perm (Fin dimension))
    (angles : Fin dimension → ℝ) : ℝ :=
  ∏ index, basis index (angles (permutation index))

noncomputable def andreiefCoordinateProduct
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (permutation : Equiv.Perm (Fin dimension))
    (angles : Fin dimension → ℝ) : ℝ :=
  ∏ index,
    basis index (angles index) * basis (permutation.symm index) (angles index)

theorem andreiefDiagonal_mul_permutation_eq_coordinate
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (permutation : Equiv.Perm (Fin dimension))
    (angles : Fin dimension → ℝ) :
    andreiefDiagonalProduct basis angles *
        andreiefPermutationProduct basis permutation angles =
      andreiefCoordinateProduct basis permutation angles := by
  unfold andreiefDiagonalProduct andreiefPermutationProduct
    andreiefCoordinateProduct
  rw [← Equiv.prod_comp permutation.symm
    (fun index => basis index (angles (permutation index)))]
  simp only [Equiv.apply_symm_apply]
  rw [Finset.prod_mul_distrib]

theorem continuous_andreiefCoordinateProduct
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (hbasis : ∀ index, Continuous (basis index))
    (permutation : Equiv.Perm (Fin dimension)) :
    Continuous (andreiefCoordinateProduct basis permutation) := by
  unfold andreiefCoordinateProduct
  apply continuous_finsetProd
  intro index _hindex
  exact ((hbasis index).comp (continuous_apply index)).mul
    ((hbasis (permutation.symm index)).comp (continuous_apply index))

theorem integrable_andreiefCoordinateProduct
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (hbasis : ∀ index, Continuous (basis index))
    (permutation : Equiv.Perm (Fin dimension)) :
    Integrable (andreiefCoordinateProduct basis permutation)
      (cosineCubeProductMeasure dimension) :=
  integrable_continuous_cosineCube
    (continuous_andreiefCoordinateProduct basis hbasis permutation)

theorem integral_andreiefCoordinateProduct
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (permutation : Equiv.Perm (Fin dimension)) :
    (∫ angles : Fin dimension → ℝ,
      andreiefCoordinateProduct basis permutation angles
      ∂cosineCubeProductMeasure dimension) =
      ∏ index,
        andreiefMomentMatrix basis index (permutation.symm index) := by
  unfold andreiefCoordinateProduct andreiefMomentMatrix
    cosineCubeProductMeasure
  rw [MeasureTheory.integral_fintype_prod_eq_prod
    (fun index angle =>
      basis index angle * basis (permutation.symm index) angle)]

theorem andreiefDiagonal_mul_det_eq_sum
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (angles : Fin dimension → ℝ) :
    andreiefDiagonalProduct basis angles *
        (andreiefEvaluationMatrix basis angles).det =
      ∑ permutation : Equiv.Perm (Fin dimension),
        ((permutation.sign : ℤ) : ℝ) *
          andreiefCoordinateProduct basis permutation angles := by
  rw [Matrix.det_apply', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro permutation _hpermutation
  unfold andreiefEvaluationMatrix
  change andreiefDiagonalProduct basis angles *
      (((permutation.sign : ℤ) : ℝ) *
        andreiefPermutationProduct basis permutation angles) =
    ((permutation.sign : ℤ) : ℝ) *
      andreiefCoordinateProduct basis permutation angles
  calc
    andreiefDiagonalProduct basis angles *
        (((permutation.sign : ℤ) : ℝ) *
          andreiefPermutationProduct basis permutation angles) =
      ((permutation.sign : ℤ) : ℝ) *
        (andreiefDiagonalProduct basis angles *
          andreiefPermutationProduct basis permutation angles) := by ring
    _ = _ := by rw [andreiefDiagonal_mul_permutation_eq_coordinate]

theorem andreiefMoment_det_expansion
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ) :
    (andreiefMomentMatrix basis).det =
      ∑ permutation : Equiv.Perm (Fin dimension),
        ((permutation.sign : ℤ) : ℝ) *
          ∏ index,
            andreiefMomentMatrix basis index (permutation.symm index) := by
  rw [Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro permutation _hpermutation
  congr 1
  rw [← Equiv.prod_comp permutation.symm]
  simp only [Equiv.apply_symm_apply]

theorem integral_andreiefDiagonal_mul_det
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (hbasis : ∀ index, Continuous (basis index)) :
    (∫ angles : Fin dimension → ℝ,
      andreiefDiagonalProduct basis angles *
        (andreiefEvaluationMatrix basis angles).det
      ∂cosineCubeProductMeasure dimension) =
      (andreiefMomentMatrix basis).det := by
  rw [show (fun angles : Fin dimension → ℝ =>
      andreiefDiagonalProduct basis angles *
        (andreiefEvaluationMatrix basis angles).det) =
      fun angles =>
        ∑ permutation : Equiv.Perm (Fin dimension),
          ((permutation.sign : ℤ) : ℝ) *
            andreiefCoordinateProduct basis permutation angles by
    funext angles
    exact andreiefDiagonal_mul_det_eq_sum basis angles]
  rw [integral_finsetSum]
  · rw [andreiefMoment_det_expansion]
    apply Finset.sum_congr rfl
    intro permutation _hpermutation
    rw [integral_const_mul,
      integral_andreiefCoordinateProduct basis permutation]
  · intro permutation _hpermutation
    exact (integrable_andreiefCoordinateProduct
      basis hbasis permutation).const_mul _

end FibonacciRibbonKernel
