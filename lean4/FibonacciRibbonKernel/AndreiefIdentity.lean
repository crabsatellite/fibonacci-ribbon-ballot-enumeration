import FibonacciRibbonKernel.AndreiefCommonIntegral

namespace FibonacciRibbonKernel

open MeasureTheory
open scoped BigOperators

noncomputable def andreiefCoordinatePermEquiv
    {dimension : ℕ} (permutation : Equiv.Perm (Fin dimension)) :
    (Fin dimension → ℝ) ≃ᵐ (Fin dimension → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin dimension => ℝ)
    permutation).symm

theorem andreiefCoordinatePermEquiv_apply
    {dimension : ℕ} (permutation : Equiv.Perm (Fin dimension))
    (angles : Fin dimension → ℝ) (index : Fin dimension) :
    andreiefCoordinatePermEquiv permutation angles index =
      angles (permutation index) := by
  rfl

theorem measurePreserving_andreiefCoordinatePermEquiv
    {dimension : ℕ} (permutation : Equiv.Perm (Fin dimension)) :
    MeasurePreserving (andreiefCoordinatePermEquiv permutation)
      (cosineCubeProductMeasure dimension)
      (cosineCubeProductMeasure dimension) := by
  unfold andreiefCoordinatePermEquiv cosineCubeProductMeasure
  exact (measurePreserving_piCongrLeft
    (fun _ : Fin dimension => cosineIntervalMeasure) permutation).symm

theorem andreiefPermutationProduct_coordinatePerm_symm
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (permutation : Equiv.Perm (Fin dimension))
    (angles : Fin dimension → ℝ) :
    andreiefPermutationProduct basis permutation
        (andreiefCoordinatePermEquiv permutation.symm angles) =
      andreiefDiagonalProduct basis angles := by
  unfold andreiefPermutationProduct andreiefDiagonalProduct
  apply Finset.prod_congr rfl
  intro index _hindex
  rw [andreiefCoordinatePermEquiv_apply, Equiv.symm_apply_apply]

theorem andreiefEvaluationMatrix_coordinatePerm
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (permutation : Equiv.Perm (Fin dimension))
    (angles : Fin dimension → ℝ) :
    andreiefEvaluationMatrix basis
        (andreiefCoordinatePermEquiv permutation angles) =
      (andreiefEvaluationMatrix basis angles).submatrix permutation id := by
  ext row column
  unfold andreiefEvaluationMatrix
  rw [andreiefCoordinatePermEquiv_apply]
  rfl

theorem andreiefEvaluationDet_coordinatePerm
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (permutation : Equiv.Perm (Fin dimension))
    (angles : Fin dimension → ℝ) :
    (andreiefEvaluationMatrix basis
        (andreiefCoordinatePermEquiv permutation angles)).det =
      ((permutation.sign : ℤ) : ℝ) *
        (andreiefEvaluationMatrix basis angles).det := by
  rw [andreiefEvaluationMatrix_coordinatePerm,
    Matrix.det_permute]

noncomputable def andreiefLeibnizTerm
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (permutation : Equiv.Perm (Fin dimension))
    (angles : Fin dimension → ℝ) : ℝ :=
  ((permutation.sign : ℤ) : ℝ) *
    andreiefPermutationProduct basis permutation angles *
      (andreiefEvaluationMatrix basis angles).det

theorem continuous_andreiefPermutationProduct
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (hbasis : ∀ index, Continuous (basis index))
    (permutation : Equiv.Perm (Fin dimension)) :
    Continuous (andreiefPermutationProduct basis permutation) := by
  unfold andreiefPermutationProduct
  apply continuous_finsetProd
  intro index _hindex
  exact (hbasis index).comp (continuous_apply (permutation index))

theorem andreiefEvaluationDet_expansion
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (angles : Fin dimension → ℝ) :
    (andreiefEvaluationMatrix basis angles).det =
      ∑ permutation : Equiv.Perm (Fin dimension),
        ((permutation.sign : ℤ) : ℝ) *
          andreiefPermutationProduct basis permutation angles := by
  rw [Matrix.det_apply']
  rfl

theorem continuous_andreiefEvaluationDet
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (hbasis : ∀ index, Continuous (basis index)) :
    Continuous (fun angles => (andreiefEvaluationMatrix basis angles).det) := by
  rw [show (fun angles : Fin dimension → ℝ =>
      (andreiefEvaluationMatrix basis angles).det) =
      fun angles => ∑ permutation : Equiv.Perm (Fin dimension),
        ((permutation.sign : ℤ) : ℝ) *
          andreiefPermutationProduct basis permutation angles by
    funext angles
    exact andreiefEvaluationDet_expansion basis angles]
  apply continuous_finsetSum
  intro permutation _hpermutation
  exact continuous_const.mul
    (continuous_andreiefPermutationProduct basis hbasis permutation)

theorem integrable_andreiefLeibnizTerm
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (hbasis : ∀ index, Continuous (basis index))
    (permutation : Equiv.Perm (Fin dimension)) :
    Integrable (andreiefLeibnizTerm basis permutation)
      (cosineCubeProductMeasure dimension) := by
  apply integrable_continuous_cosineCube
  unfold andreiefLeibnizTerm
  exact (continuous_const.mul
    (continuous_andreiefPermutationProduct basis hbasis permutation)).mul
      (continuous_andreiefEvaluationDet basis hbasis)

theorem andreief_sign_sq
    {dimension : ℕ} (permutation : Equiv.Perm (Fin dimension)) :
    (((permutation.sign : ℤ) : ℝ)) ^ 2 = 1 := by
  have hsignAbs : |((permutation.sign : ℤ) : ℝ)| = 1 := by
    exact_mod_cast Equiv.Perm.sign_abs permutation
  rw [← sq_abs, hsignAbs]
  norm_num

theorem andreiefLeibnizTerm_coordinatePerm_symm
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (permutation : Equiv.Perm (Fin dimension))
    (angles : Fin dimension → ℝ) :
    andreiefLeibnizTerm basis permutation
        (andreiefCoordinatePermEquiv permutation.symm angles) =
      andreiefDiagonalProduct basis angles *
        (andreiefEvaluationMatrix basis angles).det := by
  unfold andreiefLeibnizTerm
  rw [andreiefPermutationProduct_coordinatePerm_symm,
    andreiefEvaluationDet_coordinatePerm,
    Equiv.Perm.sign_symm]
  have hsign := andreief_sign_sq permutation
  calc
    ((permutation.sign : ℤ) : ℝ) *
          andreiefDiagonalProduct basis angles *
        (((permutation.sign : ℤ) : ℝ) *
          (andreiefEvaluationMatrix basis angles).det) =
      (((permutation.sign : ℤ) : ℝ) ^ 2) *
        (andreiefDiagonalProduct basis angles *
          (andreiefEvaluationMatrix basis angles).det) := by ring
    _ = _ := by rw [hsign, one_mul]

theorem integral_andreiefLeibnizTerm
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (permutation : Equiv.Perm (Fin dimension)) :
    (∫ angles : Fin dimension → ℝ,
      andreiefLeibnizTerm basis permutation angles
      ∂cosineCubeProductMeasure dimension) =
      ∫ angles : Fin dimension → ℝ,
        andreiefDiagonalProduct basis angles *
          (andreiefEvaluationMatrix basis angles).det
        ∂cosineCubeProductMeasure dimension := by
  rw [← (measurePreserving_andreiefCoordinatePermEquiv
    permutation.symm).integral_comp'
      (andreiefLeibnizTerm basis permutation)]
  apply integral_congr_ae
  filter_upwards with angles
  exact andreiefLeibnizTerm_coordinatePerm_symm basis permutation angles

theorem andreief_det_sq_eq_sum
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (angles : Fin dimension → ℝ) :
    (andreiefEvaluationMatrix basis angles).det ^ 2 =
      ∑ permutation : Equiv.Perm (Fin dimension),
        andreiefLeibnizTerm basis permutation angles := by
  rw [pow_two]
  nth_rewrite 1 [andreiefEvaluationDet_expansion]
  rw [Finset.sum_mul]
  unfold andreiefLeibnizTerm
  rfl

theorem andreief_identity
    {dimension : ℕ} (basis : Fin dimension → ℝ → ℝ)
    (hbasis : ∀ index, Continuous (basis index)) :
    (∫ angles : Fin dimension → ℝ,
      (andreiefEvaluationMatrix basis angles).det ^ 2
      ∂cosineCubeProductMeasure dimension) =
      (dimension.factorial : ℝ) * (andreiefMomentMatrix basis).det := by
  rw [show (fun angles : Fin dimension → ℝ =>
      (andreiefEvaluationMatrix basis angles).det ^ 2) =
      fun angles => ∑ permutation : Equiv.Perm (Fin dimension),
        andreiefLeibnizTerm basis permutation angles by
    funext angles
    exact andreief_det_sq_eq_sum basis angles]
  rw [integral_finsetSum]
  · simp_rw [integral_andreiefLeibnizTerm basis]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
      nsmul_eq_mul]
    rw [integral_andreiefDiagonal_mul_det basis hbasis]
    norm_num
  · intro permutation _hpermutation
    exact integrable_andreiefLeibnizTerm basis hbasis permutation

end FibonacciRibbonKernel
