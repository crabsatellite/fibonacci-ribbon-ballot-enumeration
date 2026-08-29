import FibonacciRibbonKernel.RegevNormalization

namespace FibonacciRibbonKernel

open scoped Classical

noncomputable def regevCenteredRow
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (row : Fin (rank + 1)) : ℝ :=
  (((shape.1 row).val : ℝ) - (size : ℝ) / (rank + 1 : ℝ)) *
    Real.sqrt ((rank + 1 : ℝ) / (size : ℝ))

theorem BoundedPartition.rows_antitone
    {rank size : ℕ} (shape : BoundedPartition rank size) :
    Antitone (fun row : Fin (rank + 1) => (shape.1 row).val) := by
  rw [Fin.antitone_iff_succ_le]
  exact fun row => Fin.mk_le_mk.mp (shape.2.1 row)

theorem regevCenteredRow_sum_zero
    {rank size : ℕ} (shape : BoundedPartition rank size) :
    (∑ row : Fin (rank + 1), regevCenteredRow shape row) = 0 := by
  unfold regevCenteredRow
  rw [← Finset.sum_mul]
  have hrows :
      (∑ row : Fin (rank + 1), ((shape.1 row).val : ℝ)) = size := by
    exact_mod_cast shape.2.2
  rw [Finset.sum_sub_distrib, hrows]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hdimension : (rank + 1 : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem regevCenteredRow_antitone
    {rank size : ℕ} (shape : BoundedPartition rank size) :
    Antitone (regevCenteredRow shape) := by
  intro row next hrow
  unfold regevCenteredRow
  apply mul_le_mul_of_nonneg_right
  · have hrows : ((shape.1 next).val : ℝ) ≤
        ((shape.1 row).val : ℝ) := by
      exact_mod_cast shape.rows_antitone hrow
    exact sub_le_sub_right hrows _
  · positivity

theorem regevCenteredRow_reconstruct
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) (row : Fin (rank + 1)) :
    ((shape.1 row).val : ℝ) =
      (size : ℝ) / (rank + 1 : ℝ) +
        regevCenteredRow shape row *
          Real.sqrt ((size : ℝ) / (rank + 1 : ℝ)) := by
  have hdimensionPos : (0 : ℝ) < rank + 1 := by positivity
  have hsizePos : (0 : ℝ) < size := by positivity
  have hfirstNonneg :
      0 ≤ (rank + 1 : ℝ) / (size : ℝ) := by positivity
  have hsecondNonneg :
      0 ≤ (size : ℝ) / (rank + 1 : ℝ) := by positivity
  have hmul :
      Real.sqrt ((rank + 1 : ℝ) / (size : ℝ)) *
          Real.sqrt ((size : ℝ) / (rank + 1 : ℝ)) = 1 := by
    rw [← Real.sqrt_mul hfirstNonneg]
    have hinside :
        (rank + 1 : ℝ) / (size : ℝ) *
            ((size : ℝ) / (rank + 1 : ℝ)) = 1 := by
      field_simp
    rw [hinside, Real.sqrt_one]
  unfold regevCenteredRow
  nlinarith

theorem matsumoto_pair_factor_centered
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) (row next : Fin (rank + 1)) :
    ((shape.1 row).val : ℝ) - (shape.1 next).val +
        (next.val : ℝ) - row.val =
      Real.sqrt ((size : ℝ) / (rank + 1 : ℝ)) *
          (regevCenteredRow shape row - regevCenteredRow shape next) +
        (next.val : ℝ) - row.val := by
  have hrow := regevCenteredRow_reconstruct shape hsize row
  have hnext := regevCenteredRow_reconstruct shape hsize next
  linarith

end FibonacciRibbonKernel
