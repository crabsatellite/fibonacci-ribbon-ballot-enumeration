import FibonacciRibbonKernel.RegevMehtaGeometry

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped Classical

noncomputable def mehtaCenterTransform (rank : ℕ)
    (input : (Fin rank → ℝ) × ℝ) : Fin (rank + 1) → ℝ :=
  fun row => tracelessExtend input.1 row + input.2

noncomputable def standardMehtaGaussian (dimension : ℕ)
    (coordinates : Fin dimension → ℝ) : ℝ :=
  Real.exp (-(∑ row, coordinates row ^ 2 / 2))

noncomputable def standardMehtaVandermonde (dimension : ℕ)
    (coordinates : Fin dimension → ℝ) : ℝ :=
  ∏ row : Fin dimension, ∏ next ∈ Finset.Ioi row,
    |coordinates row - coordinates next|

noncomputable def standardMehtaIntegrand (dimension : ℕ)
    (coordinates : Fin dimension → ℝ) : ℝ :=
  standardMehtaGaussian dimension coordinates *
    standardMehtaVandermonde dimension coordinates

theorem mehtaCenterTransform_apply (rank : ℕ)
    (input : (Fin rank → ℝ) × ℝ) (row : Fin (rank + 1)) :
    mehtaCenterTransform rank input row =
      tracelessExtend input.1 row + input.2 := rfl

theorem mehtaCenterTransform_sum (rank : ℕ)
    (input : (Fin rank → ℝ) × ℝ) :
    ∑ row, mehtaCenterTransform rank input row =
      (rank + 1 : ℕ) * input.2 := by
  unfold mehtaCenterTransform
  rw [Finset.sum_add_distrib, tracelessExtend_sum]
  simp

theorem mehtaCenterTransform_sum_sq (rank : ℕ)
    (input : (Fin rank → ℝ) × ℝ) :
    ∑ row, mehtaCenterTransform rank input row ^ 2 =
      (∑ row, tracelessExtend input.1 row ^ 2) +
        (rank + 1 : ℕ) * input.2 ^ 2 := by
  unfold mehtaCenterTransform
  simp_rw [add_sq, Finset.sum_add_distrib]
  have hcross :
      (∑ row : Fin (rank + 1),
        2 * tracelessExtend input.1 row * input.2) = 0 := by
    rw [show (∑ row : Fin (rank + 1),
        2 * tracelessExtend input.1 row * input.2) =
      2 * (∑ row : Fin (rank + 1),
        tracelessExtend input.1 row) * input.2 by
      rw [Finset.mul_sum, Finset.sum_mul]]
    rw [tracelessExtend_sum]
    ring
  rw [hcross]
  simp

theorem mehtaCenterTransform_sub (rank : ℕ)
    (input : (Fin rank → ℝ) × ℝ)
    (row next : Fin (rank + 1)) :
    mehtaCenterTransform rank input row -
        mehtaCenterTransform rank input next =
      tracelessExtend input.1 row - tracelessExtend input.1 next := by
  unfold mehtaCenterTransform
  ring

theorem mehtaCenterTransform_antitone_iff (rank : ℕ)
    (input : (Fin rank → ℝ) × ℝ) :
    Antitone (mehtaCenterTransform rank input) ↔
      Antitone (tracelessExtend input.1) := by
  constructor
  · intro h row next hle
    have hvalue := h hle
    simp only [mehtaCenterTransform_apply] at hvalue
    linarith
  · intro h row next hle
    simp only [mehtaCenterTransform_apply]
    simpa [add_comm] using add_le_add_right (h hle) input.2

theorem standardMehtaGaussian_center (rank : ℕ)
    (input : (Fin rank → ℝ) × ℝ) :
    standardMehtaGaussian (rank + 1)
        (mehtaCenterTransform rank input) =
      Real.exp (-((rank + 1 : ℕ) : ℝ) * input.2 ^ 2 / 2) *
        regevGaussianKernel rank input.1 := by
  unfold standardMehtaGaussian regevGaussianKernel
  rw [show (∑ row : Fin (rank + 1),
        mehtaCenterTransform rank input row ^ 2 / 2) =
      (∑ row : Fin (rank + 1),
        tracelessExtend input.1 row ^ 2 / 2) +
          ((rank + 1 : ℕ) : ℝ) * input.2 ^ 2 / 2 by
    rw [← Finset.sum_div, ← Finset.sum_div,
      mehtaCenterTransform_sum_sq]
    push_cast
    ring]
  rw [show -((∑ row : Fin (rank + 1),
        tracelessExtend input.1 row ^ 2 / 2) +
          ((rank + 1 : ℕ) : ℝ) * input.2 ^ 2 / 2) =
      (-((rank + 1 : ℕ) : ℝ) * input.2 ^ 2 / 2) +
        -(∑ row : Fin (rank + 1),
          tracelessExtend input.1 row ^ 2 / 2) by ring]
  rw [Real.exp_add]

theorem standardMehtaVandermonde_center
    (rank : ℕ) (input : (Fin rank → ℝ) × ℝ)
    (hchamber : input.1 ∈ regevChamber rank) :
    standardMehtaVandermonde (rank + 1)
        (mehtaCenterTransform rank input) =
      regevVandermonde rank input.1 := by
  unfold standardMehtaVandermonde regevVandermonde
  apply Finset.prod_congr rfl
  intro row hrow
  apply Finset.prod_congr rfl
  intro next hnext
  rw [mehtaCenterTransform_sub]
  rw [abs_of_nonneg]
  exact sub_nonneg.mpr (hchamber (Finset.mem_Ioi.mp hnext).le)

theorem standardMehtaIntegrand_center
    (rank : ℕ) (input : (Fin rank → ℝ) × ℝ)
    (hchamber : input.1 ∈ regevChamber rank) :
    standardMehtaIntegrand (rank + 1)
        (mehtaCenterTransform rank input) =
      Real.exp (-((rank + 1 : ℕ) : ℝ) * input.2 ^ 2 / 2) *
        (regevGaussianKernel rank input.1 *
          regevVandermonde rank input.1) := by
  unfold standardMehtaIntegrand
  rw [standardMehtaGaussian_center,
    standardMehtaVandermonde_center rank input hchamber]
  ring

end FibonacciRibbonKernel
