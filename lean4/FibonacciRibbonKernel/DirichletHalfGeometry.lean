import FibonacciRibbonKernel.DirichletHalfTarget

namespace FibonacciRibbonKernel

open Set
open scoped Classical

noncomputable def dirichletConsTransform (dimension : ℕ)
    (input : ℝ × (Fin dimension → ℝ)) : Fin (dimension + 1) → ℝ :=
  Fin.cons input.1 ((1 - input.1) • input.2)

@[simp] theorem dirichletConsTransform_zero (dimension : ℕ)
    (input : ℝ × (Fin dimension → ℝ)) :
    dirichletConsTransform dimension input 0 = input.1 := by
  simp [dirichletConsTransform]

@[simp] theorem dirichletConsTransform_succ (dimension : ℕ)
    (input : ℝ × (Fin dimension → ℝ)) (index : Fin dimension) :
    dirichletConsTransform dimension input index.succ =
      (1 - input.1) * input.2 index := by
  simp [dirichletConsTransform]

theorem dirichletConsTransform_sum (dimension : ℕ)
    (input : ℝ × (Fin dimension → ℝ)) :
    ∑ index, dirichletConsTransform dimension input index =
      input.1 + (1 - input.1) * ∑ index, input.2 index := by
  rw [Fin.sum_univ_succ]
  simp only [dirichletConsTransform_zero,
    dirichletConsTransform_succ]
  rw [← Finset.mul_sum]

theorem dirichletConsTransform_mem_iff (dimension : ℕ)
    (input : ℝ × (Fin dimension → ℝ)) :
    dirichletConsTransform dimension input ∈
        dirichletOpenSimplex (dimension + 1) ↔
      input.1 ∈ Set.Ioo (0 : ℝ) 1 ∧
        input.2 ∈ dirichletOpenSimplex dimension := by
  unfold dirichletOpenSimplex
  simp only [Set.mem_setOf_eq, Set.mem_Ioo]
  rw [dirichletConsTransform_sum]
  constructor
  · rintro ⟨hpositive, hsum⟩
    have hfirst : 0 < input.1 := by
      simpa using hpositive 0
    have htailNonneg : 0 ≤
        (1 - input.1) * ∑ index, input.2 index := by
      rw [Finset.mul_sum]
      apply Finset.sum_nonneg
      intro index hindex
      simpa only [dirichletConsTransform_succ] using
        (hpositive index.succ).le
    have hfirstLt : input.1 < 1 := by linarith
    have hscale : 0 < 1 - input.1 := sub_pos.mpr hfirstLt
    have hcoordinate : ∀ index, 0 < input.2 index := by
      intro index
      have hscaled := hpositive index.succ
      rw [dirichletConsTransform_succ] at hscaled
      exact (mul_pos_iff_of_pos_left hscale).mp hscaled
    have htailSum : (∑ index, input.2 index) < 1 := by
      have hrewrite :
          input.1 + (1 - input.1) * (∑ index, input.2 index) - 1 =
            (1 - input.1) * ((∑ index, input.2 index) - 1) := by ring
      have hnegative :
          (1 - input.1) * ((∑ index, input.2 index) - 1) < 0 := by
        rw [← hrewrite]
        linarith
      rcases mul_neg_iff.mp hnegative with hcase | hcase
      · exact sub_neg.mp hcase.2
      · exact (not_lt_of_ge hscale.le hcase.1).elim
    exact ⟨⟨hfirst, hfirstLt⟩, hcoordinate, htailSum⟩
  · rintro ⟨⟨hfirst, hfirstLt⟩, hcoordinate, htailSum⟩
    have hscale : 0 < 1 - input.1 := sub_pos.mpr hfirstLt
    constructor
    · intro index
      cases index using Fin.cases with
      | zero => simpa using hfirst
      | succ index =>
          rw [dirichletConsTransform_succ]
          exact mul_pos hscale (hcoordinate index)
    · have hrewrite :
          input.1 + (1 - input.1) * (∑ index, input.2 index) - 1 =
            (1 - input.1) * ((∑ index, input.2 index) - 1) := by ring
      have hnegative :
          input.1 + (1 - input.1) * (∑ index, input.2 index) - 1 < 0 := by
        rw [hrewrite]
        exact mul_neg_of_pos_of_neg hscale (sub_neg.mpr htailSum)
      linarith

end FibonacciRibbonKernel
