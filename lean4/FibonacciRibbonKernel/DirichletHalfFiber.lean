import FibonacciRibbonKernel.DirichletHalfScaling

namespace FibonacciRibbonKernel

open Set Pointwise
open scoped Classical Pointwise

def dirichletTailFiber (dimension : ℕ) (first : ℝ) :
    Set (Fin dimension → ℝ) :=
  {tail | (∀ index, 0 < tail index) ∧
    (∑ index, tail index) < 1 - first}

theorem dirichletTailFiber_eq_smul (dimension : ℕ)
    {first : ℝ} (hfirst : first ∈ Set.Ioo (0 : ℝ) 1) :
    dirichletTailFiber dimension first =
      (1 - first) • dirichletOpenSimplex dimension := by
  ext tail
  have hscale : 0 < 1 - first := sub_pos.mpr hfirst.2
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hscale.ne']
  unfold dirichletTailFiber dirichletOpenSimplex
  simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul]
  have hinverse : 0 < (1 - first)⁻¹ := inv_pos.mpr hscale
  constructor
  · rintro ⟨hpositive, hsum⟩
    constructor
    · intro index
      exact mul_pos hinverse (hpositive index)
    · rw [← Finset.mul_sum]
      rw [inv_mul_lt_iff₀ hscale]
      simpa only [inv_mul_cancel₀ hscale.ne', one_mul, mul_one] using hsum
  · rintro ⟨hpositive, hsum⟩
    constructor
    · intro index
      have hscaled := hpositive index
      exact (mul_pos_iff_of_pos_left hinverse).mp hscaled
    · rw [← Finset.mul_sum] at hsum
      rw [inv_mul_lt_one₀ hscale] at hsum
      exact hsum

theorem finCons_mem_dirichletSimplex_iff (dimension : ℕ)
    (first : ℝ) (tail : Fin dimension → ℝ) :
    Fin.cons first tail ∈ dirichletOpenSimplex (dimension + 1) ↔
      0 < first ∧ tail ∈ dirichletTailFiber dimension first := by
  unfold dirichletOpenSimplex dirichletTailFiber
  simp only [Set.mem_setOf_eq]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  constructor
  · rintro ⟨hpositive, hsum⟩
    constructor
    · simpa using hpositive 0
    · constructor
      · intro index
        simpa using hpositive index.succ
      · linarith
  · rintro ⟨hfirst, hpositive, hsum⟩
    constructor
    · intro index
      cases index using Fin.cases with
      | zero => simpa using hfirst
      | succ index => simpa using hpositive index
    · linarith

end FibonacciRibbonKernel
