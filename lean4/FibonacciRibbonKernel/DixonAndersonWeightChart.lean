import FibonacciRibbonKernel.DixonAndersonWeightPositivity

namespace FibonacciRibbonKernel

open scoped Classical

noncomputable def andersonWeightChart {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ) : Fin dimension → ℝ :=
  fun anchor => andersonWeight anchors roots anchor.castSucc

noncomputable def simplexExtend {dimension : ℕ}
    (coordinates : Fin dimension → ℝ) : Fin (dimension + 1) → ℝ :=
  Fin.lastCases (1 - ∑ index, coordinates index) coordinates

@[simp] theorem simplexExtend_castSucc {dimension : ℕ}
    (coordinates : Fin dimension → ℝ) (index : Fin dimension) :
    simplexExtend coordinates index.castSucc = coordinates index := by
  simp [simplexExtend]

@[simp] theorem simplexExtend_last {dimension : ℕ}
    (coordinates : Fin dimension → ℝ) :
    simplexExtend coordinates (Fin.last dimension) =
      1 - ∑ index, coordinates index := by
  simp [simplexExtend]

theorem simplexExtend_sum {dimension : ℕ}
    (coordinates : Fin dimension → ℝ) :
    ∑ anchor, simplexExtend coordinates anchor = 1 := by
  rw [Fin.sum_univ_castSucc, simplexExtend_last]
  simp

theorem simplexExtend_andersonWeightChart {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ)
    (hanchors : Function.Injective anchors) :
    simplexExtend (andersonWeightChart anchors roots) =
      andersonWeight anchors roots := by
  funext anchor
  cases anchor using Fin.lastCases with
  | last =>
      rw [simplexExtend_last]
      unfold andersonWeightChart
      have hsum := sum_andersonWeight_eq_one anchors roots hanchors
      rw [Fin.sum_univ_castSucc] at hsum
      linarith
  | cast index =>
      rw [simplexExtend_castSucc]
      rfl

theorem andersonWeightChart_mem_simplex {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ)
    (hanchors : StrictAnti anchors)
    (hinterlace : DixonAndersonInterlacing anchors roots) :
    andersonWeightChart anchors roots ∈
      dirichletOpenSimplex dimension := by
  constructor
  · intro index
    exact andersonWeight_pos anchors roots hanchors hinterlace index.castSucc
  · have hlast := andersonWeight_pos anchors roots hanchors hinterlace
      (Fin.last dimension)
    have hextend := congrFun
      (simplexExtend_andersonWeightChart anchors roots hanchors.injective)
      (Fin.last dimension)
    rw [simplexExtend_last] at hextend
    linarith

theorem roots_strictAnti_of_interlacing {dimension : ℕ}
    {anchors : Fin (dimension + 1) → ℝ}
    {roots : Fin dimension → ℝ}
    (hanchors : StrictAnti anchors)
    (hinterlace : DixonAndersonInterlacing anchors roots) :
    StrictAnti roots := by
  intro first next hlt
  have hindex : first.succ ≤ next.castSucc := by
    exact_mod_cast hlt
  exact ((hinterlace next).1.trans_le
    (hanchors.antitone hindex)).trans (hinterlace first).2

end FibonacciRibbonKernel
