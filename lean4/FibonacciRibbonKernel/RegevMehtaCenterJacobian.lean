import FibonacciRibbonKernel.RegevMehtaCenterIntegral
import Mathlib.LinearAlgebra.Matrix.SchurComplement

namespace FibonacciRibbonKernel

open scoped Classical Matrix

noncomputable def mehtaCenterBlockMatrix (rank : ℕ) :
    Matrix (Fin rank ⊕ Fin 1) (Fin rank ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks
    (1 : Matrix (Fin rank) (Fin rank) ℝ)
    (fun _ _ => 1)
    (fun _ _ => -1)
    (1 : Matrix (Fin 1) (Fin 1) ℝ)

theorem mehtaCenterBlockMatrix_det (rank : ℕ) :
    (mehtaCenterBlockMatrix rank).det = (rank + 1 : ℕ) := by
  unfold mehtaCenterBlockMatrix
  rw [Matrix.det_fromBlocks_one₁₁]
  let lowerLeft : Matrix (Fin 1) (Fin rank) ℝ :=
    fun _ _ => -1
  let upperRight : Matrix (Fin rank) (Fin 1) ℝ :=
    fun _ _ => 1
  have hmatrix :
      (1 : Matrix (Fin 1) (Fin 1) ℝ) -
          lowerLeft * upperRight =
        fun _ _ : Fin 1 => ((rank + 1 : ℕ) : ℝ) := by
    ext row column
    fin_cases row
    fin_cases column
    simp [lowerLeft, upperRight, Matrix.mul_apply]
    ring
  rw [hmatrix]
  simp

theorem mehtaCenterBlockMatrix_det_ne_zero (rank : ℕ) :
    (mehtaCenterBlockMatrix rank).det ≠ 0 := by
  rw [mehtaCenterBlockMatrix_det]
  positivity

end FibonacciRibbonKernel
