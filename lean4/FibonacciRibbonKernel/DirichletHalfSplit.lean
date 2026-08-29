import FibonacciRibbonKernel.DirichletHalfInnerIntegral
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped Classical

noncomputable def dirichletSplitFirstEquiv (dimension : ℕ) :
    (Fin (dimension + 1) → ℝ) ≃ᵐ ℝ × (Fin dimension → ℝ) :=
  MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (dimension + 1) => ℝ) 0

theorem dirichletSplitFirstEquiv_apply (dimension : ℕ)
    (coordinates : Fin (dimension + 1) → ℝ) :
    dirichletSplitFirstEquiv dimension coordinates =
      (coordinates 0, fun index => coordinates index.succ) := by
  apply Prod.ext
  · rfl
  · funext index
    change Fin.tail coordinates index = coordinates index.succ
    rfl

theorem dirichletSplitFirstEquiv_symm_apply (dimension : ℕ)
    (input : ℝ × (Fin dimension → ℝ)) :
    (dirichletSplitFirstEquiv dimension).symm input =
      Fin.cons input.1 input.2 := by
  apply (dirichletSplitFirstEquiv dimension).injective
  rw [(dirichletSplitFirstEquiv dimension).apply_symm_apply]
  rw [dirichletSplitFirstEquiv_apply]
  apply Prod.ext
  · simp
  · funext index
    simp

theorem volume_preserving_dirichletSplitFirst (dimension : ℕ) :
    MeasurePreserving (dirichletSplitFirstEquiv dimension)
      (volume : Measure (Fin (dimension + 1) → ℝ))
      ((volume : Measure ℝ).prod
        (volume : Measure (Fin dimension → ℝ))) :=
  volume_preserving_piFinSuccAbove
    (fun _ : Fin (dimension + 1) => ℝ) 0

def dirichletPairDomain (dimension : ℕ) :
    Set (ℝ × (Fin dimension → ℝ)) :=
  {input | 0 < input.1 ∧
    input.2 ∈ dirichletTailFiber dimension input.1}

theorem dirichletSplitFirst_preimage_domain (dimension : ℕ) :
    ⇑(dirichletSplitFirstEquiv dimension) ⁻¹'
        dirichletPairDomain dimension =
      dirichletOpenSimplex (dimension + 1) := by
  ext coordinates
  rw [Set.mem_preimage]
  unfold dirichletPairDomain
  simp only [Set.mem_setOf_eq]
  rw [dirichletSplitFirstEquiv_apply]
  have hiff := (finCons_mem_dirichletSimplex_iff dimension
    (coordinates 0) (fun index => coordinates index.succ)).symm
  rw [← Fin.cons_self_tail coordinates]
  exact hiff

theorem dirichletHalfIntegral_eq_pair (dimension : ℕ) :
    dirichletHalfIntegral (dimension + 1) =
      ∫ input in dirichletPairDomain dimension,
        dirichletHalfIntegrand (dimension + 1)
          (Fin.cons input.1 input.2)
        ∂((volume : Measure ℝ).prod
          (volume : Measure (Fin dimension → ℝ))) := by
  unfold dirichletHalfIntegral
  have hchange :=
    (volume_preserving_dirichletSplitFirst dimension).setIntegral_preimage_emb
      (dirichletSplitFirstEquiv dimension).measurableEmbedding
      (fun input : ℝ × (Fin dimension → ℝ) =>
        dirichletHalfIntegrand (dimension + 1)
          (Fin.cons input.1 input.2))
      (dirichletPairDomain dimension)
  rw [dirichletSplitFirst_preimage_domain] at hchange
  rw [← hchange]
  apply setIntegral_congr_fun
  · exact (dirichletOpenSimplex_measurableSet (dimension + 1))
  · intro coordinates hcoordinates
    change dirichletHalfIntegrand (dimension + 1) coordinates =
      dirichletHalfIntegrand (dimension + 1)
        (Fin.cons ((dirichletSplitFirstEquiv dimension coordinates).1)
          ((dirichletSplitFirstEquiv dimension coordinates).2))
    rw [dirichletSplitFirstEquiv_apply]
    exact congrArg (dirichletHalfIntegrand (dimension + 1))
      (Fin.cons_self_tail coordinates).symm

end FibonacciRibbonKernel
