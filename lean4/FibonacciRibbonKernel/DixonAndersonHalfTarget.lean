import FibonacciRibbonKernel.DirichletHalfFubini
import Mathlib.LinearAlgebra.Lagrange

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped Classical

def DixonAndersonInterlacing {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ) : Prop :=
  ∀ index : Fin dimension,
    anchors index.castSucc > roots index ∧
      roots index > anchors index.succ

def dixonAndersonDomain (dimension : ℕ)
    (anchors : Fin (dimension + 1) → ℝ) :
    Set (Fin dimension → ℝ) :=
  {roots | DixonAndersonInterlacing anchors roots}

noncomputable def dixonAndersonHalfIntegrand (dimension : ℕ)
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ) : ℝ :=
  (∏ first : Fin dimension, ∏ next ∈ Finset.Ioi first,
    (roots first - roots next)) *
  ∏ root : Fin dimension, ∏ anchor : Fin (dimension + 1),
    |roots root - anchors anchor| ^ (-1 / 2 : ℝ)

noncomputable def dixonAndersonHalfIntegral (dimension : ℕ)
    (anchors : Fin (dimension + 1) → ℝ) : ℝ :=
  ∫ roots in dixonAndersonDomain dimension anchors,
    dixonAndersonHalfIntegrand dimension anchors roots

noncomputable def expectedDixonAndersonHalfIntegral
    (dimension : ℕ) : ℝ :=
  Real.Gamma (1 / 2) ^ (dimension + 1) /
    Real.Gamma (((dimension + 1 : ℕ) : ℝ) / 2)

def DixonAndersonHalfEvaluation (dimension : ℕ) : Prop :=
  ∀ anchors : Fin (dimension + 1) → ℝ,
    StrictAnti anchors →
      dixonAndersonHalfIntegral dimension anchors =
        expectedDixonAndersonHalfIntegral dimension

theorem dixonAndersonDomain_zero (anchors : Fin 1 → ℝ) :
    dixonAndersonDomain 0 anchors = Set.univ := by
  ext roots
  simp only [dixonAndersonDomain, Set.mem_setOf_eq,
    Set.mem_univ, iff_true]
  intro index
  exact Fin.elim0 index

theorem dixonAndersonHalfIntegrand_zero (anchors : Fin 1 → ℝ) :
    dixonAndersonHalfIntegrand 0 anchors = fun _ => 1 := by
  funext roots
  simp [dixonAndersonHalfIntegrand]

theorem dixonAndersonHalfEvaluation_zero :
    DixonAndersonHalfEvaluation 0 := by
  intro anchors hanchors
  unfold dixonAndersonHalfIntegral expectedDixonAndersonHalfIntegral
  rw [dixonAndersonDomain_zero,
    dixonAndersonHalfIntegrand_zero, setIntegral_univ]
  have hvolume : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
    rw [Measure.volume_pi_eq_dirac (fun row : Fin 0 => Fin.elim0 row)]
    simp
  rw [integral_const, measureReal_def, hvolume]
  norm_num
  have hgamma : Real.Gamma (1 / 2 : ℝ) ≠ 0 := by positivity
  exact (div_self hgamma).symm

end FibonacciRibbonKernel
