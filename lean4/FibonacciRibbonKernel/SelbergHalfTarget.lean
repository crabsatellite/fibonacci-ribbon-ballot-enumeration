import FibonacciRibbonKernel.MehtaVandermondeSymmetry
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped Classical

def selbergUnitBox (dimension : ℕ) : Set (Fin dimension → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Ioo 0 1)

def orderedSelbergDomain (dimension : ℕ) : Set (Fin dimension → ℝ) :=
  selbergUnitBox dimension ∩ standardMehtaChamber dimension

noncomputable def selbergHalfWeight
    (alpha beta : ℝ) (value : ℝ) : ℝ :=
  value ^ (alpha - 1) * (1 - value) ^ (beta - 1)

noncomputable def selbergHalfIntegrand
    (dimension : ℕ) (alpha beta : ℝ)
    (coordinates : Fin dimension → ℝ) : ℝ :=
  (∏ row, selbergHalfWeight alpha beta (coordinates row)) *
    standardMehtaVandermonde dimension coordinates

noncomputable def orderedSelbergHalfIntegral
    (dimension : ℕ) (alpha beta : ℝ) : ℝ :=
  ∫ coordinates in orderedSelbergDomain dimension,
    selbergHalfIntegrand dimension alpha beta coordinates

noncomputable def selbergHalfGammaProduct
    (dimension : ℕ) (alpha beta : ℝ) : ℝ :=
  ∏ j ∈ Finset.range dimension,
    (Real.Gamma (alpha + (j : ℝ) / 2) *
      Real.Gamma (beta + (j : ℝ) / 2) *
      Real.Gamma (1 + ((j + 1 : ℕ) : ℝ) / 2)) /
        (Real.Gamma
          (alpha + beta + ((dimension + j - 1 : ℕ) : ℝ) / 2) *
          Real.Gamma (3 / 2))

noncomputable def expectedOrderedSelbergHalfIntegral
    (dimension : ℕ) (alpha beta : ℝ) : ℝ :=
  selbergHalfGammaProduct dimension alpha beta /
    (dimension.factorial : ℝ)

def OrderedSelbergHalfEvaluation
    (dimension : ℕ) (alpha beta : ℝ) : Prop :=
  orderedSelbergHalfIntegral dimension alpha beta =
    expectedOrderedSelbergHalfIntegral dimension alpha beta

theorem selbergUnitBox_zero : selbergUnitBox 0 = Set.univ := by
  ext coordinates
  simp [selbergUnitBox]

theorem orderedSelbergDomain_zero : orderedSelbergDomain 0 = Set.univ := by
  rw [orderedSelbergDomain, selbergUnitBox_zero]
  ext coordinates
  simp only [Set.mem_inter_iff, Set.mem_univ, true_and, iff_true,
    standardMehtaChamber, Set.mem_setOf_eq]
  intro row
  exact Fin.elim0 row

theorem selbergHalfIntegrand_zero (alpha beta : ℝ) :
    selbergHalfIntegrand 0 alpha beta = fun _ => 1 := by
  funext coordinates
  simp [selbergHalfIntegrand, standardMehtaVandermonde]

theorem orderedSelbergHalfIntegral_zero (alpha beta : ℝ) :
    orderedSelbergHalfIntegral 0 alpha beta = 1 := by
  unfold orderedSelbergHalfIntegral
  rw [orderedSelbergDomain_zero, setIntegral_univ,
    selbergHalfIntegrand_zero]
  have hvolume : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
    rw [Measure.volume_pi_eq_dirac (fun row : Fin 0 => Fin.elim0 row)]
    simp
  rw [integral_const, measureReal_def, hvolume]
  norm_num

theorem expectedOrderedSelbergHalfIntegral_zero (alpha beta : ℝ) :
    expectedOrderedSelbergHalfIntegral 0 alpha beta = 1 := by
  simp [expectedOrderedSelbergHalfIntegral, selbergHalfGammaProduct]

theorem orderedSelbergHalfEvaluation_zero (alpha beta : ℝ) :
    OrderedSelbergHalfEvaluation 0 alpha beta := by
  unfold OrderedSelbergHalfEvaluation
  rw [orderedSelbergHalfIntegral_zero,
    expectedOrderedSelbergHalfIntegral_zero]

end FibonacciRibbonKernel
