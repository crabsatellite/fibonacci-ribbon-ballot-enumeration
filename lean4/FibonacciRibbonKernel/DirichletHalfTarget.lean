import FibonacciRibbonKernel.SelbergHalfRecurrenceAlgebra

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped Classical

def dirichletOpenSimplex (dimension : ℕ) : Set (Fin dimension → ℝ) :=
  {coordinates |
    (∀ index, 0 < coordinates index) ∧
      (∑ index, coordinates index) < 1}

noncomputable def dirichletHalfIntegrand (dimension : ℕ)
    (coordinates : Fin dimension → ℝ) : ℝ :=
  (∏ index, coordinates index ^ (-1 / 2 : ℝ)) *
    (1 - ∑ index, coordinates index) ^ (-1 / 2 : ℝ)

noncomputable def dirichletHalfIntegral (dimension : ℕ) : ℝ :=
  ∫ coordinates in dirichletOpenSimplex dimension,
    dirichletHalfIntegrand dimension coordinates

noncomputable def expectedDirichletHalfIntegral (dimension : ℕ) : ℝ :=
  Real.Gamma (1 / 2) ^ (dimension + 1) /
    Real.Gamma (((dimension + 1 : ℕ) : ℝ) / 2)

def DirichletHalfEvaluation (dimension : ℕ) : Prop :=
  dirichletHalfIntegral dimension = expectedDirichletHalfIntegral dimension

theorem dirichletOpenSimplex_zero :
    dirichletOpenSimplex 0 = Set.univ := by
  ext coordinates
  simp [dirichletOpenSimplex]

theorem dirichletHalfIntegrand_zero :
    dirichletHalfIntegrand 0 = fun _ => 1 := by
  funext coordinates
  simp [dirichletHalfIntegrand]

theorem dirichletHalfIntegral_zero :
    dirichletHalfIntegral 0 = 1 := by
  unfold dirichletHalfIntegral
  rw [dirichletOpenSimplex_zero, setIntegral_univ,
    dirichletHalfIntegrand_zero]
  have hvolume : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
    rw [Measure.volume_pi_eq_dirac (fun row : Fin 0 => Fin.elim0 row)]
    simp
  rw [integral_const, measureReal_def, hvolume]
  norm_num

theorem expectedDirichletHalfIntegral_zero :
    expectedDirichletHalfIntegral 0 = 1 := by
  unfold expectedDirichletHalfIntegral
  norm_num
  have hgamma : Real.Gamma (1 / 2 : ℝ) ≠ 0 := by positivity
  exact hgamma

theorem dirichletHalfEvaluation_zero : DirichletHalfEvaluation 0 := by
  unfold DirichletHalfEvaluation
  rw [dirichletHalfIntegral_zero,
    expectedDirichletHalfIntegral_zero]

theorem expectedDirichletHalfIntegral_succ (dimension : ℕ) :
    expectedDirichletHalfIntegral (dimension + 1) =
      (Real.Gamma (1 / 2) *
        Real.Gamma (((dimension + 1 : ℕ) : ℝ) / 2) /
          Real.Gamma (((dimension + 2 : ℕ) : ℝ) / 2)) *
        expectedDirichletHalfIntegral dimension := by
  unfold expectedDirichletHalfIntegral
  have hgammaMiddle :
      Real.Gamma (((dimension + 1 : ℕ) : ℝ) / 2) ≠ 0 := by positivity
  field_simp [hgammaMiddle]
  ring

end FibonacciRibbonKernel
