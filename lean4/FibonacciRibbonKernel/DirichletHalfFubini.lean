import FibonacciRibbonKernel.DirichletHalfPair
import Mathlib.MeasureTheory.Integral.Prod

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped Classical

theorem integrable_dirichletPairRestricted_section
    (dimension : ℕ) (first : ℝ)
    (hintegrable : IntegrableOn
      (dirichletHalfIntegrand dimension)
      (dirichletOpenSimplex dimension)) :
    Integrable (fun tail : Fin dimension → ℝ =>
      dirichletPairRestricted dimension (first, tail)) := by
  by_cases hfirst : first ∈ Set.Ioo (0 : ℝ) 1
  · have hfunction : (fun tail : Fin dimension → ℝ =>
        dirichletPairRestricted dimension (first, tail)) =
      (dirichletTailFiber dimension first).indicator
        (fun tail => dirichletHalfIntegrand (dimension + 1)
          (Fin.cons first tail)) := by
      funext tail
      unfold dirichletPairRestricted
      by_cases htail : tail ∈ dirichletTailFiber dimension first
      · rw [Set.indicator_of_mem htail, Set.indicator_of_mem]
        exact ⟨hfirst.1, htail⟩
      · rw [Set.indicator_of_notMem htail, Set.indicator_of_notMem]
        intro hpair
        exact htail hpair.2
    rw [hfunction]
    exact IntegrableOn.integrable_indicator
      (integrableOn_dirichletHalfTail dimension hfirst hintegrable)
      (dirichletTailFiber_measurableSet dimension first)
  · have hzero : (fun tail : Fin dimension → ℝ =>
        dirichletPairRestricted dimension (first, tail)) =
          (fun _ => 0) := by
      funext tail
      unfold dirichletPairRestricted
      rw [Set.indicator_of_notMem]
      intro hpair
      exact hfirst (dirichletPairDomain_first_mem hpair)
    rw [hzero]
    change Integrable (0 : (Fin dimension → ℝ) → ℝ) volume
    exact integrable_zero (Fin dimension → ℝ) ℝ
      (volume : Measure (Fin dimension → ℝ))

theorem integrable_dirichletPairRestricted_outer_norm
    (dimension : ℕ) :
    Integrable (fun first : ℝ =>
      ∫ tail : Fin dimension → ℝ,
        ‖dirichletPairRestricted dimension (first, tail)‖) := by
  have hfunction : (fun first : ℝ =>
      ∫ tail : Fin dimension → ℝ,
        ‖dirichletPairRestricted dimension (first, tail)‖) =
    (Set.Ioo (0 : ℝ) 1).indicator
      (fun first => dirichletHalfIntegral dimension *
        dirichletHalfOuterWeight dimension first) := by
    funext first
    rw [dirichletPairRestricted_inner_norm]
    by_cases hfirst : first ∈ Set.Ioo (0 : ℝ) 1
    · rw [Set.indicator_of_mem hfirst, Set.indicator_of_mem hfirst,
        dirichletHalfTailIntegral_eq dimension hfirst]
      ring
    · rw [Set.indicator_of_notMem hfirst,
        Set.indicator_of_notMem hfirst]
  rw [hfunction]
  rw [integrable_indicator_iff measurableSet_Ioo]
  exact (integrableOn_dirichletHalfOuterWeight dimension).const_mul
    (dirichletHalfIntegral dimension)

theorem integrable_dirichletPairRestricted
    (dimension : ℕ)
    (hintegrable : IntegrableOn
      (dirichletHalfIntegrand dimension)
      (dirichletOpenSimplex dimension)) :
    Integrable (dirichletPairRestricted dimension)
      ((volume : Measure ℝ).prod
        (volume : Measure (Fin dimension → ℝ))) := by
  rw [integrable_prod_iff
    (aestronglyMeasurable_dirichletPairRestricted dimension)]
  constructor
  · exact ae_of_all _ fun first =>
      integrable_dirichletPairRestricted_section dimension first hintegrable
  · exact integrable_dirichletPairRestricted_outer_norm dimension

theorem dirichletHalfIntegral_succ_recurrence
    (dimension : ℕ)
    (hintegrable : IntegrableOn
      (dirichletHalfIntegrand dimension)
      (dirichletOpenSimplex dimension)) :
    dirichletHalfIntegral (dimension + 1) =
      (Real.Gamma (1 / 2) *
        Real.Gamma (((dimension + 1 : ℕ) : ℝ) / 2) /
          Real.Gamma (((dimension + 2 : ℕ) : ℝ) / 2)) *
        dirichletHalfIntegral dimension := by
  have hpair := integrable_dirichletPairRestricted dimension hintegrable
  have hfubini := integral_prod (dirichletPairRestricted dimension) hpair
  have hsetIntegral :
      (∫ input in dirichletPairDomain dimension,
        dirichletHalfIntegrand (dimension + 1)
          (Fin.cons input.1 input.2)
        ∂((volume : Measure ℝ).prod
          (volume : Measure (Fin dimension → ℝ)))) =
      ∫ input, dirichletPairRestricted dimension input
        ∂((volume : Measure ℝ).prod
          (volume : Measure (Fin dimension → ℝ))) := by
    unfold dirichletPairRestricted
    rw [integral_indicator (dirichletPairDomain_measurableSet dimension)]
  have hleft : dirichletHalfIntegral (dimension + 1) =
      ∫ input, dirichletPairRestricted dimension input
        ∂((volume : Measure ℝ).prod
          (volume : Measure (Fin dimension → ℝ))) :=
    (dirichletHalfIntegral_eq_pair dimension).trans hsetIntegral
  have houter :
      (∫ first : ℝ,
        (Set.Ioo (0 : ℝ) 1).indicator
          (dirichletHalfTailIntegral dimension) first) =
      (∫ first in Set.Ioo (0 : ℝ) 1,
        dirichletHalfOuterWeight dimension first) *
          dirichletHalfIntegral dimension := by
    rw [integral_indicator measurableSet_Ioo]
    rw [show (∫ first in Set.Ioo (0 : ℝ) 1,
        dirichletHalfTailIntegral dimension first) =
      ∫ first in Set.Ioo (0 : ℝ) 1,
        dirichletHalfOuterWeight dimension first *
          dirichletHalfIntegral dimension by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro first hfirst
      exact dirichletHalfTailIntegral_eq dimension hfirst]
    rw [integral_mul_const]
  have hbeta := integral_selbergHalfWeight_Ioo
    (alpha := (1 / 2 : ℝ))
    (beta := (((dimension + 1 : ℕ) : ℝ) / 2))
    (by norm_num) (by positivity)
  have hdenominator :
      (1 / 2 : ℝ) + (((dimension + 1 : ℕ) : ℝ) / 2) =
        (((dimension + 2 : ℕ) : ℝ) / 2) := by
    push_cast
    ring
  rw [hdenominator] at hbeta
  calc
    dirichletHalfIntegral (dimension + 1) =
        ∫ input, dirichletPairRestricted dimension input
          ∂((volume : Measure ℝ).prod
            (volume : Measure (Fin dimension → ℝ))) := hleft
    _ = ∫ first : ℝ, ∫ tail : Fin dimension → ℝ,
          dirichletPairRestricted dimension (first, tail) := hfubini
    _ = ∫ first : ℝ,
          (Set.Ioo (0 : ℝ) 1).indicator
            (dirichletHalfTailIntegral dimension) first := by
      apply integral_congr_ae
      filter_upwards with first
      exact dirichletPairRestricted_inner dimension first
    _ = (∫ first in Set.Ioo (0 : ℝ) 1,
          dirichletHalfOuterWeight dimension first) *
            dirichletHalfIntegral dimension := houter
    _ = _ := by
      rw [dirichletHalfOuterWeight_eq_selberg, hbeta]

theorem integrableOn_dirichletHalfIntegrand_succ
    (dimension : ℕ)
    (hintegrable : IntegrableOn
      (dirichletHalfIntegrand dimension)
      (dirichletOpenSimplex dimension)) :
    IntegrableOn (dirichletHalfIntegrand (dimension + 1))
      (dirichletOpenSimplex (dimension + 1)) := by
  let pairFunction : (ℝ × (Fin dimension → ℝ)) → ℝ := fun input =>
    dirichletHalfIntegrand (dimension + 1) (Fin.cons input.1 input.2)
  have hpair := integrable_dirichletPairRestricted dimension hintegrable
  have hpairOn : IntegrableOn pairFunction (dirichletPairDomain dimension)
      ((volume : Measure ℝ).prod
        (volume : Measure (Fin dimension → ℝ))) := by
    rw [← integrable_indicator_iff
      (dirichletPairDomain_measurableSet dimension)]
    change Integrable (dirichletPairRestricted dimension)
      ((volume : Measure ℝ).prod
        (volume : Measure (Fin dimension → ℝ)))
    exact hpair
  have htransport :=
    (MeasurePreserving.integrableOn_comp_preimage
      (volume_preserving_dirichletSplitFirst dimension)
      (dirichletSplitFirstEquiv dimension).measurableEmbedding).mpr hpairOn
  rw [dirichletSplitFirst_preimage_domain] at htransport
  apply IntegrableOn.congr_fun htransport
  · intro coordinates hcoordinates
    change pairFunction (dirichletSplitFirstEquiv dimension coordinates) =
      dirichletHalfIntegrand (dimension + 1) coordinates
    rw [dirichletSplitFirstEquiv_apply]
    dsimp only [pairFunction]
    exact congrArg (dirichletHalfIntegrand (dimension + 1))
      (Fin.cons_self_tail coordinates)
  · exact dirichletOpenSimplex_measurableSet (dimension + 1)

theorem integrableOn_dirichletHalfIntegrand_all (dimension : ℕ) :
    IntegrableOn (dirichletHalfIntegrand dimension)
      (dirichletOpenSimplex dimension) := by
  induction dimension with
  | zero =>
      rw [dirichletOpenSimplex_zero, dirichletHalfIntegrand_zero]
      rw [IntegrableOn, Measure.restrict_univ]
      change Integrable (fun _ : Fin 0 → ℝ => (1 : ℝ)) volume
      rw [integrable_const_iff]
      right
      have hvolume : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
        rw [Measure.volume_pi_eq_dirac (fun row : Fin 0 => Fin.elim0 row)]
        simp
      exact ⟨by simp [hvolume]⟩
  | succ dimension ih =>
      exact integrableOn_dirichletHalfIntegrand_succ dimension ih

theorem dirichletHalfEvaluation_all (dimension : ℕ) :
    DirichletHalfEvaluation dimension := by
  induction dimension with
  | zero => exact dirichletHalfEvaluation_zero
  | succ dimension ih =>
      unfold DirichletHalfEvaluation at ih ⊢
      have hintegrable := integrableOn_dirichletHalfIntegrand_all dimension
      rw [dirichletHalfIntegral_succ_recurrence dimension hintegrable,
        ih, expectedDirichletHalfIntegral_succ]

end FibonacciRibbonKernel
