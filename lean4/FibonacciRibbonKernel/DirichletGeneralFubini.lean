import FibonacciRibbonKernel.DirichletGeneralTail
import FibonacciRibbonKernel.DirichletHalfPair
import Mathlib.MeasureTheory.Integral.Prod

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped Classical BigOperators

noncomputable def dirichletGeneralPairRestricted (dimension : ℕ)
    (parameters : Fin (dimension + 2) → ℝ) :
    (ℝ × (Fin dimension → ℝ)) → ℝ :=
  (dirichletPairDomain dimension).indicator fun input =>
    dirichletGeneralIntegrand (dimension + 1) parameters
      (Fin.cons input.1 input.2)

theorem dirichletGeneralPairRestricted_nonneg
    (dimension : ℕ) (parameters : Fin (dimension + 2) → ℝ)
    (input : ℝ × (Fin dimension → ℝ)) :
    0 ≤ dirichletGeneralPairRestricted dimension parameters input := by
  by_cases hinput : input ∈ dirichletPairDomain dimension
  · rw [dirichletGeneralPairRestricted, Set.indicator_of_mem hinput]
    exact (dirichletGeneralIntegrand_pos_of_mem
      ((finCons_mem_dirichletSimplex_iff dimension
        input.1 input.2).mpr hinput)).le
  · rw [dirichletGeneralPairRestricted,
      Set.indicator_of_notMem hinput]

theorem aestronglyMeasurable_dirichletGeneralPairRestricted
    (dimension : ℕ) (parameters : Fin (dimension + 2) → ℝ) :
    AEStronglyMeasurable
      (dirichletGeneralPairRestricted dimension parameters)
      ((volume : Measure ℝ).prod
        (volume : Measure (Fin dimension → ℝ))) := by
  rw [dirichletGeneralPairRestricted,
    aestronglyMeasurable_indicator_iff
      (dirichletPairDomain_measurableSet dimension)]
  apply ContinuousOn.aestronglyMeasurable
  · apply (continuousOn_dirichletGeneralIntegrand
      (dimension + 1) parameters).comp
    · fun_prop
    · intro input hinput
      exact (finCons_mem_dirichletSimplex_iff dimension
        input.1 input.2).mpr hinput
  · exact dirichletPairDomain_measurableSet dimension

theorem dirichletGeneralPairRestricted_inner
    (dimension : ℕ) (parameters : Fin (dimension + 2) → ℝ)
    (first : ℝ) :
    (∫ tail : Fin dimension → ℝ,
      dirichletGeneralPairRestricted dimension parameters (first, tail)) =
      (Set.Ioo (0 : ℝ) 1).indicator
        (dirichletGeneralTailIntegral dimension parameters) first := by
  by_cases hfirst : first ∈ Set.Ioo (0 : ℝ) 1
  · rw [Set.indicator_of_mem hfirst]
    unfold dirichletGeneralPairRestricted
    unfold dirichletGeneralTailIntegral
    rw [← integral_indicator
      (dirichletTailFiber_measurableSet dimension first)]
    apply integral_congr_ae
    filter_upwards with tail
    by_cases htail : tail ∈ dirichletTailFiber dimension first
    · rw [Set.indicator_of_mem htail, Set.indicator_of_mem]
      exact ⟨hfirst.1, htail⟩
    · rw [Set.indicator_of_notMem htail,
        Set.indicator_of_notMem]
      intro hpair
      exact htail hpair.2
  · rw [Set.indicator_of_notMem hfirst]
    have hzero : (fun tail : Fin dimension → ℝ =>
        dirichletGeneralPairRestricted dimension parameters
          (first, tail)) = fun _ => 0 := by
      funext tail
      unfold dirichletGeneralPairRestricted
      rw [Set.indicator_of_notMem]
      intro hpair
      exact hfirst (dirichletPairDomain_first_mem hpair)
    rw [hzero]
    simp

theorem dirichletGeneralPairRestricted_inner_norm
    (dimension : ℕ) (parameters : Fin (dimension + 2) → ℝ)
    (first : ℝ) :
    (∫ tail : Fin dimension → ℝ,
      ‖dirichletGeneralPairRestricted dimension parameters
        (first, tail)‖) =
      (Set.Ioo (0 : ℝ) 1).indicator
        (dirichletGeneralTailIntegral dimension parameters) first := by
  rw [show (fun tail : Fin dimension → ℝ =>
      ‖dirichletGeneralPairRestricted dimension parameters
        (first, tail)‖) =
    fun tail => dirichletGeneralPairRestricted dimension parameters
      (first, tail) by
      funext tail
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact dirichletGeneralPairRestricted_nonneg
        dimension parameters (first, tail)]
  exact dirichletGeneralPairRestricted_inner
    dimension parameters first

theorem integrable_dirichletGeneralPairRestricted_section
    (dimension : ℕ) (parameters : Fin (dimension + 2) → ℝ)
    (first : ℝ)
    (hintegrable : IntegrableOn
      (dirichletGeneralIntegrand dimension (Fin.tail parameters))
      (dirichletOpenSimplex dimension)) :
    Integrable (fun tail : Fin dimension → ℝ =>
      dirichletGeneralPairRestricted dimension parameters
        (first, tail)) := by
  by_cases hfirst : first ∈ Set.Ioo (0 : ℝ) 1
  · have hfunction : (fun tail : Fin dimension → ℝ =>
        dirichletGeneralPairRestricted dimension parameters
          (first, tail)) =
      (dirichletTailFiber dimension first).indicator
        (fun tail => dirichletGeneralIntegrand
          (dimension + 1) parameters (Fin.cons first tail)) := by
      funext tail
      unfold dirichletGeneralPairRestricted
      by_cases htail : tail ∈ dirichletTailFiber dimension first
      · rw [Set.indicator_of_mem htail, Set.indicator_of_mem]
        exact ⟨hfirst.1, htail⟩
      · rw [Set.indicator_of_notMem htail,
          Set.indicator_of_notMem]
        intro hpair
        exact htail hpair.2
    rw [hfunction]
    exact IntegrableOn.integrable_indicator
      (integrableOn_dirichletGeneralTail
        dimension parameters hfirst hintegrable)
      (dirichletTailFiber_measurableSet dimension first)
  · have hzero : (fun tail : Fin dimension → ℝ =>
        dirichletGeneralPairRestricted dimension parameters
          (first, tail)) = fun _ => 0 := by
      funext tail
      unfold dirichletGeneralPairRestricted
      rw [Set.indicator_of_notMem]
      intro hpair
      exact hfirst (dirichletPairDomain_first_mem hpair)
    rw [hzero]
    exact integrable_zero (Fin dimension → ℝ) ℝ
      (volume : Measure (Fin dimension → ℝ))

theorem integrable_dirichletGeneralPairRestricted_outer_norm
    (dimension : ℕ) (parameters : Fin (dimension + 2) → ℝ)
    (hparameters : ∀ anchor, 0 < parameters anchor) :
    Integrable (fun first : ℝ =>
      ∫ tail : Fin dimension → ℝ,
        ‖dirichletGeneralPairRestricted dimension parameters
          (first, tail)‖) := by
  have hfunction : (fun first : ℝ =>
      ∫ tail : Fin dimension → ℝ,
        ‖dirichletGeneralPairRestricted dimension parameters
          (first, tail)‖) =
    (Set.Ioo (0 : ℝ) 1).indicator
      (fun first =>
        dirichletGeneralIntegral dimension (Fin.tail parameters) *
          dirichletGeneralOuterWeight dimension parameters first) := by
    funext first
    rw [dirichletGeneralPairRestricted_inner_norm]
    by_cases hfirst : first ∈ Set.Ioo (0 : ℝ) 1
    · rw [Set.indicator_of_mem hfirst, Set.indicator_of_mem hfirst,
        dirichletGeneralTailIntegral_eq dimension parameters hfirst]
      ring
    · rw [Set.indicator_of_notMem hfirst,
        Set.indicator_of_notMem hfirst]
  rw [hfunction]
  rw [integrable_indicator_iff measurableSet_Ioo]
  exact (integrableOn_dirichletGeneralOuterWeight
    dimension parameters hparameters).const_mul
      (dirichletGeneralIntegral dimension (Fin.tail parameters))

theorem integrable_dirichletGeneralPairRestricted
    (dimension : ℕ) (parameters : Fin (dimension + 2) → ℝ)
    (hparameters : ∀ anchor, 0 < parameters anchor)
    (hintegrable : IntegrableOn
      (dirichletGeneralIntegrand dimension (Fin.tail parameters))
      (dirichletOpenSimplex dimension)) :
    Integrable (dirichletGeneralPairRestricted dimension parameters)
      ((volume : Measure ℝ).prod
        (volume : Measure (Fin dimension → ℝ))) := by
  rw [integrable_prod_iff
    (aestronglyMeasurable_dirichletGeneralPairRestricted
      dimension parameters)]
  constructor
  · exact ae_of_all _ fun first =>
      integrable_dirichletGeneralPairRestricted_section
        dimension parameters first hintegrable
  · exact integrable_dirichletGeneralPairRestricted_outer_norm
      dimension parameters hparameters

theorem dirichletGeneralIntegral_eq_pair
    (dimension : ℕ) (parameters : Fin (dimension + 2) → ℝ) :
    dirichletGeneralIntegral (dimension + 1) parameters =
      ∫ input in dirichletPairDomain dimension,
        dirichletGeneralIntegrand (dimension + 1) parameters
          (Fin.cons input.1 input.2)
        ∂((volume : Measure ℝ).prod
          (volume : Measure (Fin dimension → ℝ))) := by
  unfold dirichletGeneralIntegral
  have hchange :=
    (volume_preserving_dirichletSplitFirst dimension).setIntegral_preimage_emb
      (dirichletSplitFirstEquiv dimension).measurableEmbedding
      (fun input : ℝ × (Fin dimension → ℝ) =>
        dirichletGeneralIntegrand (dimension + 1) parameters
          (Fin.cons input.1 input.2))
      (dirichletPairDomain dimension)
  rw [dirichletSplitFirst_preimage_domain] at hchange
  rw [← hchange]
  apply setIntegral_congr_fun
  · exact dirichletOpenSimplex_measurableSet (dimension + 1)
  · intro coordinates hcoordinates
    change dirichletGeneralIntegrand (dimension + 1) parameters coordinates =
      dirichletGeneralIntegrand (dimension + 1) parameters
        (Fin.cons ((dirichletSplitFirstEquiv dimension coordinates).1)
          ((dirichletSplitFirstEquiv dimension coordinates).2))
    rw [dirichletSplitFirstEquiv_apply]
    exact congrArg (dirichletGeneralIntegrand (dimension + 1) parameters)
      (Fin.cons_self_tail coordinates).symm

theorem dirichletGeneralIntegral_succ_recurrence
    (dimension : ℕ) (parameters : Fin (dimension + 2) → ℝ)
    (hparameters : ∀ anchor, 0 < parameters anchor)
    (hintegrable : IntegrableOn
      (dirichletGeneralIntegrand dimension (Fin.tail parameters))
      (dirichletOpenSimplex dimension)) :
    dirichletGeneralIntegral (dimension + 1) parameters =
      (Real.Gamma (parameters 0) *
        Real.Gamma (dirichletGeneralTailSum dimension parameters) /
          Real.Gamma (parameters 0 +
            dirichletGeneralTailSum dimension parameters)) *
        dirichletGeneralIntegral dimension (Fin.tail parameters) := by
  have hpair := integrable_dirichletGeneralPairRestricted
    dimension parameters hparameters hintegrable
  have hfubini := integral_prod
    (dirichletGeneralPairRestricted dimension parameters) hpair
  have hsetIntegral :
      (∫ input in dirichletPairDomain dimension,
        dirichletGeneralIntegrand (dimension + 1) parameters
          (Fin.cons input.1 input.2)
        ∂((volume : Measure ℝ).prod
          (volume : Measure (Fin dimension → ℝ)))) =
      ∫ input, dirichletGeneralPairRestricted dimension parameters input
        ∂((volume : Measure ℝ).prod
          (volume : Measure (Fin dimension → ℝ))) := by
    unfold dirichletGeneralPairRestricted
    rw [integral_indicator (dirichletPairDomain_measurableSet dimension)]
  have hleft : dirichletGeneralIntegral (dimension + 1) parameters =
      ∫ input, dirichletGeneralPairRestricted dimension parameters input
        ∂((volume : Measure ℝ).prod
          (volume : Measure (Fin dimension → ℝ))) :=
    (dirichletGeneralIntegral_eq_pair dimension parameters).trans
      hsetIntegral
  have houter :
      (∫ first : ℝ,
        (Set.Ioo (0 : ℝ) 1).indicator
          (dirichletGeneralTailIntegral dimension parameters) first) =
      (∫ first in Set.Ioo (0 : ℝ) 1,
        dirichletGeneralOuterWeight dimension parameters first) *
          dirichletGeneralIntegral dimension (Fin.tail parameters) := by
    rw [integral_indicator measurableSet_Ioo]
    rw [show (∫ first in Set.Ioo (0 : ℝ) 1,
        dirichletGeneralTailIntegral dimension parameters first) =
      ∫ first in Set.Ioo (0 : ℝ) 1,
        dirichletGeneralOuterWeight dimension parameters first *
          dirichletGeneralIntegral dimension (Fin.tail parameters) by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro first hfirst
      exact dirichletGeneralTailIntegral_eq
        dimension parameters hfirst]
    rw [integral_mul_const]
  have hbeta := integral_selbergHalfWeight_Ioo
    (hparameters 0)
    (dirichletGeneralTailSum_pos dimension parameters hparameters)
  rw [← dirichletGeneralOuterWeight_eq_selberg
    dimension parameters] at hbeta
  calc
    dirichletGeneralIntegral (dimension + 1) parameters =
        ∫ input, dirichletGeneralPairRestricted dimension parameters input
          ∂((volume : Measure ℝ).prod
            (volume : Measure (Fin dimension → ℝ))) := hleft
    _ = ∫ first : ℝ, ∫ tail : Fin dimension → ℝ,
          dirichletGeneralPairRestricted dimension parameters
            (first, tail) := hfubini
    _ = ∫ first : ℝ,
          (Set.Ioo (0 : ℝ) 1).indicator
            (dirichletGeneralTailIntegral dimension parameters) first := by
      apply integral_congr_ae
      filter_upwards with first
      exact dirichletGeneralPairRestricted_inner
        dimension parameters first
    _ = (∫ first in Set.Ioo (0 : ℝ) 1,
          dirichletGeneralOuterWeight dimension parameters first) *
            dirichletGeneralIntegral dimension
              (Fin.tail parameters) := houter
    _ = _ := by rw [hbeta]

theorem integrableOn_dirichletGeneralIntegrand_succ
    (dimension : ℕ) (parameters : Fin (dimension + 2) → ℝ)
    (hparameters : ∀ anchor, 0 < parameters anchor)
    (hintegrable : IntegrableOn
      (dirichletGeneralIntegrand dimension (Fin.tail parameters))
      (dirichletOpenSimplex dimension)) :
    IntegrableOn (dirichletGeneralIntegrand (dimension + 1) parameters)
      (dirichletOpenSimplex (dimension + 1)) := by
  let pairFunction : (ℝ × (Fin dimension → ℝ)) → ℝ := fun input =>
    dirichletGeneralIntegrand (dimension + 1) parameters
      (Fin.cons input.1 input.2)
  have hpair := integrable_dirichletGeneralPairRestricted
    dimension parameters hparameters hintegrable
  have hpairOn : IntegrableOn pairFunction (dirichletPairDomain dimension)
      ((volume : Measure ℝ).prod
        (volume : Measure (Fin dimension → ℝ))) := by
    rw [← integrable_indicator_iff
      (dirichletPairDomain_measurableSet dimension)]
    change Integrable
      (dirichletGeneralPairRestricted dimension parameters)
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
      dirichletGeneralIntegrand (dimension + 1) parameters coordinates
    rw [dirichletSplitFirstEquiv_apply]
    dsimp only [pairFunction]
    exact congrArg (dirichletGeneralIntegrand (dimension + 1) parameters)
      (Fin.cons_self_tail coordinates)
  · exact dirichletOpenSimplex_measurableSet (dimension + 1)

theorem integrableOn_dirichletGeneralIntegrand_all (dimension : ℕ) :
    ∀ (parameters : Fin (dimension + 1) → ℝ),
      (∀ anchor, 0 < parameters anchor) →
      IntegrableOn (dirichletGeneralIntegrand dimension parameters)
        (dirichletOpenSimplex dimension) := by
  induction dimension with
  | zero =>
      intro parameters hparameters
      rw [dirichletOpenSimplex_zero, dirichletGeneralIntegrand_zero]
      rw [IntegrableOn, Measure.restrict_univ]
      change Integrable (fun _ : Fin 0 → ℝ => (1 : ℝ)) volume
      rw [integrable_const_iff]
      right
      have hvolume : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
        rw [Measure.volume_pi_eq_dirac (fun row : Fin 0 => Fin.elim0 row)]
        simp
      exact ⟨by simp [hvolume]⟩
  | succ dimension ih =>
      intro parameters hparameters
      apply integrableOn_dirichletGeneralIntegrand_succ
        dimension parameters hparameters
      exact ih (Fin.tail parameters) fun anchor =>
        hparameters anchor.succ

theorem expectedDirichletGeneralIntegral_succ
    (dimension : ℕ) (parameters : Fin (dimension + 2) → ℝ)
    (hparameters : ∀ anchor, 0 < parameters anchor) :
    expectedDirichletGeneralIntegral (dimension + 1) parameters =
      (Real.Gamma (parameters 0) *
        Real.Gamma (dirichletGeneralTailSum dimension parameters) /
          Real.Gamma (parameters 0 +
            dirichletGeneralTailSum dimension parameters)) *
        expectedDirichletGeneralIntegral dimension
          (Fin.tail parameters) := by
  unfold expectedDirichletGeneralIntegral
  rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
  change
    (Real.Gamma (parameters 0) *
        ∏ anchor : Fin (dimension + 1),
          Real.Gamma ((Fin.tail parameters) anchor)) /
      Real.Gamma (parameters 0 +
        dirichletGeneralTailSum dimension parameters) = _
  have htailGamma :
      Real.Gamma (dirichletGeneralTailSum dimension parameters) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos
      (dirichletGeneralTailSum_pos
        dimension parameters hparameters)).ne'
  have htailSum :
      (∑ anchor : Fin (dimension + 1),
        (Fin.tail parameters) anchor) =
      dirichletGeneralTailSum dimension parameters := by
    rfl
  rw [htailSum]
  field_simp [htailGamma]

theorem dirichletGeneralEvaluation_all (dimension : ℕ) :
    ∀ (parameters : Fin (dimension + 1) → ℝ),
      (∀ anchor, 0 < parameters anchor) →
      DirichletGeneralEvaluation dimension parameters := by
  induction dimension with
  | zero =>
      intro parameters hparameters
      exact dirichletGeneralEvaluation_zero parameters (hparameters 0)
  | succ dimension ih =>
      intro parameters hparameters
      unfold DirichletGeneralEvaluation
      rw [dirichletGeneralIntegral_succ_recurrence
        dimension parameters hparameters
        (integrableOn_dirichletGeneralIntegrand_all dimension
          (Fin.tail parameters) fun anchor => hparameters anchor.succ)]
      rw [ih (Fin.tail parameters)
        (fun anchor => hparameters anchor.succ)]
      exact (expectedDirichletGeneralIntegral_succ
        dimension parameters hparameters).symm

end FibonacciRibbonKernel
