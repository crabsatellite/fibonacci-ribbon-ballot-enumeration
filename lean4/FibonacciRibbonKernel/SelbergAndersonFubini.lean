import FibonacciRibbonKernel.SelbergAndersonJoint
import Mathlib.MeasureTheory.Integral.Prod

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped Classical BigOperators

def selbergAndersonJointDomain (rank : ℕ) :
    Set ((Fin (rank + 1) → ℝ) × (Fin (rank + 2) → ℝ)) :=
  {input |
    input.1 ∈ strictOrderedSelbergDomain (rank + 1) ∧
      DixonAndersonInterlacing
        (selbergExtendedAnchors rank input.1) input.2}

noncomputable def selbergAndersonJointRestricted (rank : ℕ)
    (alpha beta : ℝ) :
    ((Fin (rank + 1) → ℝ) × (Fin (rank + 2) → ℝ)) → ℝ :=
  (selbergAndersonJointDomain rank).indicator fun input =>
    selbergAndersonJointIntegrand rank alpha beta input.2 input.1

theorem continuous_selbergExtendedAnchors_coordinate
    (rank : ℕ) (anchor : Fin (rank + 3)) :
    Continuous (fun roots : Fin (rank + 1) → ℝ =>
      selbergExtendedAnchors rank roots anchor) := by
  cases anchor using Fin.cases with
  | zero => simpa using (continuous_const : Continuous
      (fun _ : Fin (rank + 1) → ℝ => (1 : ℝ)))
  | succ anchor =>
      cases anchor using Fin.lastCases with
      | last => simpa using (continuous_const : Continuous
          (fun _ : Fin (rank + 1) → ℝ => (0 : ℝ)))
      | cast index =>
          simp only [selbergExtendedAnchors_root]
          exact continuous_apply index

theorem selbergAndersonJointDomain_measurableSet (rank : ℕ) :
    MeasurableSet (selbergAndersonJointDomain rank) := by
  have hrepresentation : selbergAndersonJointDomain rank =
      {input : (Fin (rank + 1) → ℝ) × (Fin (rank + 2) → ℝ) |
        input.1 ∈ strictOrderedSelbergDomain (rank + 1)} ∩
      ⋂ index : Fin (rank + 2),
        ({input |
            input.2 index <
              selbergExtendedAnchors rank input.1 index.castSucc} ∩
          {input |
            selbergExtendedAnchors rank input.1 index.succ <
              input.2 index}) := by
    ext input
    simp [selbergAndersonJointDomain,
      DixonAndersonInterlacing]
  rw [hrepresentation]
  apply MeasurableSet.inter
  · exact (strictOrderedSelbergDomain_measurableSet (rank + 1)).preimage
      measurable_fst
  · apply MeasurableSet.iInter
    intro index
    apply MeasurableSet.inter
    · exact measurableSet_lt
        ((measurable_pi_apply index).comp measurable_snd)
        ((continuous_selbergExtendedAnchors_coordinate
          rank index.castSucc).measurable.comp measurable_fst)
    · exact measurableSet_lt
        ((continuous_selbergExtendedAnchors_coordinate
          rank index.succ).measurable.comp measurable_fst)
        ((measurable_pi_apply index).comp measurable_snd)

theorem continuousOn_selbergAndersonJointIntegrand
    (rank : ℕ) (alpha beta : ℝ) :
    ContinuousOn
      (fun input : (Fin (rank + 1) → ℝ) × (Fin (rank + 2) → ℝ) =>
        selbergAndersonJointIntegrand rank alpha beta input.2 input.1)
      (selbergAndersonJointDomain rank) := by
  unfold selbergAndersonJointIntegrand
  apply ContinuousOn.mul
  · exact ((continuous_standardMehtaVandermonde (rank + 1)).comp
      continuous_fst).continuousOn
  · unfold dixonAndersonGeneralIntegrand
    apply ContinuousOn.mul
    · apply continuousOn_finsetProd Finset.univ
      intro first hfirst
      apply continuousOn_finsetProd (Finset.Ioi first)
      intro next hnext
      fun_prop
    · unfold dixonAndersonGeneralCrossProduct
      apply continuousOn_finsetProd Finset.univ
      intro upperIndex hupperIndex
      apply continuousOn_finsetProd Finset.univ
      intro anchor hanchor
      apply continuousOn_of_forall_continuousAt
      intro input hinput
      have hanchors := selbergExtendedAnchors_strictAnti
        rank input.1 hinput.1
      have hne := anchor_sub_root_ne_zero_of_interlacing
        hanchors hinput.2 anchor upperIndex
      have hcontinuous : ContinuousAt
          (fun current :
              (Fin (rank + 1) → ℝ) × (Fin (rank + 2) → ℝ) =>
            |current.2 upperIndex -
              selbergExtendedAnchors rank current.1 anchor|) input := by
        have hupper : Continuous
            (fun current :
                (Fin (rank + 1) → ℝ) × (Fin (rank + 2) → ℝ) =>
              current.2 upperIndex) :=
          (continuous_apply upperIndex).comp continuous_snd
        have hlower : Continuous
            (fun current :
                (Fin (rank + 1) → ℝ) × (Fin (rank + 2) → ℝ) =>
              selbergExtendedAnchors rank current.1 anchor) :=
          (continuous_selbergExtendedAnchors_coordinate rank anchor).comp
            continuous_fst
        exact (hupper.sub hlower).abs.continuousAt
      apply hcontinuous.rpow_const
      left
      rw [abs_ne_zero]
      exact sub_ne_zero.mpr (sub_ne_zero.mp hne).symm

theorem aestronglyMeasurable_selbergAndersonJointRestricted
    (rank : ℕ) (alpha beta : ℝ) :
    AEStronglyMeasurable
      (selbergAndersonJointRestricted rank alpha beta)
      ((volume : Measure (Fin (rank + 1) → ℝ)).prod
        (volume : Measure (Fin (rank + 2) → ℝ))) := by
  rw [selbergAndersonJointRestricted,
    aestronglyMeasurable_indicator_iff
      (selbergAndersonJointDomain_measurableSet rank)]
  exact (continuousOn_selbergAndersonJointIntegrand rank alpha beta).aestronglyMeasurable
    (selbergAndersonJointDomain_measurableSet rank)

theorem selbergHalfIntegrand_pos_of_strict
    {dimension : ℕ} {alpha beta : ℝ}
    (_halpha : 0 < alpha) (_hbeta : 0 < beta)
    {coordinates : Fin dimension → ℝ}
    (hcoordinates : coordinates ∈ strictOrderedSelbergDomain dimension) :
    0 < selbergHalfIntegrand dimension alpha beta coordinates := by
  unfold selbergHalfIntegrand selbergHalfWeight
  apply mul_pos
  · apply Finset.prod_pos
    intro index hindex
    exact mul_pos
      (Real.rpow_pos_of_pos (hcoordinates.1 index (Set.mem_univ _)).1 _)
      (Real.rpow_pos_of_pos
        (sub_pos.mpr (hcoordinates.1 index (Set.mem_univ _)).2) _)
  · rw [standardMehtaVandermonde_eq_ordered_of_strictAnti
      coordinates hcoordinates.2]
    apply Finset.prod_pos
    intro first hfirst
    apply Finset.prod_pos
    intro next hnext
    exact sub_pos.mpr (hcoordinates.2 (Finset.mem_Ioi.mp hnext))

theorem dixonAndersonHalfIntegrand_pos_of_interlacing
    {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ)
    (hanchors : StrictAnti anchors)
    (hinterlace : DixonAndersonInterlacing anchors roots) :
    0 < dixonAndersonHalfIntegrand dimension anchors roots := by
  unfold dixonAndersonHalfIntegrand
  apply mul_pos
  · have hroots := roots_strictAnti_of_interlacing hanchors hinterlace
    apply Finset.prod_pos
    intro first hfirst
    apply Finset.prod_pos
    intro next hnext
    exact sub_pos.mpr (hroots (Finset.mem_Ioi.mp hnext))
  · apply Finset.prod_pos
    intro root hroot
    apply Finset.prod_pos
    intro anchor hanchor
    apply Real.rpow_pos_of_pos
    rw [abs_pos]
    exact sub_ne_zero.mpr
      (sub_ne_zero.mp (anchor_sub_root_ne_zero_of_interlacing
        hanchors hinterlace anchor root)).symm

theorem selbergAndersonJointRestricted_nonneg
    (rank : ℕ) {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (input : (Fin (rank + 1) → ℝ) × (Fin (rank + 2) → ℝ)) :
    0 ≤ selbergAndersonJointRestricted rank alpha beta input := by
  by_cases hinput : input ∈ selbergAndersonJointDomain rank
  · rw [selbergAndersonJointRestricted, Set.indicator_of_mem hinput]
    have hiff := (selbergJointDomain_iff rank input.2 input.1).mpr hinput
    rw [selbergAndersonJointIntegrand_eq_upper_first
      rank alpha beta input.2 input.1 hiff.1 hiff.2]
    exact (mul_pos
      (selbergHalfIntegrand_pos_of_strict halpha hbeta hiff.1)
      (dixonAndersonHalfIntegrand_pos_of_interlacing
        input.2 input.1 hiff.1.2 hiff.2)).le
  · rw [selbergAndersonJointRestricted,
      Set.indicator_of_notMem hinput]

theorem integrable_selbergAndersonJointRestricted_section
    (rank : ℕ) {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (lower : Fin (rank + 1) → ℝ) :
    Integrable (fun upper : Fin (rank + 2) → ℝ =>
      selbergAndersonJointRestricted rank alpha beta (lower, upper)) := by
  by_cases hlower : lower ∈ strictOrderedSelbergDomain (rank + 1)
  · have hfunction : (fun upper : Fin (rank + 2) → ℝ =>
        selbergAndersonJointRestricted rank alpha beta (lower, upper)) =
      (dixonAndersonDomain (rank + 2)
        (selbergExtendedAnchors rank lower)).indicator
        (fun upper => selbergAndersonJointIntegrand
          rank alpha beta upper lower) := by
      funext upper
      unfold selbergAndersonJointRestricted
      by_cases hinterlace : DixonAndersonInterlacing
          (selbergExtendedAnchors rank lower) upper
      · rw [Set.indicator_of_mem, Set.indicator_of_mem hinterlace]
        exact ⟨hlower, hinterlace⟩
      · rw [Set.indicator_of_notMem, Set.indicator_of_notMem hinterlace]
        intro hjoint
        exact hinterlace hjoint.2
    rw [hfunction]
    apply IntegrableOn.integrable_indicator
    · unfold selbergAndersonJointIntegrand
      exact (integrableOn_dixonAndersonGeneralIntegrand
        (selbergExtendedAnchors rank lower)
        (selbergAndersonParameters rank alpha beta)
        (selbergExtendedAnchors_strictAnti rank lower hlower)
        (selbergAndersonParameters_pos rank halpha hbeta)).const_mul
          (standardMehtaVandermonde (rank + 1) lower)
    · exact dixonAndersonDomain_measurableSet
        (selbergExtendedAnchors rank lower)
  · have hzero : (fun upper : Fin (rank + 2) → ℝ =>
        selbergAndersonJointRestricted rank alpha beta (lower, upper)) =
        fun _ => 0 := by
      funext upper
      unfold selbergAndersonJointRestricted
      rw [Set.indicator_of_notMem]
      intro hjoint
      exact hlower hjoint.1
    rw [hzero]
    exact integrable_zero _ _ _

theorem selbergAndersonJointRestricted_inner_norm
    (rank : ℕ) {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (lower : Fin (rank + 1) → ℝ) :
    (∫ upper : Fin (rank + 2) → ℝ,
      ‖selbergAndersonJointRestricted rank alpha beta (lower, upper)‖) =
      (strictOrderedSelbergDomain (rank + 1)).indicator
        (fun current => selbergAndersonCoefficient rank alpha beta *
          selbergHalfIntegrand (rank + 1)
            (alpha + 1 / 2) (beta + 1 / 2) current) lower := by
  rw [show (fun upper : Fin (rank + 2) → ℝ =>
      ‖selbergAndersonJointRestricted rank alpha beta (lower, upper)‖) =
    fun upper => selbergAndersonJointRestricted rank alpha beta
      (lower, upper) by
      funext upper
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact selbergAndersonJointRestricted_nonneg
        rank halpha hbeta (lower, upper)]
  by_cases hlower : lower ∈ strictOrderedSelbergDomain (rank + 1)
  · rw [Set.indicator_of_mem hlower]
    have hfunction : (fun upper : Fin (rank + 2) → ℝ =>
        selbergAndersonJointRestricted rank alpha beta (lower, upper)) =
      (dixonAndersonDomain (rank + 2)
        (selbergExtendedAnchors rank lower)).indicator
        (fun upper => selbergAndersonJointIntegrand
          rank alpha beta upper lower) := by
      funext upper
      unfold selbergAndersonJointRestricted
      by_cases hinterlace : DixonAndersonInterlacing
          (selbergExtendedAnchors rank lower) upper
      · rw [Set.indicator_of_mem, Set.indicator_of_mem hinterlace]
        exact ⟨hlower, hinterlace⟩
      · rw [Set.indicator_of_notMem, Set.indicator_of_notMem hinterlace]
        intro hjoint
        exact hinterlace hjoint.2
    rw [hfunction]
    rw [integral_indicator
      (dixonAndersonDomain_measurableSet
        (selbergExtendedAnchors rank lower))]
    exact selbergAndersonJointIntegral_upper_section
      rank halpha hbeta lower hlower
  · rw [Set.indicator_of_notMem hlower]
    have hzero : (fun upper : Fin (rank + 2) → ℝ =>
        selbergAndersonJointRestricted rank alpha beta (lower, upper)) =
        fun _ => 0 := by
      funext upper
      unfold selbergAndersonJointRestricted
      rw [Set.indicator_of_notMem]
      intro hjoint
      exact hlower hjoint.1
    rw [hzero]
    simp

theorem integrable_selbergAndersonJointRestricted_outer_norm
    (rank : ℕ) {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hintegrable : IntegrableOn
      (selbergHalfIntegrand (rank + 1)
        (alpha + 1 / 2) (beta + 1 / 2))
      (strictOrderedSelbergDomain (rank + 1))) :
    Integrable (fun lower : Fin (rank + 1) → ℝ =>
      ∫ upper : Fin (rank + 2) → ℝ,
        ‖selbergAndersonJointRestricted rank alpha beta
          (lower, upper)‖) := by
  rw [show (fun lower : Fin (rank + 1) → ℝ =>
      ∫ upper : Fin (rank + 2) → ℝ,
        ‖selbergAndersonJointRestricted rank alpha beta
          (lower, upper)‖) =
    (strictOrderedSelbergDomain (rank + 1)).indicator
      (fun lower => selbergAndersonCoefficient rank alpha beta *
        selbergHalfIntegrand (rank + 1)
          (alpha + 1 / 2) (beta + 1 / 2) lower) by
      funext lower
      exact selbergAndersonJointRestricted_inner_norm
        rank halpha hbeta lower]
  exact IntegrableOn.integrable_indicator
    (hintegrable.const_mul (selbergAndersonCoefficient rank alpha beta))
    (strictOrderedSelbergDomain_measurableSet (rank + 1))

theorem integrable_selbergAndersonJointRestricted
    (rank : ℕ) {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hintegrable : IntegrableOn
      (selbergHalfIntegrand (rank + 1)
        (alpha + 1 / 2) (beta + 1 / 2))
      (strictOrderedSelbergDomain (rank + 1))) :
    Integrable (selbergAndersonJointRestricted rank alpha beta)
      ((volume : Measure (Fin (rank + 1) → ℝ)).prod
        (volume : Measure (Fin (rank + 2) → ℝ))) := by
  rw [integrable_prod_iff
    (aestronglyMeasurable_selbergAndersonJointRestricted
      rank alpha beta)]
  constructor
  · exact ae_of_all _ fun lower =>
      integrable_selbergAndersonJointRestricted_section
        rank halpha hbeta lower
  · exact integrable_selbergAndersonJointRestricted_outer_norm
      rank halpha hbeta hintegrable

theorem selbergAndersonJointRestricted_inner
    (rank : ℕ) {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (lower : Fin (rank + 1) → ℝ) :
    (∫ upper : Fin (rank + 2) → ℝ,
      selbergAndersonJointRestricted rank alpha beta (lower, upper)) =
      (strictOrderedSelbergDomain (rank + 1)).indicator
        (fun current => selbergAndersonCoefficient rank alpha beta *
          selbergHalfIntegrand (rank + 1)
            (alpha + 1 / 2) (beta + 1 / 2) current) lower := by
  rw [← selbergAndersonJointRestricted_inner_norm
    rank halpha hbeta lower]
  apply integral_congr_ae
  filter_upwards with upper
  rw [Real.norm_eq_abs, abs_of_nonneg]
  exact selbergAndersonJointRestricted_nonneg
    rank halpha hbeta (lower, upper)

theorem selbergAndersonJointRestricted_lower_integral
    (rank : ℕ) {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) :
    (∫ lower : Fin (rank + 1) → ℝ,
      ∫ upper : Fin (rank + 2) → ℝ,
        selbergAndersonJointRestricted rank alpha beta (lower, upper)) =
      selbergAndersonCoefficient rank alpha beta *
        (∫ lower in strictOrderedSelbergDomain (rank + 1),
          selbergHalfIntegrand (rank + 1)
            (alpha + 1 / 2) (beta + 1 / 2) lower) := by
  rw [show (fun lower : Fin (rank + 1) → ℝ =>
      ∫ upper : Fin (rank + 2) → ℝ,
        selbergAndersonJointRestricted rank alpha beta (lower, upper)) =
    (strictOrderedSelbergDomain (rank + 1)).indicator
      (fun lower => selbergAndersonCoefficient rank alpha beta *
        selbergHalfIntegrand (rank + 1)
          (alpha + 1 / 2) (beta + 1 / 2) lower) by
      funext lower
      exact selbergAndersonJointRestricted_inner
        rank halpha hbeta lower]
  rw [integral_indicator
    (strictOrderedSelbergDomain_measurableSet (rank + 1))]
  rw [integral_const_mul]

theorem selbergAndersonJointRestricted_upper_section
    (rank : ℕ) {alpha beta : ℝ}
    (_halpha : 0 < alpha) (_hbeta : 0 < beta)
    (upper : Fin (rank + 2) → ℝ) :
    (∫ lower : Fin (rank + 1) → ℝ,
      selbergAndersonJointRestricted rank alpha beta (lower, upper)) =
      (strictOrderedSelbergDomain (rank + 2)).indicator
        (fun current =>
          expectedDixonAndersonHalfIntegral (rank + 1) *
            selbergHalfIntegrand (rank + 2) alpha beta current) upper := by
  by_cases hupper : upper ∈ strictOrderedSelbergDomain (rank + 2)
  · rw [Set.indicator_of_mem hupper]
    have hfunction : (fun lower : Fin (rank + 1) → ℝ =>
        selbergAndersonJointRestricted rank alpha beta (lower, upper)) =
      (dixonAndersonDomain (rank + 1) upper).indicator
        (fun lower => selbergAndersonJointIntegrand
          rank alpha beta upper lower) := by
      funext lower
      unfold selbergAndersonJointRestricted
      by_cases hinterlace : DixonAndersonInterlacing upper lower
      · have hjoint := (selbergJointDomain_iff rank upper lower).mp
          ⟨hupper, hinterlace⟩
        have hjointMem : (lower, upper) ∈
            selbergAndersonJointDomain rank := by
          exact hjoint
        rw [Set.indicator_of_mem hjointMem,
          Set.indicator_of_mem hinterlace]
      · rw [Set.indicator_of_notMem,
          Set.indicator_of_notMem hinterlace]
        intro hjoint
        exact hinterlace
          ((selbergJointDomain_iff rank upper lower).mpr hjoint).2
    rw [hfunction]
    rw [integral_indicator (dixonAndersonDomain_measurableSet upper)]
    rw [show (∫ lower in dixonAndersonDomain (rank + 1) upper,
        selbergAndersonJointIntegrand rank alpha beta upper lower) =
      ∫ lower in dixonAndersonDomain (rank + 1) upper,
        selbergHalfIntegrand (rank + 2) alpha beta upper *
          dixonAndersonHalfIntegrand (rank + 1) upper lower by
      apply setIntegral_congr_fun (dixonAndersonDomain_measurableSet upper)
      intro lower hinterlace
      exact selbergAndersonJointIntegrand_eq_upper_first
        rank alpha beta upper lower hupper hinterlace]
    rw [integral_const_mul]
    have hevaluation := dixonAndersonHalfEvaluation_all (rank + 1)
    unfold DixonAndersonHalfEvaluation at hevaluation
    change selbergHalfIntegrand (rank + 2) alpha beta upper *
        dixonAndersonHalfIntegral (rank + 1) upper = _
    rw [hevaluation upper hupper.2]
    ring
  · rw [Set.indicator_of_notMem hupper]
    have hzero : (fun lower : Fin (rank + 1) → ℝ =>
        selbergAndersonJointRestricted rank alpha beta (lower, upper)) =
        fun _ => 0 := by
      funext lower
      unfold selbergAndersonJointRestricted
      rw [Set.indicator_of_notMem]
      intro hjoint
      exact hupper ((selbergJointDomain_iff rank upper lower).mpr hjoint).1
    rw [hzero]
    simp

theorem selbergAndersonJointRestricted_upper_section_norm
    (rank : ℕ) {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (upper : Fin (rank + 2) → ℝ) :
    (∫ lower : Fin (rank + 1) → ℝ,
      ‖selbergAndersonJointRestricted rank alpha beta (lower, upper)‖) =
      (strictOrderedSelbergDomain (rank + 2)).indicator
        (fun current =>
          expectedDixonAndersonHalfIntegral (rank + 1) *
            selbergHalfIntegrand (rank + 2) alpha beta current) upper := by
  rw [show (fun lower : Fin (rank + 1) → ℝ =>
      ‖selbergAndersonJointRestricted rank alpha beta (lower, upper)‖) =
    fun lower => selbergAndersonJointRestricted rank alpha beta
      (lower, upper) by
      funext lower
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact selbergAndersonJointRestricted_nonneg
        rank halpha hbeta (lower, upper)]
  exact selbergAndersonJointRestricted_upper_section
    rank halpha hbeta upper

theorem selbergAndersonJointRestricted_upper_integral
    (rank : ℕ) {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) :
    (∫ upper : Fin (rank + 2) → ℝ,
      ∫ lower : Fin (rank + 1) → ℝ,
        selbergAndersonJointRestricted rank alpha beta (lower, upper)) =
      expectedDixonAndersonHalfIntegral (rank + 1) *
        (∫ upper in strictOrderedSelbergDomain (rank + 2),
          selbergHalfIntegrand (rank + 2) alpha beta upper) := by
  rw [show (fun upper : Fin (rank + 2) → ℝ =>
      ∫ lower : Fin (rank + 1) → ℝ,
        selbergAndersonJointRestricted rank alpha beta (lower, upper)) =
    (strictOrderedSelbergDomain (rank + 2)).indicator
      (fun upper => expectedDixonAndersonHalfIntegral (rank + 1) *
        selbergHalfIntegrand (rank + 2) alpha beta upper) by
      funext upper
      exact selbergAndersonJointRestricted_upper_section
        rank halpha hbeta upper]
  rw [integral_indicator
    (strictOrderedSelbergDomain_measurableSet (rank + 2))]
  rw [integral_const_mul]

theorem expectedDixonAndersonHalfIntegral_pos (dimension : ℕ) :
    0 < expectedDixonAndersonHalfIntegral dimension := by
  unfold expectedDixonAndersonHalfIntegral
  positivity

theorem integrableOn_selbergHalfIntegrand_succ
    (rank : ℕ) {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hintegrable : IntegrableOn
      (selbergHalfIntegrand (rank + 1)
        (alpha + 1 / 2) (beta + 1 / 2))
      (strictOrderedSelbergDomain (rank + 1))) :
    IntegrableOn (selbergHalfIntegrand (rank + 2) alpha beta)
      (strictOrderedSelbergDomain (rank + 2)) := by
  have hjoint := integrable_selbergAndersonJointRestricted
    rank halpha hbeta hintegrable
  have houter := hjoint.integral_norm_prod_right
  have hscaled : Integrable
      ((strictOrderedSelbergDomain (rank + 2)).indicator
        (fun upper => expectedDixonAndersonHalfIntegral (rank + 1) *
          selbergHalfIntegrand (rank + 2) alpha beta upper)) := by
    rw [← show (fun upper : Fin (rank + 2) → ℝ =>
        ∫ lower : Fin (rank + 1) → ℝ,
          ‖selbergAndersonJointRestricted rank alpha beta
            (lower, upper)‖) =
      (strictOrderedSelbergDomain (rank + 2)).indicator
        (fun upper => expectedDixonAndersonHalfIntegral (rank + 1) *
          selbergHalfIntegrand (rank + 2) alpha beta upper) by
        funext upper
        exact selbergAndersonJointRestricted_upper_section_norm
          rank halpha hbeta upper]
    exact houter
  let coefficient := expectedDixonAndersonHalfIntegral (rank + 1)
  have hcoefficient : coefficient ≠ 0 :=
    (expectedDixonAndersonHalfIntegral_pos (rank + 1)).ne'
  have hunscaled := hscaled.const_mul coefficient⁻¹
  have hfunction : (fun upper : Fin (rank + 2) → ℝ =>
      coefficient⁻¹ *
        (strictOrderedSelbergDomain (rank + 2)).indicator
          (fun current => coefficient *
            selbergHalfIntegrand (rank + 2) alpha beta current) upper) =
      (strictOrderedSelbergDomain (rank + 2)).indicator
        (selbergHalfIntegrand (rank + 2) alpha beta) := by
    funext upper
    by_cases hupper : upper ∈ strictOrderedSelbergDomain (rank + 2)
    · rw [Set.indicator_of_mem hupper, Set.indicator_of_mem hupper]
      field_simp [hcoefficient]
    · rw [Set.indicator_of_notMem hupper,
        Set.indicator_of_notMem hupper]
      ring
  change Integrable (fun upper : Fin (rank + 2) → ℝ =>
    coefficient⁻¹ *
      (strictOrderedSelbergDomain (rank + 2)).indicator
        (fun current => coefficient *
          selbergHalfIntegrand (rank + 2) alpha beta current) upper) at hunscaled
  rw [hfunction] at hunscaled
  rw [← integrable_indicator_iff
    (strictOrderedSelbergDomain_measurableSet (rank + 2))]
  exact hunscaled

theorem selbergAnderson_balance
    (rank : ℕ) {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hintegrable : IntegrableOn
      (selbergHalfIntegrand (rank + 1)
        (alpha + 1 / 2) (beta + 1 / 2))
      (strictOrderedSelbergDomain (rank + 1))) :
    expectedDixonAndersonHalfIntegral (rank + 1) *
        (∫ upper in strictOrderedSelbergDomain (rank + 2),
          selbergHalfIntegrand (rank + 2) alpha beta upper) =
      selbergAndersonCoefficient rank alpha beta *
        (∫ lower in strictOrderedSelbergDomain (rank + 1),
          selbergHalfIntegrand (rank + 1)
            (alpha + 1 / 2) (beta + 1 / 2) lower) := by
  have hjoint := integrable_selbergAndersonJointRestricted
    rank halpha hbeta hintegrable
  have hleft := integral_prod
    (selbergAndersonJointRestricted rank alpha beta) hjoint
  have hright := integral_prod_symm
    (selbergAndersonJointRestricted rank alpha beta) hjoint
  have hiterated :
      (∫ lower : Fin (rank + 1) → ℝ,
        ∫ upper : Fin (rank + 2) → ℝ,
          selbergAndersonJointRestricted rank alpha beta (lower, upper)) =
      ∫ upper : Fin (rank + 2) → ℝ,
        ∫ lower : Fin (rank + 1) → ℝ,
          selbergAndersonJointRestricted rank alpha beta
            (lower, upper) := hleft.symm.trans hright
  rw [selbergAndersonJointRestricted_lower_integral
      rank halpha hbeta,
    selbergAndersonJointRestricted_upper_integral
      rank halpha hbeta] at hiterated
  exact hiterated.symm

theorem orderedSelbergHalfIntegral_succ_recurrence
    (rank : ℕ) {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hintegrable : IntegrableOn
      (selbergHalfIntegrand (rank + 1)
        (alpha + 1 / 2) (beta + 1 / 2))
      (strictOrderedSelbergDomain (rank + 1))) :
    orderedSelbergHalfIntegral (rank + 2) alpha beta =
      (selbergAndersonCoefficient rank alpha beta /
        expectedDixonAndersonHalfIntegral (rank + 1)) *
        orderedSelbergHalfIntegral (rank + 1)
          (alpha + 1 / 2) (beta + 1 / 2) := by
  have hbalance := selbergAnderson_balance
    rank halpha hbeta hintegrable
  rw [← orderedSelbergHalfIntegral_eq_strict
      (rank + 2) alpha beta,
    ← orderedSelbergHalfIntegral_eq_strict
      (rank + 1) (alpha + 1 / 2) (beta + 1 / 2)] at hbalance
  have hnonzero : expectedDixonAndersonHalfIntegral (rank + 1) ≠ 0 :=
    (expectedDixonAndersonHalfIntegral_pos (rank + 1)).ne'
  field_simp [hnonzero]
  convert hbalance using 1 <;> ring

theorem strictOrderedSelbergDomain_one :
    strictOrderedSelbergDomain 1 =
      (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Set.Ioo 0 1 := by
  ext coordinates
  simp only [strictOrderedSelbergDomain, Set.mem_inter_iff,
    strictMehtaChamber, Set.mem_setOf_eq, Set.mem_preimage,
    MeasurableEquiv.funUnique_apply]
  constructor
  · intro h
    change coordinates default ∈ Set.Ioo (0 : ℝ) 1
    rw [Fin.eq_zero default]
    exact h.1 0 (Set.mem_univ 0)
  · intro h
    constructor
    · intro index hindex
      change coordinates default ∈ Set.Ioo (0 : ℝ) 1 at h
      rw [Fin.eq_zero default] at h
      rw [Fin.eq_zero index]
      exact h
    · intro first next hlt
      rw [Fin.eq_zero first, Fin.eq_zero next] at hlt
      exact (lt_irrefl 0 hlt).elim

theorem integrableOn_selbergHalfIntegrand_one
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    IntegrableOn (selbergHalfIntegrand 1 alpha beta)
      (strictOrderedSelbergDomain 1) := by
  rw [strictOrderedSelbergDomain_one]
  have htransport :=
    ((volume_preserving_funUnique (Fin 1) ℝ).integrableOn_comp_preimage
      (MeasurableEquiv.measurableEmbedding
        (MeasurableEquiv.funUnique (Fin 1) ℝ))).mpr
      (integrableOn_selbergHalfWeight_Ioo halpha hbeta)
  apply IntegrableOn.congr_fun htransport
  · intro coordinates hcoordinates
    change selbergHalfWeight alpha beta (coordinates 0) =
      selbergHalfIntegrand 1 alpha beta coordinates
    exact (selbergHalfIntegrand_one alpha beta coordinates).symm
  · exact (MeasurableEquiv.measurableEmbedding
      (MeasurableEquiv.funUnique (Fin 1) ℝ)).measurable measurableSet_Ioo

theorem integrableOn_selbergHalfIntegrand_all (dimension : ℕ) :
    ∀ {alpha beta : ℝ}, 0 < alpha → 0 < beta →
      IntegrableOn (selbergHalfIntegrand dimension alpha beta)
        (strictOrderedSelbergDomain dimension) := by
  induction dimension with
  | zero =>
      intro alpha beta halpha hbeta
      have hdomain : strictOrderedSelbergDomain 0 = Set.univ := by
        ext coordinates
        simp only [strictOrderedSelbergDomain, Set.mem_inter_iff,
          strictMehtaChamber, Set.mem_setOf_eq, Set.mem_univ,
          iff_true]
        constructor
        · intro index hindex
          exact Fin.elim0 index
        · intro first
          exact Fin.elim0 first
      rw [hdomain]
      rw [selbergHalfIntegrand_zero, IntegrableOn,
        Measure.restrict_univ]
      change Integrable (fun _ : Fin 0 → ℝ => (1 : ℝ)) volume
      rw [integrable_const_iff]
      right
      have hvolume : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
        rw [Measure.volume_pi_eq_dirac (fun row : Fin 0 => Fin.elim0 row)]
        simp
      exact ⟨by simp [hvolume]⟩
  | succ dimension ih =>
      intro alpha beta halpha hbeta
      cases dimension with
      | zero =>
          exact integrableOn_selbergHalfIntegrand_one halpha hbeta
      | succ rank =>
          apply integrableOn_selbergHalfIntegrand_succ
            rank halpha hbeta
          exact ih (by positivity) (by positivity)

end FibonacciRibbonKernel
