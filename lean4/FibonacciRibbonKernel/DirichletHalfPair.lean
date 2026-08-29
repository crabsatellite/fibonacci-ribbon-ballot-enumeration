import FibonacciRibbonKernel.DirichletHalfSplit

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped Classical

theorem dirichletPairDomain_measurableSet (dimension : ℕ) :
    MeasurableSet (dirichletPairDomain dimension) := by
  have hrepresentation : dirichletPairDomain dimension =
      {input : ℝ × (Fin dimension → ℝ) | 0 < input.1} ∩
      (⋂ index : Fin dimension,
        {input : ℝ × (Fin dimension → ℝ) | 0 < input.2 index}) ∩
      {input : ℝ × (Fin dimension → ℝ) |
        (∑ index, input.2 index) < 1 - input.1} := by
    ext input
    simp [dirichletPairDomain, dirichletTailFiber, and_assoc]
  rw [hrepresentation]
  apply MeasurableSet.inter
  · apply MeasurableSet.inter
    · exact measurableSet_lt measurable_const measurable_fst
    · exact MeasurableSet.iInter fun index =>
        measurableSet_lt measurable_const
          ((measurable_pi_apply index).comp measurable_snd)
  · exact measurableSet_lt
      (Finset.measurable_fun_sum Finset.univ fun index hindex =>
        (measurable_pi_apply index).comp measurable_snd)
      (measurable_const.sub measurable_fst)

theorem dirichletPairDomain_first_mem
    {dimension : ℕ} {input : ℝ × (Fin dimension → ℝ)}
    (hinput : input ∈ dirichletPairDomain dimension) :
    input.1 ∈ Set.Ioo (0 : ℝ) 1 := by
  have hfirst : 0 < input.1 := hinput.1
  have hsumNonneg : 0 ≤ ∑ index, input.2 index :=
    Finset.sum_nonneg fun index hindex => (hinput.2.1 index).le
  have hfirstLt : input.1 < 1 := by linarith [hinput.2.2]
  exact ⟨hfirst, hfirstLt⟩

theorem dirichletHalfIntegrand_nonneg_of_mem
    {dimension : ℕ} {coordinates : Fin dimension → ℝ}
    (hcoordinates : coordinates ∈ dirichletOpenSimplex dimension) :
    0 ≤ dirichletHalfIntegrand dimension coordinates := by
  unfold dirichletHalfIntegrand
  apply mul_nonneg
  · exact Finset.prod_nonneg fun index hindex =>
      Real.rpow_nonneg (hcoordinates.1 index).le _
  · exact Real.rpow_nonneg (sub_pos.mpr hcoordinates.2).le _

noncomputable def dirichletPairRestricted (dimension : ℕ) :
    (ℝ × (Fin dimension → ℝ)) → ℝ :=
  (dirichletPairDomain dimension).indicator fun input =>
    dirichletHalfIntegrand (dimension + 1) (Fin.cons input.1 input.2)

theorem dirichletPairRestricted_nonneg (dimension : ℕ)
    (input : ℝ × (Fin dimension → ℝ)) :
    0 ≤ dirichletPairRestricted dimension input := by
  by_cases hinput : input ∈ dirichletPairDomain dimension
  · rw [dirichletPairRestricted, Set.indicator_of_mem hinput]
    apply dirichletHalfIntegrand_nonneg_of_mem
    exact (finCons_mem_dirichletSimplex_iff dimension input.1 input.2).mpr hinput
  · rw [dirichletPairRestricted, Set.indicator_of_notMem hinput]

theorem aestronglyMeasurable_dirichletPairRestricted (dimension : ℕ) :
    AEStronglyMeasurable (dirichletPairRestricted dimension)
      ((volume : Measure ℝ).prod
        (volume : Measure (Fin dimension → ℝ))) := by
  rw [dirichletPairRestricted,
    aestronglyMeasurable_indicator_iff
      (dirichletPairDomain_measurableSet dimension)]
  apply ContinuousOn.aestronglyMeasurable
  · apply (continuousOn_dirichletHalfIntegrand (dimension + 1)).comp
    · fun_prop
    · intro input hinput
      exact (finCons_mem_dirichletSimplex_iff dimension
        input.1 input.2).mpr hinput
  · exact dirichletPairDomain_measurableSet dimension

theorem dirichletPairRestricted_inner (dimension : ℕ) (first : ℝ) :
    (∫ tail : Fin dimension → ℝ,
      dirichletPairRestricted dimension (first, tail)) =
      (Set.Ioo (0 : ℝ) 1).indicator
        (dirichletHalfTailIntegral dimension) first := by
  by_cases hfirst : first ∈ Set.Ioo (0 : ℝ) 1
  · rw [Set.indicator_of_mem hfirst]
    unfold dirichletPairRestricted dirichletHalfTailIntegral
    rw [← integral_indicator
      (dirichletTailFiber_measurableSet dimension first)]
    apply integral_congr_ae
    filter_upwards with tail
    by_cases htail : tail ∈ dirichletTailFiber dimension first
    · rw [Set.indicator_of_mem htail, Set.indicator_of_mem]
      exact ⟨hfirst.1, htail⟩
    · rw [Set.indicator_of_notMem htail, Set.indicator_of_notMem]
      intro hpair
      exact htail hpair.2
  · rw [Set.indicator_of_notMem hfirst]
    have hzero : (fun tail : Fin dimension → ℝ =>
        dirichletPairRestricted dimension (first, tail)) =
          (fun _ => 0) := by
      funext tail
      unfold dirichletPairRestricted
      rw [Set.indicator_of_notMem]
      intro hpair
      exact hfirst (dirichletPairDomain_first_mem hpair)
    rw [hzero]
    simp

theorem dirichletPairRestricted_inner_norm (dimension : ℕ) (first : ℝ) :
    (∫ tail : Fin dimension → ℝ,
      ‖dirichletPairRestricted dimension (first, tail)‖) =
      (Set.Ioo (0 : ℝ) 1).indicator
        (dirichletHalfTailIntegral dimension) first := by
  rw [show (fun tail : Fin dimension → ℝ =>
      ‖dirichletPairRestricted dimension (first, tail)‖) =
    fun tail => dirichletPairRestricted dimension (first, tail) by
      funext tail
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact dirichletPairRestricted_nonneg dimension (first, tail)]
  exact dirichletPairRestricted_inner dimension first

theorem dirichletHalfOuterWeight_eq_selberg (dimension : ℕ) :
    dirichletHalfOuterWeight dimension =
      selbergHalfWeight (1 / 2) (((dimension + 1 : ℕ) : ℝ) / 2) := by
  funext first
  unfold dirichletHalfOuterWeight selbergHalfWeight
  have hfirstExponent : (-1 / 2 : ℝ) = 1 / 2 - 1 := by ring
  have hsecondExponent :
      ((dimension : ℝ) - 1) / 2 =
        (((dimension + 1 : ℕ) : ℝ) / 2) - 1 := by
    push_cast
    ring
  rw [hfirstExponent, hsecondExponent]

theorem integrableOn_dirichletHalfOuterWeight (dimension : ℕ) :
    IntegrableOn (dirichletHalfOuterWeight dimension) (Set.Ioo (0 : ℝ) 1) := by
  rw [dirichletHalfOuterWeight_eq_selberg]
  apply integrableOn_selbergHalfWeight_Ioo <;> positivity

end FibonacciRibbonKernel
