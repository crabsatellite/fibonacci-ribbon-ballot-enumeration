import FibonacciRibbonKernel.DirichletHalfFiber
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace FibonacciRibbonKernel

open MeasureTheory Set Pointwise
open scoped Classical Pointwise

theorem dirichletOpenSimplex_measurableSet (dimension : ℕ) :
    MeasurableSet (dirichletOpenSimplex dimension) := by
  have hrepresentation : dirichletOpenSimplex dimension =
      (⋂ index : Fin dimension,
        {coordinates : Fin dimension → ℝ | 0 < coordinates index}) ∩
      {coordinates : Fin dimension → ℝ |
        (∑ index, coordinates index) < 1} := by
    ext coordinates
    simp [dirichletOpenSimplex]
  rw [hrepresentation]
  apply MeasurableSet.inter
  · exact MeasurableSet.iInter fun index =>
      measurableSet_lt measurable_const (measurable_pi_apply index)
  · exact measurableSet_lt
      (Finset.measurable_fun_sum Finset.univ
        fun index hindex => measurable_pi_apply index)
      measurable_const

theorem continuousOn_dirichletHalfIntegrand (dimension : ℕ) :
    ContinuousOn (dirichletHalfIntegrand dimension)
      (dirichletOpenSimplex dimension) := by
  unfold dirichletHalfIntegrand
  apply ContinuousOn.mul
  · apply continuousOn_finsetProd Finset.univ
    intro index hindex
    apply continuousOn_of_forall_continuousAt
    intro coordinates hcoordinates
    exact (continuous_apply index).continuousAt.rpow_const
      (Or.inl (hcoordinates.1 index).ne')
  · apply continuousOn_of_forall_continuousAt
    intro coordinates hcoordinates
    have hsum : ContinuousAt
        (fun coordinates : Fin dimension → ℝ =>
          1 - ∑ index, coordinates index) coordinates := by
      fun_prop
    exact hsum.rpow_const
      (Or.inl (sub_pos.mpr hcoordinates.2).ne')

noncomputable def dirichletHalfTailIntegral
    (dimension : ℕ) (first : ℝ) : ℝ :=
  ∫ tail in dirichletTailFiber dimension first,
    dirichletHalfIntegrand (dimension + 1) (Fin.cons first tail)

theorem dirichletTailFiber_measurableSet
    (dimension : ℕ) (first : ℝ) :
    MeasurableSet (dirichletTailFiber dimension first) := by
  have hrepresentation : dirichletTailFiber dimension first =
      (⋂ index : Fin dimension,
        {tail : Fin dimension → ℝ | 0 < tail index}) ∩
      {tail : Fin dimension → ℝ |
        (∑ index, tail index) < 1 - first} := by
    ext tail
    simp [dirichletTailFiber]
  rw [hrepresentation]
  apply MeasurableSet.inter
  · exact MeasurableSet.iInter fun index =>
      measurableSet_lt measurable_const (measurable_pi_apply index)
  · exact measurableSet_lt
      (Finset.measurable_fun_sum Finset.univ
        fun index hindex => measurable_pi_apply index)
      measurable_const

noncomputable def dirichletHalfOuterWeight
    (dimension : ℕ) (first : ℝ) : ℝ :=
  first ^ (-1 / 2 : ℝ) *
    (1 - first) ^ (((dimension : ℝ) - 1) / 2)

theorem dirichletHalf_jacobian_power (dimension : ℕ) {scale : ℝ}
    (hscale : 0 < scale) :
    scale ^ dimension *
        scale ^ (-((dimension + 1 : ℕ) : ℝ) / 2) =
      scale ^ (((dimension : ℝ) - 1) / 2) := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_add hscale]
  congr 1
  push_cast
  ring

theorem dirichletHalfTailIntegral_eq
    (dimension : ℕ) {first : ℝ}
    (hfirst : first ∈ Set.Ioo (0 : ℝ) 1) :
    dirichletHalfTailIntegral dimension first =
      dirichletHalfOuterWeight dimension first *
        dirichletHalfIntegral dimension := by
  let scale := 1 - first
  let lifted : (Fin dimension → ℝ) → ℝ := fun tail =>
    dirichletHalfIntegrand (dimension + 1) (Fin.cons first tail)
  have hscale : 0 < scale := sub_pos.mpr hfirst.2
  have hscaledIntegral := Measure.setIntegral_comp_smul_of_pos
    (volume : Measure (Fin dimension → ℝ)) lifted
    (dirichletOpenSimplex dimension) hscale
  have hpointwise :
      (∫ coordinates in dirichletOpenSimplex dimension,
        lifted (scale • coordinates)) =
      first ^ (-1 / 2 : ℝ) *
        scale ^ (-((dimension + 1 : ℕ) : ℝ) / 2) *
          dirichletHalfIntegral dimension := by
    rw [show (∫ coordinates in dirichletOpenSimplex dimension,
        lifted (scale • coordinates)) =
      ∫ coordinates in dirichletOpenSimplex dimension,
        (first ^ (-1 / 2 : ℝ) *
          scale ^ (-((dimension + 1 : ℕ) : ℝ) / 2)) *
            dirichletHalfIntegrand dimension coordinates by
      apply setIntegral_congr_fun
      · exact dirichletOpenSimplex_measurableSet dimension
      · intro coordinates hcoordinates
        change dirichletHalfIntegrand (dimension + 1)
            (dirichletConsTransform dimension (first, coordinates)) = _
        rw [dirichletHalfIntegrand_cons_scale dimension
          (first, coordinates) hfirst hcoordinates]]
    rw [integral_const_mul]
    rfl
  rw [hpointwise] at hscaledIntegral
  have hfiber :
      scale • dirichletOpenSimplex dimension =
        dirichletTailFiber dimension first := by
    dsimp only [scale]
    exact (dirichletTailFiber_eq_smul dimension hfirst).symm
  rw [hfiber] at hscaledIntegral
  unfold dirichletHalfTailIntegral dirichletHalfOuterWeight
  dsimp only [lifted, scale] at hscaledIntegral
  have hdimensionPower :
      (((1 - first) ^ Module.finrank ℝ (Fin dimension → ℝ))⁻¹ : ℝ) =
        ((1 - first) ^ dimension)⁻¹ := by
    simp
  rw [hdimensionPower] at hscaledIntegral
  have hscalePower : (1 - first) ^ dimension ≠ 0 :=
    pow_ne_zero dimension hscale.ne'
  have hjacobian := dirichletHalf_jacobian_power dimension hscale
  dsimp only [scale] at hjacobian
  simp only [smul_eq_mul] at hscaledIntegral
  field_simp [hscalePower] at hscaledIntegral
  have hexponent :
      -(((dimension + 1 : ℕ) : ℝ) / 2) =
        -((dimension + 1 : ℕ) : ℝ) / 2 := by ring
  rw [hexponent] at hscaledIntegral
  rw [← hscaledIntegral]
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring]
  linear_combination
    first ^ (-(1 / 2 : ℝ)) * dirichletHalfIntegral dimension * hjacobian

theorem integrableOn_dirichletHalfTail
    (dimension : ℕ) {first : ℝ}
    (hfirst : first ∈ Set.Ioo (0 : ℝ) 1)
    (hintegrable : IntegrableOn
      (dirichletHalfIntegrand dimension)
      (dirichletOpenSimplex dimension)) :
    IntegrableOn
      (fun tail => dirichletHalfIntegrand (dimension + 1)
        (Fin.cons first tail))
      (dirichletTailFiber dimension first) := by
  let scale := 1 - first
  let constant := first ^ (-1 / 2 : ℝ) *
    scale ^ (-((dimension + 1 : ℕ) : ℝ) / 2)
  let baseRestricted : (Fin dimension → ℝ) → ℝ :=
    (dirichletOpenSimplex dimension).indicator
      (dirichletHalfIntegrand dimension)
  let tailRestricted : (Fin dimension → ℝ) → ℝ :=
    (dirichletTailFiber dimension first).indicator
      (fun tail => dirichletHalfIntegrand (dimension + 1)
        (Fin.cons first tail))
  have hscale : 0 < scale := sub_pos.mpr hfirst.2
  have hbase : Integrable baseRestricted :=
    hintegrable.integrable_indicator
      (dirichletOpenSimplex_measurableSet dimension)
  have hscaled : Integrable
      (fun tail => baseRestricted (scale⁻¹ • tail)) :=
    hbase.comp_smul (inv_ne_zero hscale.ne')
  have hconstant : Integrable
      (fun tail => constant * baseRestricted (scale⁻¹ • tail)) :=
    hscaled.const_mul constant
  have hfunctions : tailRestricted =
      fun tail => constant * baseRestricted (scale⁻¹ • tail) := by
    funext tail
    by_cases htail : tail ∈ dirichletTailFiber dimension first
    · have hy : scale⁻¹ • tail ∈ dirichletOpenSimplex dimension := by
        rw [← Set.mem_smul_set_iff_inv_smul_mem₀ hscale.ne']
        rw [← dirichletTailFiber_eq_smul dimension hfirst]
        exact htail
      dsimp only [tailRestricted, baseRestricted]
      rw [Set.indicator_of_mem htail, Set.indicator_of_mem hy]
      have hpoint := dirichletHalfIntegrand_cons_scale dimension
        (first, scale⁻¹ • tail) hfirst hy
      have htailRecover : scale • (scale⁻¹ • tail) = tail := by
        rw [← mul_smul, mul_inv_cancel₀ hscale.ne', one_smul]
      calc
        dirichletHalfIntegrand (dimension + 1) (Fin.cons first tail) =
            dirichletHalfIntegrand (dimension + 1)
              (Fin.cons first (scale • (scale⁻¹ • tail))) := by
          rw [htailRecover]
        _ = constant * dirichletHalfIntegrand dimension
              (scale⁻¹ • tail) := by
          change dirichletHalfIntegrand (dimension + 1)
            (dirichletConsTransform dimension (first, scale⁻¹ • tail)) = _
          dsimp only [constant] at hpoint ⊢
          exact hpoint
    · have hy : scale⁻¹ • tail ∉ dirichletOpenSimplex dimension := by
        intro hy
        apply htail
        rw [dirichletTailFiber_eq_smul dimension hfirst]
        rw [Set.mem_smul_set_iff_inv_smul_mem₀ hscale.ne']
        exact hy
      dsimp only [tailRestricted, baseRestricted]
      rw [Set.indicator_of_notMem htail, Set.indicator_of_notMem hy]
      ring
  rw [← integrable_indicator_iff
    (dirichletTailFiber_measurableSet dimension first)]
  change Integrable tailRestricted
  rw [hfunctions]
  exact hconstant

end FibonacciRibbonKernel
