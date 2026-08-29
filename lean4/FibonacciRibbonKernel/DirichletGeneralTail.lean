import FibonacciRibbonKernel.DirichletGeneralTarget

namespace FibonacciRibbonKernel

open MeasureTheory Set Pointwise
open scoped Classical Pointwise BigOperators

noncomputable def dirichletGeneralTailSum (dimension : ℕ)
    (parameters : Fin (dimension + 2) → ℝ) : ℝ :=
  ∑ anchor : Fin (dimension + 1), parameters anchor.succ

noncomputable def dirichletGeneralOuterWeight (dimension : ℕ)
    (parameters : Fin (dimension + 2) → ℝ) (first : ℝ) : ℝ :=
  first ^ (parameters 0 - 1) *
    (1 - first) ^ (dirichletGeneralTailSum dimension parameters - 1)

noncomputable def dirichletGeneralTailIntegral (dimension : ℕ)
    (parameters : Fin (dimension + 2) → ℝ) (first : ℝ) : ℝ :=
  ∫ tail in dirichletTailFiber dimension first,
    dirichletGeneralIntegrand (dimension + 1) parameters
      (Fin.cons first tail)

theorem dirichletGeneral_jacobian_power (dimension : ℕ)
    (tailSum : ℝ) {scale : ℝ} (hscale : 0 < scale) :
    scale ^ dimension *
        scale ^ (tailSum - (dimension + 1 : ℕ)) =
      scale ^ (tailSum - 1) := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_add hscale]
  congr 1
  push_cast
  ring

theorem dirichletGeneralTailIntegral_eq
    (dimension : ℕ) (parameters : Fin (dimension + 2) → ℝ)
    {first : ℝ} (hfirst : first ∈ Set.Ioo (0 : ℝ) 1) :
    dirichletGeneralTailIntegral dimension parameters first =
      dirichletGeneralOuterWeight dimension parameters first *
        dirichletGeneralIntegral dimension (Fin.tail parameters) := by
  let scale := 1 - first
  let lifted : (Fin dimension → ℝ) → ℝ := fun tail =>
    dirichletGeneralIntegrand (dimension + 1) parameters
      (Fin.cons first tail)
  let constant := first ^ (parameters 0 - 1) *
    scale ^ (dirichletGeneralTailSum dimension parameters -
      (dimension + 1 : ℕ))
  have hscale : 0 < scale := sub_pos.mpr hfirst.2
  have hscaledIntegral := Measure.setIntegral_comp_smul_of_pos
    (volume : Measure (Fin dimension → ℝ)) lifted
    (dirichletOpenSimplex dimension) hscale
  have hpointwise :
      (∫ coordinates in dirichletOpenSimplex dimension,
        lifted (scale • coordinates)) =
      constant *
        dirichletGeneralIntegral dimension (Fin.tail parameters) := by
    rw [show (∫ coordinates in dirichletOpenSimplex dimension,
        lifted (scale • coordinates)) =
      ∫ coordinates in dirichletOpenSimplex dimension,
        constant * dirichletGeneralIntegrand dimension
          (Fin.tail parameters) coordinates by
      apply setIntegral_congr_fun
      · exact dirichletOpenSimplex_measurableSet dimension
      · intro coordinates hcoordinates
        change dirichletGeneralIntegrand (dimension + 1) parameters
            (dirichletConsTransform dimension (first, coordinates)) = _
        rw [dirichletGeneralIntegrand_cons_scale dimension parameters
          (first, coordinates) hfirst hcoordinates]
        rfl]
    rw [integral_const_mul]
    rfl
  rw [hpointwise] at hscaledIntegral
  have hfiber :
      scale • dirichletOpenSimplex dimension =
        dirichletTailFiber dimension first := by
    dsimp only [scale]
    exact (dirichletTailFiber_eq_smul dimension hfirst).symm
  rw [hfiber] at hscaledIntegral
  unfold dirichletGeneralTailIntegral dirichletGeneralOuterWeight
  dsimp only [lifted, constant, scale] at hscaledIntegral
  have hdimensionPower :
      (((1 - first) ^ Module.finrank ℝ (Fin dimension → ℝ))⁻¹ : ℝ) =
        ((1 - first) ^ dimension)⁻¹ := by
    simp
  rw [hdimensionPower] at hscaledIntegral
  have hscalePower : (1 - first) ^ dimension ≠ 0 :=
    pow_ne_zero dimension hscale.ne'
  have hjacobian := dirichletGeneral_jacobian_power dimension
    (dirichletGeneralTailSum dimension parameters) hscale
  simp only [smul_eq_mul] at hscaledIntegral
  field_simp [hscalePower] at hscaledIntegral
  rw [← hscaledIntegral]
  linear_combination
    first ^ (parameters 0 - 1) *
      dirichletGeneralIntegral dimension (Fin.tail parameters) * hjacobian

theorem integrableOn_dirichletGeneralTail
    (dimension : ℕ) (parameters : Fin (dimension + 2) → ℝ)
    {first : ℝ} (hfirst : first ∈ Set.Ioo (0 : ℝ) 1)
    (hintegrable : IntegrableOn
      (dirichletGeneralIntegrand dimension (Fin.tail parameters))
      (dirichletOpenSimplex dimension)) :
    IntegrableOn
      (fun tail => dirichletGeneralIntegrand (dimension + 1) parameters
        (Fin.cons first tail))
      (dirichletTailFiber dimension first) := by
  let scale := 1 - first
  let constant := first ^ (parameters 0 - 1) *
    scale ^ (dirichletGeneralTailSum dimension parameters -
      (dimension + 1 : ℕ))
  let baseRestricted : (Fin dimension → ℝ) → ℝ :=
    (dirichletOpenSimplex dimension).indicator
      (dirichletGeneralIntegrand dimension (Fin.tail parameters))
  let tailRestricted : (Fin dimension → ℝ) → ℝ :=
    (dirichletTailFiber dimension first).indicator
      (fun tail => dirichletGeneralIntegrand (dimension + 1) parameters
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
      have hpoint := dirichletGeneralIntegrand_cons_scale
        dimension parameters (first, scale⁻¹ • tail) hfirst hy
      have htailRecover : scale • (scale⁻¹ • tail) = tail := by
        rw [← mul_smul, mul_inv_cancel₀ hscale.ne', one_smul]
      calc
        dirichletGeneralIntegrand (dimension + 1) parameters
            (Fin.cons first tail) =
          dirichletGeneralIntegrand (dimension + 1) parameters
            (Fin.cons first (scale • (scale⁻¹ • tail))) := by
              rw [htailRecover]
        _ = constant * dirichletGeneralIntegrand dimension
              (Fin.tail parameters) (scale⁻¹ • tail) := by
          change dirichletGeneralIntegrand (dimension + 1) parameters
            (dirichletConsTransform dimension
              (first, scale⁻¹ • tail)) = _
          dsimp only [constant, dirichletGeneralTailSum] at hpoint ⊢
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

theorem dirichletGeneralTailSum_pos
    (dimension : ℕ) (parameters : Fin (dimension + 2) → ℝ)
    (hparameters : ∀ anchor, 0 < parameters anchor) :
    0 < dirichletGeneralTailSum dimension parameters := by
  unfold dirichletGeneralTailSum
  apply Finset.sum_pos'
  · intro anchor hanchor
    exact (hparameters anchor.succ).le
  · exact ⟨0, Finset.mem_univ 0, hparameters (Fin.succ 0)⟩

theorem dirichletGeneralOuterWeight_eq_selberg
    (dimension : ℕ) (parameters : Fin (dimension + 2) → ℝ) :
    dirichletGeneralOuterWeight dimension parameters =
      selbergHalfWeight (parameters 0)
        (dirichletGeneralTailSum dimension parameters) := by
  funext first
  unfold dirichletGeneralOuterWeight selbergHalfWeight
  rfl

theorem integrableOn_dirichletGeneralOuterWeight
    (dimension : ℕ) (parameters : Fin (dimension + 2) → ℝ)
    (hparameters : ∀ anchor, 0 < parameters anchor) :
    IntegrableOn (dirichletGeneralOuterWeight dimension parameters)
      (Set.Ioo (0 : ℝ) 1) := by
  rw [dirichletGeneralOuterWeight_eq_selberg]
  exact integrableOn_selbergHalfWeight_Ioo
    (hparameters 0)
    (dirichletGeneralTailSum_pos dimension parameters hparameters)

end FibonacciRibbonKernel
