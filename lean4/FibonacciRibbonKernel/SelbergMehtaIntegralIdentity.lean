import FibonacciRibbonKernel.SelbergMehtaScaling

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set
open scoped Classical Topology BigOperators

noncomputable def selbergMehtaAffineDerivative
    (dimension index : ℕ) :
    (Fin dimension → ℝ) →L[ℝ] (Fin dimension → ℝ) :=
  (selbergMehtaScale index)⁻¹ •
    ContinuousLinearMap.id ℝ (Fin dimension → ℝ)

set_option backward.isDefEq.respectTransparency false in
theorem hasFDerivAt_selbergMehtaAffine
    (dimension index : ℕ) (coordinates : Fin dimension → ℝ) :
    HasFDerivAt (selbergMehtaAffine dimension index)
      (selbergMehtaAffineDerivative dimension index) coordinates := by
  have hderivative : selbergMehtaAffineDerivative dimension index =
      ContinuousLinearMap.pi fun coordinate : Fin dimension =>
        (selbergMehtaScale index)⁻¹ •
          ContinuousLinearMap.proj
            (R := ℝ) (φ := fun _ : Fin dimension => ℝ) coordinate := by
    apply ContinuousLinearMap.ext
    intro direction
    funext coordinate
    simp [selbergMehtaAffineDerivative]
  rw [hderivative, hasFDerivAt_pi]
  intro coordinate
  change HasFDerivAt
    (fun current : Fin dimension → ℝ =>
      (1 / 2 : ℝ) + current coordinate / selbergMehtaScale index)
    ((selbergMehtaScale index)⁻¹ •
      ContinuousLinearMap.proj
        (R := ℝ) (φ := fun _ : Fin dimension => ℝ) coordinate)
    coordinates
  have hconstant : HasFDerivAt
      (fun _ : Fin dimension → ℝ => (1 / 2 : ℝ))
      (0 : (Fin dimension → ℝ) →L[ℝ] ℝ) coordinates :=
    hasFDerivAt_const _ _
  have happly : HasFDerivAt
      (fun current : Fin dimension → ℝ => current coordinate)
      (ContinuousLinearMap.proj
        (R := ℝ) (φ := fun _ : Fin dimension => ℝ) coordinate)
      coordinates := hasFDerivAt_apply coordinate coordinates
  have hadd := hconstant.add
    (happly.const_mul (selbergMehtaScale index)⁻¹)
  have hadd' : HasFDerivAt
      ((fun _ : Fin dimension → ℝ => (1 / 2 : ℝ)) +
        fun current : Fin dimension → ℝ =>
          (selbergMehtaScale index)⁻¹ * current coordinate)
      ((selbergMehtaScale index)⁻¹ •
        ContinuousLinearMap.proj
          (R := ℝ) (φ := fun _ : Fin dimension => ℝ) coordinate)
      coordinates := hadd.congr_fderiv (by simp)
  apply hadd'.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun current => by
    change (1 / 2 : ℝ) + current coordinate /
        selbergMehtaScale index =
      (1 / 2 : ℝ) +
        (selbergMehtaScale index)⁻¹ * current coordinate
    field_simp [(selbergMehtaScale_pos index).ne']

theorem selbergMehtaAffine_injective
    (dimension index : ℕ) :
    Function.Injective (selbergMehtaAffine dimension index) := by
  intro left right hequal
  funext coordinate
  have hcoordinate := congrFun hequal coordinate
  unfold selbergMehtaAffine at hcoordinate
  have hscale := (selbergMehtaScale_pos index).ne'
  field_simp [hscale] at hcoordinate
  linarith

theorem selbergMehtaAffine_image_scaledDomain
    (dimension index : ℕ) :
    selbergMehtaAffine dimension index ''
        selbergMehtaScaledDomain dimension index =
      orderedSelbergDomain dimension := by
  apply Set.Subset.antisymm
  · rintro coordinates ⟨source, hsource, rfl⟩
    exact (selbergMehtaAffine_mem_ordered_iff_scaled
      dimension index source).mpr hsource
  · intro coordinates hcoordinates
    let source : Fin dimension → ℝ := fun coordinate =>
      selbergMehtaScale index * (coordinates coordinate - 1 / 2)
    have hrecover :
        selbergMehtaAffine dimension index source = coordinates := by
      funext coordinate
      unfold selbergMehtaAffine
      dsimp only [source]
      have hscale := (selbergMehtaScale_pos index).ne'
      field_simp [hscale]
      ring
    have hsource : source ∈ selbergMehtaScaledDomain dimension index :=
      (selbergMehtaAffine_mem_ordered_iff_scaled
        dimension index source).mp (hrecover.symm ▸ hcoordinates)
    exact ⟨source, hsource, hrecover⟩

theorem det_selbergMehtaAffineDerivative
    (dimension index : ℕ) :
    (selbergMehtaAffineDerivative dimension index).det =
      (selbergMehtaScale index)⁻¹ ^ dimension := by
  unfold selbergMehtaAffineDerivative
  change LinearMap.det
      ((selbergMehtaScale index)⁻¹ •
        LinearMap.id (R := ℝ) (M := Fin dimension → ℝ)) = _
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
  simp

theorem selbergMehtaNormalization_pos (dimension index : ℕ) :
    0 < selbergMehtaNormalization dimension index := by
  unfold selbergMehtaNormalization
  exact mul_pos (pow_pos (by norm_num) _)
    (pow_pos (selbergMehtaScale_pos index) _)

theorem selbergMehta_inverseNormalization
    (dimension index : ℕ) :
    (selbergMehtaScale index)⁻¹ ^ dimension *
        (1 / 4 : ℝ) ^ ((index + 1) * dimension) *
        (selbergMehtaScale index)⁻¹ ^ mehtaPairCount dimension =
      (selbergMehtaNormalization dimension index)⁻¹ := by
  unfold selbergMehtaNormalization
  have hscale := (selbergMehtaScale_pos index).ne'
  field_simp [hscale]
  have hscaleDimension :
      selbergMehtaScale index ^ dimension *
        (selbergMehtaScale index)⁻¹ ^ dimension = 1 := by
    rw [← mul_pow]
    simp [hscale]
  have hscalePairs :
      selbergMehtaScale index ^ mehtaPairCount dimension *
        (selbergMehtaScale index)⁻¹ ^ mehtaPairCount dimension = 1 := by
    rw [← mul_pow]
    simp [hscale]
  have hfourDimension :
      (1 / 4 : ℝ) ^ dimension * 4 ^ dimension = 1 := by
    rw [← mul_pow]
    norm_num
  have hfourIndex :
      (1 / 4 : ℝ) ^ (dimension * index) *
        4 ^ (dimension * index) = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = (selbergMehtaScale index ^ dimension *
          (selbergMehtaScale index)⁻¹ ^ dimension) *
        (selbergMehtaScale index ^ mehtaPairCount dimension *
          (selbergMehtaScale index)⁻¹ ^ mehtaPairCount dimension) *
        ((1 / 4 : ℝ) ^ dimension * 4 ^ dimension) *
        ((1 / 4 : ℝ) ^ (dimension * index) *
          4 ^ (dimension * index)) := by ring
    _ = 1 := by
      rw [hscaleDimension, hscalePairs,
        hfourDimension, hfourIndex]
      norm_num

theorem integral_selbergMehtaRescaled_eq_normalizedSelberg
    (dimension index : ℕ) :
    (∫ coordinates,
      selbergMehtaRescaledIntegrand dimension index coordinates) =
      selbergMehtaNormalization dimension index *
        orderedSelbergHalfIntegral dimension
          ((index + 2 : ℕ) : ℝ) ((index + 2 : ℕ) : ℝ) := by
  let core : (Fin dimension → ℝ) → ℝ := fun coordinates =>
    (∏ coordinate, selbergMehtaScalarWeight index
      (coordinates coordinate)) *
      standardMehtaVandermonde dimension coordinates
  have hchange :=
    integral_image_eq_integral_abs_det_fderiv_smul
      (μ := (volume : Measure (Fin dimension → ℝ)))
      (f := selbergMehtaAffine dimension index)
      (f' := fun _ => selbergMehtaAffineDerivative dimension index)
      (selbergMehtaScaledDomain_measurableSet dimension index)
      (fun coordinates hcoordinates =>
        (hasFDerivAt_selbergMehtaAffine
          dimension index coordinates).hasFDerivWithinAt)
      (selbergMehtaAffine_injective dimension index).injOn
      (selbergHalfIntegrand dimension
        ((index + 2 : ℕ) : ℝ) ((index + 2 : ℕ) : ℝ))
  rw [selbergMehtaAffine_image_scaledDomain] at hchange
  have hpointwise :
      (∫ coordinates in selbergMehtaScaledDomain dimension index,
        |(selbergMehtaAffineDerivative dimension index).det| *
          selbergHalfIntegrand dimension
            ((index + 2 : ℕ) : ℝ) ((index + 2 : ℕ) : ℝ)
            (selbergMehtaAffine dimension index coordinates)) =
      (selbergMehtaNormalization dimension index)⁻¹ *
        ∫ coordinates in selbergMehtaScaledDomain dimension index,
          core coordinates := by
    rw [show (∫ coordinates in selbergMehtaScaledDomain dimension index,
        |(selbergMehtaAffineDerivative dimension index).det| *
          selbergHalfIntegrand dimension
            ((index + 2 : ℕ) : ℝ) ((index + 2 : ℕ) : ℝ)
            (selbergMehtaAffine dimension index coordinates)) =
      ∫ coordinates in selbergMehtaScaledDomain dimension index,
        (selbergMehtaNormalization dimension index)⁻¹ *
          core coordinates by
      apply setIntegral_congr_fun
        (selbergMehtaScaledDomain_measurableSet dimension index)
      intro coordinates hcoordinates
      rw [det_selbergMehtaAffineDerivative,
        abs_pow, abs_inv, abs_of_pos (selbergMehtaScale_pos index)]
      change (selbergMehtaScale index)⁻¹ ^ dimension *
          selbergHalfIntegrand dimension ((index + 2 : ℕ) : ℝ)
            ((index + 2 : ℕ) : ℝ)
            (selbergMehtaAffine dimension index coordinates) =
        (selbergMehtaNormalization dimension index)⁻¹ *
          core coordinates
      rw [selbergHalfIntegrand_affine_eq
        dimension index coordinates hcoordinates]
      rw [← selbergMehta_inverseNormalization dimension index]
      dsimp only [core]
      ring]
    rw [integral_const_mul]
  simp only [smul_eq_mul] at hchange
  rw [hpointwise] at hchange
  have hrestricted :
      (∫ coordinates,
        selbergMehtaRescaledIntegrand dimension index coordinates) =
      ∫ coordinates in selbergMehtaScaledDomain dimension index,
        core coordinates := by
    unfold selbergMehtaRescaledIntegrand core
    rw [integral_indicator
      (selbergMehtaScaledDomain_measurableSet dimension index)]
  rw [hrestricted]
  unfold orderedSelbergHalfIntegral
  have hnormalization := (selbergMehtaNormalization_pos dimension index).ne'
  field_simp [hnormalization] at hchange ⊢
  exact hchange.symm

theorem tendsto_normalizedExpectedSelberg_to_standardMehta
    (dimension : ℕ) :
    Tendsto (fun index =>
      selbergMehtaNormalization dimension index *
        expectedOrderedSelbergHalfIntegral dimension
          ((index + 2 : ℕ) : ℝ) ((index + 2 : ℕ) : ℝ))
      atTop (nhds (standardMehtaChamberIntegral dimension)) := by
  have hlimit := tendsto_integral_selbergMehtaRescaledIntegrand dimension
  apply hlimit.congr'
  filter_upwards with index
  rw [integral_selbergMehtaRescaled_eq_normalizedSelberg]
  rw [orderedSelbergHalfEvaluation_all dimension (by positivity) (by positivity)]

end FibonacciRibbonKernel
