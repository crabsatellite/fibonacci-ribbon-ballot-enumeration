import FibonacciRibbonKernel.AllMinusLocalDCT

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped BigOperators

noncomputable def angleCoordinateReflection (angle : ℝ) : ℝ :=
  Real.pi - angle

theorem angleCoordinateReflection_involutive :
    Function.Involutive angleCoordinateReflection := by
  intro angle
  unfold angleCoordinateReflection
  ring

theorem angleCoordinateReflection_preimage_Ioc :
    angleCoordinateReflection ⁻¹' Set.Ioc (0 : ℝ) Real.pi =
      Set.Ico (0 : ℝ) Real.pi := by
  ext angle
  simp only [Set.mem_preimage, Set.mem_Ioc, Set.mem_Ico]
  unfold angleCoordinateReflection
  constructor <;> intro h <;> constructor <;> linarith

theorem measurePreserving_angleCoordinateReflection :
    MeasurePreserving angleCoordinateReflection
      cosineIntervalMeasure cosineIntervalMeasure := by
  have hvolume : MeasurePreserving angleCoordinateReflection
      (volume : Measure ℝ) volume := by
    change MeasurePreserving (fun angle : ℝ => Real.pi - angle)
      (volume : Measure ℝ) volume
    exact volume.measurePreserving_sub_left Real.pi
  have hrestrict := Measure.restrict_map (μ := (volume : Measure ℝ))
    hvolume.measurable
    (measurableSet_Ioc : MeasurableSet (Set.Ioc (0 : ℝ) Real.pi))
  rw [hvolume.map_eq, angleCoordinateReflection_preimage_Ioc] at hrestrict
  refine ⟨hvolume.measurable, ?_⟩
  unfold cosineIntervalMeasure
  calc
    (volume.restrict (Set.Ioc (0 : ℝ) Real.pi)).map
        angleCoordinateReflection =
      (volume.restrict (Set.Ico (0 : ℝ) Real.pi)).map
        angleCoordinateReflection := by
          exact congrArg (Measure.map angleCoordinateReflection)
            (restrict_Ico_eq_restrict_Ioc
              (μ := (volume : Measure ℝ))).symm
    _ = volume.restrict (Set.Ioc (0 : ℝ) Real.pi) := hrestrict.symm

noncomputable def angleReflectionEquiv (dimension : ℕ) :
    (Fin dimension → ℝ) ≃ᵐ (Fin dimension → ℝ) where
  toEquiv :=
    { toFun := fun angles coordinate =>
        angleCoordinateReflection (angles coordinate)
      invFun := fun angles coordinate =>
        angleCoordinateReflection (angles coordinate)
      left_inv := by
        intro angles
        funext coordinate
        exact angleCoordinateReflection_involutive (angles coordinate)
      right_inv := by
        intro angles
        funext coordinate
        exact angleCoordinateReflection_involutive (angles coordinate) }
  measurable_toFun := by
    change Measurable (fun angles : Fin dimension → ℝ =>
      fun coordinate => Real.pi - angles coordinate)
    fun_prop
  measurable_invFun := by
    change Measurable (fun angles : Fin dimension → ℝ =>
      fun coordinate => Real.pi - angles coordinate)
    fun_prop

theorem angleReflectionEquiv_apply
    (dimension : ℕ) (angles : Fin dimension → ℝ) (coordinate : Fin dimension) :
    angleReflectionEquiv dimension angles coordinate =
      Real.pi - angles coordinate := rfl

theorem measurePreserving_angleReflectionEquiv (dimension : ℕ) :
    MeasurePreserving (angleReflectionEquiv dimension)
      (cosineCubeProductMeasure dimension)
      (cosineCubeProductMeasure dimension) := by
  change MeasurePreserving
    (fun angles : Fin dimension → ℝ =>
      fun coordinate => angleCoordinateReflection (angles coordinate))
    (cosineCubeProductMeasure dimension)
    (cosineCubeProductMeasure dimension)
  unfold cosineCubeProductMeasure
  exact measurePreserving_pi
    (fun _ : Fin dimension => cosineIntervalMeasure)
    (fun _ : Fin dimension => cosineIntervalMeasure)
    (fun _ : Fin dimension => measurePreserving_angleCoordinateReflection)

theorem cosineCubeScale_angleReflection
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    cosineCubeScale (angleReflectionEquiv dimension angles) =
      -cosineCubeScale angles := by
  unfold cosineCubeScale
  simp_rw [angleReflectionEquiv_apply, Real.cos_pi_sub]
  rw [Finset.sum_neg_distrib]
  ring

noncomputable def allMinusAngleWeight
    (dimension : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  ∏ coordinate, (1 - Real.cos (angles coordinate))

theorem cosineCubeWeight_allPlus_eq
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    cosineCubeWeight dimension 0 angles =
      ∏ coordinate, (1 + Real.cos (angles coordinate)) := by
  unfold cosineCubeWeight cosineFactorWeight cosineCoordinateIsPlus
  apply Finset.prod_congr rfl
  intro coordinate _hcoordinate
  simp

theorem cosineCubeWeight_angleReflection
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    cosineCubeWeight dimension 0 (angleReflectionEquiv dimension angles) =
      allMinusAngleWeight dimension angles := by
  rw [cosineCubeWeight_allPlus_eq]
  unfold allMinusAngleWeight
  apply Finset.prod_congr rfl
  intro coordinate _hcoordinate
  rw [angleReflectionEquiv_apply, Real.cos_pi_sub]
  ring

end FibonacciRibbonKernel
