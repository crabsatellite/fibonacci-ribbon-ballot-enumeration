import FibonacciRibbonKernel.WeylWeightScaling

namespace FibonacciRibbonKernel

open MeasureTheory Set

noncomputable def oddCosineCubeScale
    {dimension : ℕ} (angles : Fin dimension → ℝ) : ℝ :=
  1 + cosineCubeScale angles

noncomputable def weightedCosineCubePowerIntegrand
    {dimension : ℕ} (scale : (Fin dimension → ℝ) → ℝ)
    (weight : (Fin dimension → ℝ) → ℝ) (power : ℕ)
    (angles : Fin dimension → ℝ) : ℝ :=
  scale angles ^ power * weight angles

noncomputable def weightedCosineCubeMoment
    {dimension : ℕ} (scale : (Fin dimension → ℝ) → ℝ)
    (weight : (Fin dimension → ℝ) → ℝ) (power : ℕ) : ℝ :=
  ∫ angles : Fin dimension → ℝ,
    weightedCosineCubePowerIntegrand scale weight power angles
    ∂cosineCubeProductMeasure dimension

noncomputable def weightedCosineCubeFibonacciIntegrand
    {dimension : ℕ} (scale : (Fin dimension → ℝ) → ℝ)
    (weight : (Fin dimension → ℝ) → ℝ) (power : ℕ)
    (angles : Fin dimension → ℝ) : ℝ :=
  fibonacciScaleKernel (scale angles) power * weight angles

noncomputable def weightedCosineCubeFibonacciMoment
    {dimension : ℕ} (scale : (Fin dimension → ℝ) → ℝ)
    (weight : (Fin dimension → ℝ) → ℝ) (power : ℕ) : ℝ :=
  ∫ angles : Fin dimension → ℝ,
    weightedCosineCubeFibonacciIntegrand scale weight power angles
    ∂cosineCubeProductMeasure dimension

theorem continuous_cosineVandermondeWeight (dimension : ℕ) :
    Continuous (cosineVandermondeWeight dimension) := by
  unfold cosineVandermondeWeight
  apply continuous_finsetProd
  intro upper _hupper
  apply continuous_finsetProd
  intro lower _hlower
  exact (((Real.continuous_cos.comp (continuous_apply upper)).sub
    (Real.continuous_cos.comp (continuous_apply lower))).pow 2)

theorem continuous_evenWeylAngleWeight (dimension : ℕ) :
    Continuous (evenWeylAngleWeight dimension) := by
  unfold evenWeylAngleWeight
  apply (continuous_cosineVandermondeWeight dimension).mul
  apply continuous_finsetProd
  intro coordinate _hcoordinate
  exact continuous_const.add
    (Real.continuous_cos.comp (continuous_apply coordinate))

theorem continuous_oddWeylAngleWeight (dimension : ℕ) :
    Continuous (oddWeylAngleWeight dimension) := by
  unfold oddWeylAngleWeight
  apply (continuous_cosineVandermondeWeight dimension).mul
  apply continuous_finsetProd
  intro coordinate _hcoordinate
  exact (continuous_const.sub
      (Real.continuous_cos.comp (continuous_apply coordinate))).mul
    (continuous_const.add
      (Real.continuous_cos.comp (continuous_apply coordinate)))

theorem integrable_continuous_cosineCube
    {dimension : ℕ} {function : (Fin dimension → ℝ) → ℝ}
    (hfunction : Continuous function) :
    Integrable function (cosineCubeProductMeasure dimension) := by
  let cubeIoc : Set (Fin dimension → ℝ) :=
    Set.univ.pi fun _ : Fin dimension => Set.Ioc (0 : ℝ) Real.pi
  let cubeIcc : Set (Fin dimension → ℝ) :=
    Set.univ.pi fun _ : Fin dimension => Set.Icc (0 : ℝ) Real.pi
  have hcompact : IsCompact cubeIcc :=
    isCompact_univ_pi fun _ : Fin dimension => isCompact_Icc
  have hintegrableIcc : IntegrableOn function cubeIcc :=
    hfunction.continuousOn.integrableOn_compact hcompact
  have hintegrableIoc : IntegrableOn function cubeIoc :=
    hintegrableIcc.mono_set (cosineCubeIoc_subset_Icc dimension)
  have hmeasure : cosineCubeProductMeasure dimension =
      (volume : Measure (Fin dimension → ℝ)).restrict cubeIoc := by
    simpa only [cubeIoc] using cosineCubeProductMeasure_eq_restrict dimension
  rw [hmeasure]
  exact hintegrableIoc

theorem integrable_weightedCosineCubePowerIntegrand
    {dimension power : ℕ}
    {scale weight : (Fin dimension → ℝ) → ℝ}
    (hscale : Continuous scale) (hweight : Continuous weight) :
    Integrable (weightedCosineCubePowerIntegrand scale weight power)
      (cosineCubeProductMeasure dimension) := by
  apply integrable_continuous_cosineCube
  unfold weightedCosineCubePowerIntegrand
  exact (hscale.pow power).mul hweight

theorem weightedCosineCubeFibonacciIntegrand_eq_finite_sum
    {dimension : ℕ} (scale weight : (Fin dimension → ℝ) → ℝ)
    (power : ℕ) (angles : Fin dimension → ℝ) :
    weightedCosineCubeFibonacciIntegrand scale weight power angles =
      ∑ degree ∈ Finset.range (power + 1),
        ribbonTransformBasisWeightR power degree *
          weightedCosineCubePowerIntegrand scale weight degree angles := by
  unfold weightedCosineCubeFibonacciIntegrand
  rw [fibonacciScaleKernel_eq_finite_transform]
  unfold weightedCosineCubePowerIntegrand
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro degree _hdegree
  ring

theorem weightedCosineCubeFibonacciMoment_eq_finite_transform
    {dimension : ℕ} (scale weight : (Fin dimension → ℝ) → ℝ)
    (hscale : Continuous scale) (hweight : Continuous weight)
    (power : ℕ) :
    weightedCosineCubeFibonacciMoment scale weight power =
      ∑ degree ∈ Finset.range (power + 1),
        ribbonTransformBasisWeightR power degree *
          weightedCosineCubeMoment scale weight degree := by
  unfold weightedCosineCubeFibonacciMoment weightedCosineCubeMoment
  rw [show (fun angles : Fin dimension → ℝ =>
      weightedCosineCubeFibonacciIntegrand scale weight power angles) =
      fun angles =>
        ∑ degree ∈ Finset.range (power + 1),
          ribbonTransformBasisWeightR power degree *
            weightedCosineCubePowerIntegrand scale weight degree angles by
    funext angles
    exact weightedCosineCubeFibonacciIntegrand_eq_finite_sum
      scale weight power angles]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro degree _hdegree
    rw [integral_const_mul]
  · intro degree _hdegree
    exact (integrable_weightedCosineCubePowerIntegrand
      (power := degree) hscale hweight).const_mul _

noncomputable def evenWeylGeometricMoment
    (dimension power : ℕ) : ℝ :=
  weightedCosineCubeMoment
    (cosineCubeScale (dimension := dimension))
    (evenWeylAngleWeight dimension) power

noncomputable def evenWeylFibonacciMoment
    (dimension power : ℕ) : ℝ :=
  weightedCosineCubeFibonacciMoment
    (cosineCubeScale (dimension := dimension))
    (evenWeylAngleWeight dimension) power

noncomputable def oddWeylGeometricMoment
    (dimension power : ℕ) : ℝ :=
  weightedCosineCubeMoment
    (oddCosineCubeScale (dimension := dimension))
    (oddWeylAngleWeight dimension) power

noncomputable def oddWeylFibonacciMoment
    (dimension power : ℕ) : ℝ :=
  weightedCosineCubeFibonacciMoment
    (oddCosineCubeScale (dimension := dimension))
    (oddWeylAngleWeight dimension) power

theorem continuous_oddCosineCubeScale (dimension : ℕ) :
    Continuous (oddCosineCubeScale (dimension := dimension)) := by
  unfold oddCosineCubeScale
  exact continuous_const.add (continuous_cosineCubeScale dimension)

theorem evenWeylFibonacciMoment_eq_finite_transform
    (dimension power : ℕ) :
    evenWeylFibonacciMoment dimension power =
      ∑ degree ∈ Finset.range (power + 1),
        ribbonTransformBasisWeightR power degree *
          evenWeylGeometricMoment dimension degree := by
  exact weightedCosineCubeFibonacciMoment_eq_finite_transform
    _ _ (continuous_cosineCubeScale dimension)
    (continuous_evenWeylAngleWeight dimension) power

theorem oddWeylFibonacciMoment_eq_finite_transform
    (dimension power : ℕ) :
    oddWeylFibonacciMoment dimension power =
      ∑ degree ∈ Finset.range (power + 1),
        ribbonTransformBasisWeightR power degree *
          oddWeylGeometricMoment dimension degree := by
  exact weightedCosineCubeFibonacciMoment_eq_finite_transform
    _ _ (continuous_oddCosineCubeScale dimension)
    (continuous_oddWeylAngleWeight dimension) power

end FibonacciRibbonKernel
