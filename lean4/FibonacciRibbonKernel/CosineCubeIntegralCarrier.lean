import FibonacciRibbonKernel.CosineCubeMoment
import Mathlib.MeasureTheory.Integral.Pi

namespace FibonacciRibbonKernel

open MeasureTheory Real Set
open scoped BigOperators Interval

def cosineCoordinateIsPlus
    (plusPower minusPower : ℕ) (coordinate : Fin (plusPower + minusPower)) : Bool :=
  decide (coordinate.val < plusPower)

noncomputable def cosineCubeWeight
    (plusPower minusPower : ℕ)
    (angles : Fin (plusPower + minusPower) → ℝ) : ℝ :=
  ∏ coordinate,
    cosineFactorWeight
      (cosineCoordinateIsPlus plusPower minusPower coordinate)
      (angles coordinate)

noncomputable def cosineCubeScale
    {dimension : ℕ} (angles : Fin dimension → ℝ) : ℝ :=
  2 * ∑ coordinate, Real.cos (angles coordinate)

noncomputable def cosineCubeRawIntegrand
    (plusPower minusPower power : ℕ)
    (angles : Fin (plusPower + minusPower) → ℝ) : ℝ :=
  cosineCubeScale angles ^ power *
    cosineCubeWeight plusPower minusPower angles

noncomputable def cosineIntervalMeasure : Measure ℝ :=
  volume.restrict (Set.Ioc 0 Real.pi)

noncomputable instance cosineIntervalMeasure_isFinite :
    IsFiniteMeasure cosineIntervalMeasure := by
  unfold cosineIntervalMeasure
  infer_instance

noncomputable def cosineCubeProductMeasure (dimension : ℕ) :
    Measure (Fin dimension → ℝ) :=
  Measure.pi fun _ : Fin dimension => cosineIntervalMeasure

noncomputable instance cosineCubeProductMeasure_isFinite (dimension : ℕ) :
    IsFiniteMeasure (cosineCubeProductMeasure dimension) := by
  unfold cosineCubeProductMeasure
  infer_instance

noncomputable def cosineCubeIntegralMoment
    (plusPower minusPower power : ℕ) : ℝ :=
  (1 / Real.pi) ^ (plusPower + minusPower) *
    ∫ angles : Fin (plusPower + minusPower) → ℝ,
      cosineCubeRawIntegrand plusPower minusPower power angles
      ∂cosineCubeProductMeasure (plusPower + minusPower)

theorem cosineCubeProductMeasure_eq_restrict (dimension : ℕ) :
    cosineCubeProductMeasure dimension =
      (volume : Measure (Fin dimension → ℝ)).restrict
        (Set.univ.pi fun _ : Fin dimension => Set.Ioc (0 : ℝ) Real.pi) := by
  unfold cosineCubeProductMeasure cosineIntervalMeasure
  rw [volume_pi, Measure.restrict_pi_pi]

theorem continuous_cosineCubeScale (dimension : ℕ) :
    Continuous (cosineCubeScale (dimension := dimension)) := by
  unfold cosineCubeScale
  fun_prop

theorem continuous_cosineCubeWeight (plusPower minusPower : ℕ) :
    Continuous (cosineCubeWeight plusPower minusPower) := by
  unfold cosineCubeWeight
  apply continuous_finsetProd
  intro coordinate _hcoordinate
  exact (cosineFactorWeight_continuous
    (cosineCoordinateIsPlus plusPower minusPower coordinate)).comp
      (continuous_apply coordinate)

theorem continuous_cosineCubeRawIntegrand
    (plusPower minusPower power : ℕ) :
    Continuous (cosineCubeRawIntegrand plusPower minusPower power) := by
  unfold cosineCubeRawIntegrand
  exact (continuous_cosineCubeScale _).pow power |>.mul
    (continuous_cosineCubeWeight plusPower minusPower)

theorem cosineCubeIoc_subset_Icc (dimension : ℕ) :
    Set.univ.pi (fun _ : Fin dimension => Set.Ioc (0 : ℝ) Real.pi) ⊆
      Set.univ.pi (fun _ : Fin dimension => Set.Icc (0 : ℝ) Real.pi) := by
  intro angles hangles coordinate _hcoordinate
  exact ⟨(hangles coordinate (Set.mem_univ coordinate)).1.le,
    (hangles coordinate (Set.mem_univ coordinate)).2⟩

theorem integrable_cosineCubeRawIntegrand
    (plusPower minusPower power : ℕ) :
    Integrable (cosineCubeRawIntegrand plusPower minusPower power)
      (cosineCubeProductMeasure (plusPower + minusPower)) := by
  let dimension := plusPower + minusPower
  let cubeIoc : Set (Fin dimension → ℝ) :=
    Set.univ.pi fun _ : Fin dimension => Set.Ioc (0 : ℝ) Real.pi
  let cubeIcc : Set (Fin dimension → ℝ) :=
    Set.univ.pi fun _ : Fin dimension => Set.Icc (0 : ℝ) Real.pi
  have hcompact : IsCompact cubeIcc :=
    isCompact_univ_pi fun _ : Fin dimension => isCompact_Icc
  have hintegrableIcc : IntegrableOn
      (cosineCubeRawIntegrand plusPower minusPower power) cubeIcc :=
    (continuous_cosineCubeRawIntegrand plusPower minusPower power).continuousOn
      |>.integrableOn_compact hcompact
  have hintegrableIoc : IntegrableOn
      (cosineCubeRawIntegrand plusPower minusPower power) cubeIoc :=
    hintegrableIcc.mono_set (cosineCubeIoc_subset_Icc dimension)
  have hmeasure : cosineCubeProductMeasure dimension =
      (volume : Measure (Fin dimension → ℝ)).restrict cubeIoc := by
    simpa only [cubeIoc] using cosineCubeProductMeasure_eq_restrict dimension
  rw [hmeasure]
  exact hintegrableIoc

end FibonacciRibbonKernel
