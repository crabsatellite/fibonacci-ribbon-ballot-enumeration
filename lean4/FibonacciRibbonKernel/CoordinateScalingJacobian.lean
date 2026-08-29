import FibonacciRibbonKernel.ActualRibbonRealSubstitution
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace FibonacciRibbonKernel

open MeasureTheory

noncomputable def coordinateScalarLinearMap
    (dimension : ℕ) (scalar : ℝ) :
    (Fin dimension → ℝ) →ₗ[ℝ] (Fin dimension → ℝ) :=
  scalar • LinearMap.id

@[simp] theorem coordinateScalarLinearMap_apply
    (dimension : ℕ) (scalar : ℝ) (coordinates : Fin dimension → ℝ) :
    coordinateScalarLinearMap dimension scalar coordinates =
      fun index => scalar * coordinates index := by
  rfl

theorem coordinateScalarLinearMap_det
    (dimension : ℕ) (scalar : ℝ) :
    LinearMap.det (coordinateScalarLinearMap dimension scalar) =
      scalar ^ dimension := by
  unfold coordinateScalarLinearMap
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
  simp

theorem map_coordinateScalarLinearMap_volume
    (dimension : ℕ) {scalar : ℝ} (hscalar : scalar ≠ 0) :
    Measure.map (coordinateScalarLinearMap dimension scalar)
        (volume : Measure (Fin dimension → ℝ)) =
      ENNReal.ofReal (|scalar ^ dimension|⁻¹) • volume := by
  rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi]
  · rw [coordinateScalarLinearMap_det]
    rw [abs_inv]
  · rw [coordinateScalarLinearMap_det]
    exact pow_ne_zero _ hscalar

theorem measurable_coordinateScalarLinearMap
    (dimension : ℕ) (scalar : ℝ) :
    Measurable (coordinateScalarLinearMap dimension scalar) :=
  (LinearMap.continuous_of_finiteDimensional
    (coordinateScalarLinearMap dimension scalar)).measurable

end FibonacciRibbonKernel
