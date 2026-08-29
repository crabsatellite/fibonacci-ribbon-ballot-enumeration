import FibonacciRibbonKernel.DixonAndersonDensity
import Mathlib.MeasureTheory.Function.Jacobian

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped Classical Matrix BigOperators

theorem dixonAndersonDomain_isOpen {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ) :
    IsOpen (dixonAndersonDomain dimension anchors) := by
  have hrepresentation :
      dixonAndersonDomain dimension anchors =
        ⋂ index : Fin dimension,
          ({roots : Fin dimension → ℝ |
              roots index < anchors index.castSucc} ∩
            {roots : Fin dimension → ℝ |
              anchors index.succ < roots index}) := by
    ext roots
    simp [dixonAndersonDomain, DixonAndersonInterlacing]
  rw [hrepresentation]
  apply isOpen_iInter_of_finite
  intro index
  apply IsOpen.inter
  · exact isOpen_lt (continuous_apply index) continuous_const
  · exact isOpen_lt continuous_const (continuous_apply index)

theorem dixonAndersonDomain_measurableSet {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ) :
    MeasurableSet (dixonAndersonDomain dimension anchors) :=
  (dixonAndersonDomain_isOpen anchors).measurableSet

theorem andersonWeightChart_image_interlacing
    {dimension : ℕ} (anchors : Fin (dimension + 1) → ℝ)
    (hanchors : StrictAnti anchors) :
    andersonWeightChart anchors ''
        dixonAndersonDomain dimension anchors =
      dirichletOpenSimplex dimension := by
  apply Set.Subset.antisymm
  · rintro coordinates ⟨roots, hinterlace, rfl⟩
    exact andersonWeightChart_mem_simplex
      anchors roots hanchors hinterlace
  · intro coordinates hcoordinates
    rcases andersonWeightChart_surjective_on_interlacing
      anchors hanchors hcoordinates with
      ⟨roots, hinterlace, heq⟩
    exact ⟨roots, hinterlace, heq⟩

theorem abs_det_andersonWeightJacobianCLM
    {dimension : ℕ} (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ) :
    |(andersonWeightJacobianCLM anchors roots).det| =
      |(andersonWeightJacobianMatrix anchors roots).det| := by
  unfold andersonWeightJacobianCLM
  rw [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin']

theorem hasFDerivWithinAt_andersonWeightChartCLM
    {dimension : ℕ} (anchors : Fin (dimension + 1) → ℝ)
    (roots : Fin dimension → ℝ)
    (domain : Set (Fin dimension → ℝ)) :
    HasFDerivWithinAt (andersonWeightChart anchors)
      (andersonWeightJacobianCLM anchors roots) domain roots := by
  have hderiv :
      HasFDerivWithinAt (andersonWeightChart anchors)
        (andersonWeightChartDerivative anchors roots) domain roots :=
    (hasFDerivAt_andersonWeightChart anchors roots).hasFDerivWithinAt
  rw [andersonWeightChartDerivative_eq_toLin] at hderiv
  exact hderiv

theorem dixonAndersonHalfIntegral_eq_dirichletHalfIntegral
    {dimension : ℕ} (anchors : Fin (dimension + 1) → ℝ)
    (hanchors : StrictAnti anchors) :
    dixonAndersonHalfIntegral dimension anchors =
      dirichletHalfIntegral dimension := by
  let domain := dixonAndersonDomain dimension anchors
  have hchange :=
    integral_image_eq_integral_abs_det_fderiv_smul
      (μ := (volume : Measure (Fin dimension → ℝ)))
      (f := andersonWeightChart anchors)
      (f' := andersonWeightJacobianCLM anchors)
      (dixonAndersonDomain_measurableSet anchors)
      (fun roots hroots =>
        hasFDerivWithinAt_andersonWeightChartCLM
          anchors roots domain)
      (andersonWeightChart_injective_on_interlacing anchors hanchors)
      (dirichletHalfIntegrand dimension)
  rw [andersonWeightChart_image_interlacing anchors hanchors] at hchange
  unfold dixonAndersonHalfIntegral dirichletHalfIntegral
  rw [hchange]
  apply setIntegral_congr_fun
    (dixonAndersonDomain_measurableSet anchors)
  intro roots hinterlace
  change
    dixonAndersonHalfIntegrand dimension anchors roots =
      |(andersonWeightJacobianCLM anchors roots).det| *
        dirichletHalfIntegrand dimension
          (andersonWeightChart anchors roots)
  rw [abs_det_andersonWeightJacobianCLM]
  exact (andersonJacobian_mul_dirichletHalfIntegrand
    anchors roots hanchors hinterlace).symm

theorem dixonAndersonHalfEvaluation_all (dimension : ℕ) :
    DixonAndersonHalfEvaluation dimension := by
  intro anchors hanchors
  rw [dixonAndersonHalfIntegral_eq_dirichletHalfIntegral
    anchors hanchors]
  exact dirichletHalfEvaluation_all dimension

end FibonacciRibbonKernel
