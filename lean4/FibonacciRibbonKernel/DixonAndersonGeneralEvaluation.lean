import FibonacciRibbonKernel.DixonAndersonGeneralDensity

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped Classical Matrix BigOperators

noncomputable def dixonAndersonGeneralIntegral {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (parameters : Fin (dimension + 1) → ℝ) : ℝ :=
  ∫ roots in dixonAndersonDomain dimension anchors,
    dixonAndersonGeneralIntegrand anchors parameters roots

noncomputable def expectedDixonAndersonGeneralIntegral {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (parameters : Fin (dimension + 1) → ℝ) : ℝ :=
  dixonAndersonGeneralAnchorFactor anchors parameters *
    expectedDirichletGeneralIntegral dimension parameters

def DixonAndersonGeneralEvaluation {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (parameters : Fin (dimension + 1) → ℝ) : Prop :=
  dixonAndersonGeneralIntegral anchors parameters =
    expectedDixonAndersonGeneralIntegral anchors parameters

theorem dirichletGeneralIntegral_eq_andersonPullback
    {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (parameters : Fin (dimension + 1) → ℝ)
    (hanchors : StrictAnti anchors) :
    dirichletGeneralIntegral dimension parameters =
      ∫ roots in dixonAndersonDomain dimension anchors,
        |(andersonWeightJacobianMatrix anchors roots).det| *
          dirichletGeneralIntegrand dimension parameters
            (andersonWeightChart anchors roots) := by
  have hchange :=
    integral_image_eq_integral_abs_det_fderiv_smul
      (μ := (volume : Measure (Fin dimension → ℝ)))
      (f := andersonWeightChart anchors)
      (f' := andersonWeightJacobianCLM anchors)
      (dixonAndersonDomain_measurableSet anchors)
      (fun roots hroots =>
        hasFDerivWithinAt_andersonWeightChartCLM anchors roots
          (dixonAndersonDomain dimension anchors))
      (andersonWeightChart_injective_on_interlacing anchors hanchors)
      (dirichletGeneralIntegrand dimension parameters)
  rw [andersonWeightChart_image_interlacing anchors hanchors] at hchange
  unfold dirichletGeneralIntegral
  rw [hchange]
  apply setIntegral_congr_fun
    (dixonAndersonDomain_measurableSet anchors)
  intro roots hinterlace
  change |(andersonWeightJacobianCLM anchors roots).det| *
      dirichletGeneralIntegrand dimension parameters
        (andersonWeightChart anchors roots) =
    |(andersonWeightJacobianMatrix anchors roots).det| *
      dirichletGeneralIntegrand dimension parameters
        (andersonWeightChart anchors roots)
  rw [abs_det_andersonWeightJacobianCLM]

theorem dixonAndersonGeneralEvaluation
    {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (parameters : Fin (dimension + 1) → ℝ)
    (hanchors : StrictAnti anchors)
    (hparameters : ∀ anchor, 0 < parameters anchor) :
    DixonAndersonGeneralEvaluation anchors parameters := by
  have hpullback := dirichletGeneralIntegral_eq_andersonPullback
    anchors parameters hanchors
  have hdirichlet := dirichletGeneralEvaluation_all
    dimension parameters hparameters
  unfold DixonAndersonGeneralEvaluation
  unfold dixonAndersonGeneralIntegral
  unfold expectedDixonAndersonGeneralIntegral
  calc
    (∫ roots in dixonAndersonDomain dimension anchors,
        dixonAndersonGeneralIntegrand anchors parameters roots) =
      ∫ roots in dixonAndersonDomain dimension anchors,
        dixonAndersonGeneralAnchorFactor anchors parameters *
          (|(andersonWeightJacobianMatrix anchors roots).det| *
            dirichletGeneralIntegrand dimension parameters
              (andersonWeightChart anchors roots)) := by
        apply setIntegral_congr_fun
          (dixonAndersonDomain_measurableSet anchors)
        intro roots hinterlace
        exact (anchorFactor_mul_jacobian_mul_dirichlet_eq_generalIntegrand
          anchors parameters roots hanchors hinterlace).symm
    _ = dixonAndersonGeneralAnchorFactor anchors parameters *
        (∫ roots in dixonAndersonDomain dimension anchors,
          |(andersonWeightJacobianMatrix anchors roots).det| *
            dirichletGeneralIntegrand dimension parameters
              (andersonWeightChart anchors roots)) := by
        rw [integral_const_mul]
    _ = dixonAndersonGeneralAnchorFactor anchors parameters *
        dirichletGeneralIntegral dimension parameters := by
          rw [hpullback]
    _ = _ := by rw [hdirichlet]

theorem integrableOn_dixonAndersonGeneralIntegrand
    {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (parameters : Fin (dimension + 1) → ℝ)
    (hanchors : StrictAnti anchors)
    (hparameters : ∀ anchor, 0 < parameters anchor) :
    IntegrableOn
      (dixonAndersonGeneralIntegrand anchors parameters)
      (dixonAndersonDomain dimension anchors) := by
  have hchange :=
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
      (μ := (volume : Measure (Fin dimension → ℝ)))
      (f := andersonWeightChart anchors)
      (f' := andersonWeightJacobianCLM anchors)
      (dixonAndersonDomain_measurableSet anchors)
      (fun roots hroots =>
        hasFDerivWithinAt_andersonWeightChartCLM anchors roots
          (dixonAndersonDomain dimension anchors))
      (andersonWeightChart_injective_on_interlacing anchors hanchors)
      (dirichletGeneralIntegrand dimension parameters)
  rw [andersonWeightChart_image_interlacing anchors hanchors] at hchange
  have hpullback := hchange.mp
    (integrableOn_dirichletGeneralIntegrand_all
      dimension parameters hparameters)
  have hconstant := hpullback.const_mul
    (dixonAndersonGeneralAnchorFactor anchors parameters)
  apply IntegrableOn.congr_fun hconstant
  · intro roots hinterlace
    change dixonAndersonGeneralAnchorFactor anchors parameters *
        (|(andersonWeightJacobianCLM anchors roots).det| *
          dirichletGeneralIntegrand dimension parameters
            (andersonWeightChart anchors roots)) =
      dixonAndersonGeneralIntegrand anchors parameters roots
    rw [abs_det_andersonWeightJacobianCLM]
    exact anchorFactor_mul_jacobian_mul_dirichlet_eq_generalIntegrand
      anchors parameters roots hanchors hinterlace
  · exact dixonAndersonDomain_measurableSet anchors

theorem integrableOn_dixonAndersonHalfIntegrand
    {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (hanchors : StrictAnti anchors) :
    IntegrableOn (dixonAndersonHalfIntegrand dimension anchors)
      (dixonAndersonDomain dimension anchors) := by
  have hgeneral := integrableOn_dixonAndersonGeneralIntegrand
    anchors (fun _ => (1 / 2 : ℝ)) hanchors (fun _ => by norm_num)
  apply IntegrableOn.congr_fun hgeneral
  · intro roots hinterlace
    unfold dixonAndersonGeneralIntegrand
    unfold dixonAndersonGeneralCrossProduct
    unfold dixonAndersonHalfIntegrand
    norm_num
  · exact dixonAndersonDomain_measurableSet anchors

end FibonacciRibbonKernel
