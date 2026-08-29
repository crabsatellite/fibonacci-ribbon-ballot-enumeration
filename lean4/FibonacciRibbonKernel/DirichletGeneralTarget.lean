import FibonacciRibbonKernel.DirichletHalfSplit
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped Classical BigOperators

noncomputable def dirichletBarycentric (dimension : ℕ)
    (coordinates : Fin dimension → ℝ) : Fin (dimension + 1) → ℝ :=
  Fin.lastCases (1 - ∑ index, coordinates index) coordinates

@[simp] theorem dirichletBarycentric_castSucc {dimension : ℕ}
    (coordinates : Fin dimension → ℝ) (index : Fin dimension) :
    dirichletBarycentric dimension coordinates index.castSucc =
      coordinates index := by
  simp [dirichletBarycentric]

@[simp] theorem dirichletBarycentric_last {dimension : ℕ}
    (coordinates : Fin dimension → ℝ) :
    dirichletBarycentric dimension coordinates (Fin.last dimension) =
      1 - ∑ index, coordinates index := by
  simp [dirichletBarycentric]

noncomputable def dirichletGeneralIntegrand (dimension : ℕ)
    (parameters : Fin (dimension + 1) → ℝ)
    (coordinates : Fin dimension → ℝ) : ℝ :=
  ∏ anchor : Fin (dimension + 1),
    dirichletBarycentric dimension coordinates anchor ^
      (parameters anchor - 1)

noncomputable def dirichletGeneralIntegral (dimension : ℕ)
    (parameters : Fin (dimension + 1) → ℝ) : ℝ :=
  ∫ coordinates in dirichletOpenSimplex dimension,
    dirichletGeneralIntegrand dimension parameters coordinates

noncomputable def expectedDirichletGeneralIntegral (dimension : ℕ)
    (parameters : Fin (dimension + 1) → ℝ) : ℝ :=
  (∏ anchor, Real.Gamma (parameters anchor)) /
    Real.Gamma (∑ anchor, parameters anchor)

def DirichletGeneralEvaluation (dimension : ℕ)
    (parameters : Fin (dimension + 1) → ℝ) : Prop :=
  dirichletGeneralIntegral dimension parameters =
    expectedDirichletGeneralIntegral dimension parameters

theorem dirichletBarycentric_pos_of_mem {dimension : ℕ}
    {coordinates : Fin dimension → ℝ}
    (hcoordinates : coordinates ∈ dirichletOpenSimplex dimension)
    (anchor : Fin (dimension + 1)) :
    0 < dirichletBarycentric dimension coordinates anchor := by
  cases anchor using Fin.lastCases with
  | last =>
      rw [dirichletBarycentric_last]
      exact sub_pos.mpr hcoordinates.2
  | cast index =>
      rw [dirichletBarycentric_castSucc]
      exact hcoordinates.1 index

theorem dirichletGeneralIntegrand_pos_of_mem {dimension : ℕ}
    {parameters : Fin (dimension + 1) → ℝ}
    {coordinates : Fin dimension → ℝ}
    (hcoordinates : coordinates ∈ dirichletOpenSimplex dimension) :
    0 < dirichletGeneralIntegrand dimension parameters coordinates := by
  unfold dirichletGeneralIntegrand
  apply Finset.prod_pos
  intro anchor hanchor
  exact Real.rpow_pos_of_pos
    (dirichletBarycentric_pos_of_mem hcoordinates anchor) _

theorem continuousOn_dirichletGeneralIntegrand (dimension : ℕ)
    (parameters : Fin (dimension + 1) → ℝ) :
    ContinuousOn (dirichletGeneralIntegrand dimension parameters)
      (dirichletOpenSimplex dimension) := by
  unfold dirichletGeneralIntegrand
  apply continuousOn_finsetProd Finset.univ
  intro anchor hanchor
  apply continuousOn_of_forall_continuousAt
  intro coordinates hcoordinates
  have hcontinuous : ContinuousAt
      (fun current : Fin dimension → ℝ =>
        dirichletBarycentric dimension current anchor) coordinates := by
    cases anchor using Fin.lastCases with
    | last =>
        simp only [dirichletBarycentric_last]
        fun_prop
    | cast index =>
        simp only [dirichletBarycentric_castSucc]
        exact (continuous_apply index).continuousAt
  exact hcontinuous.rpow_const
    (Or.inl (dirichletBarycentric_pos_of_mem
      hcoordinates anchor).ne')

theorem dirichletGeneralIntegrand_zero
    (parameters : Fin 1 → ℝ) :
    dirichletGeneralIntegrand 0 parameters = fun _ => 1 := by
  funext coordinates
  unfold dirichletGeneralIntegrand
  rw [Fin.prod_univ_one]
  rw [show (0 : Fin 1) = Fin.last 0 by rfl,
    dirichletBarycentric_last]
  simp

theorem dirichletGeneralIntegral_zero
    (parameters : Fin 1 → ℝ) :
    dirichletGeneralIntegral 0 parameters = 1 := by
  unfold dirichletGeneralIntegral
  rw [dirichletOpenSimplex_zero, setIntegral_univ,
    dirichletGeneralIntegrand_zero]
  have hvolume : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
    rw [Measure.volume_pi_eq_dirac (fun row : Fin 0 => Fin.elim0 row)]
    simp
  rw [integral_const, measureReal_def, hvolume]
  norm_num

theorem expectedDirichletGeneralIntegral_zero
    (parameters : Fin 1 → ℝ) (hparameters : 0 < parameters 0) :
    expectedDirichletGeneralIntegral 0 parameters = 1 := by
  unfold expectedDirichletGeneralIntegral
  rw [Fin.prod_univ_one, Fin.sum_univ_one]
  exact div_self (by positivity)

theorem dirichletGeneralEvaluation_zero
    (parameters : Fin 1 → ℝ) (hparameters : 0 < parameters 0) :
    DirichletGeneralEvaluation 0 parameters := by
  unfold DirichletGeneralEvaluation
  rw [dirichletGeneralIntegral_zero,
    expectedDirichletGeneralIntegral_zero parameters hparameters]

@[simp] theorem dirichletBarycentric_dirichletConsTransform_zero
    (dimension : ℕ) (input : ℝ × (Fin dimension → ℝ)) :
    dirichletBarycentric (dimension + 1)
      (dirichletConsTransform dimension input) 0 = input.1 := by
  change dirichletBarycentric (dimension + 1)
    (dirichletConsTransform dimension input)
      (Fin.castSucc (0 : Fin (dimension + 1))) = input.1
  rw [dirichletBarycentric_castSucc]
  exact dirichletConsTransform_zero dimension input

@[simp] theorem dirichletBarycentric_dirichletConsTransform_succ
    (dimension : ℕ) (input : ℝ × (Fin dimension → ℝ))
    (anchor : Fin (dimension + 1)) :
    dirichletBarycentric (dimension + 1)
        (dirichletConsTransform dimension input) anchor.succ =
      (1 - input.1) *
        dirichletBarycentric dimension input.2 anchor := by
  cases anchor using Fin.lastCases with
  | last =>
      rw [show (Fin.last dimension).succ = Fin.last (dimension + 1) by rfl]
      rw [dirichletBarycentric_last, dirichletConsTransform_residual,
        dirichletBarycentric_last]
  | cast index =>
      rw [show index.castSucc.succ = index.succ.castSucc by rfl]
      rw [dirichletBarycentric_castSucc, dirichletConsTransform_succ,
        dirichletBarycentric_castSucc]

theorem dirichletGeneral_tail_product_scale
    (dimension : ℕ) (scale : ℝ)
    (parameters : Fin (dimension + 1) → ℝ)
    (coordinates : Fin dimension → ℝ)
    (hscale : 0 < scale)
    (hcoordinates : coordinates ∈ dirichletOpenSimplex dimension) :
    (∏ anchor : Fin (dimension + 1),
        (scale * dirichletBarycentric dimension coordinates anchor) ^
          (parameters anchor - 1)) =
      scale ^ ((∑ anchor, parameters anchor) - (dimension + 1 : ℕ)) *
        dirichletGeneralIntegrand dimension parameters coordinates := by
  simp_rw [Real.mul_rpow hscale.le
    (dirichletBarycentric_pos_of_mem hcoordinates _).le]
  rw [Finset.prod_mul_distrib]
  rw [← Real.rpow_sum_of_pos hscale
    (fun anchor : Fin (dimension + 1) => parameters anchor - 1)
    Finset.univ]
  unfold dirichletGeneralIntegrand
  congr 1
  rw [Finset.sum_sub_distrib]
  simp

theorem dirichletGeneralIntegrand_cons_scale
    (dimension : ℕ)
    (parameters : Fin (dimension + 2) → ℝ)
    (input : ℝ × (Fin dimension → ℝ))
    (hfirst : input.1 ∈ Set.Ioo (0 : ℝ) 1)
    (htail : input.2 ∈ dirichletOpenSimplex dimension) :
    dirichletGeneralIntegrand (dimension + 1) parameters
        (dirichletConsTransform dimension input) =
      input.1 ^ (parameters 0 - 1) *
        (1 - input.1) ^
          ((∑ anchor : Fin (dimension + 1), parameters anchor.succ) -
            (dimension + 1 : ℕ)) *
          dirichletGeneralIntegrand dimension (Fin.tail parameters) input.2 := by
  have hscale : 0 < 1 - input.1 := sub_pos.mpr hfirst.2
  unfold dirichletGeneralIntegrand
  rw [Fin.prod_univ_succ]
  simp only [dirichletBarycentric_dirichletConsTransform_zero,
    dirichletBarycentric_dirichletConsTransform_succ]
  change input.1 ^ (parameters 0 - 1) *
      (∏ anchor : Fin (dimension + 1),
        ((1 - input.1) *
          dirichletBarycentric dimension input.2 anchor) ^
            ((Fin.tail parameters) anchor - 1)) = _
  rw [dirichletGeneral_tail_product_scale dimension
    (1 - input.1) (Fin.tail parameters) input.2 hscale htail]
  change input.1 ^ (parameters 0 - 1) *
      ((1 - input.1) ^
          ((∑ anchor : Fin (dimension + 1),
            (Fin.tail parameters) anchor) - (dimension + 1 : ℕ)) *
        dirichletGeneralIntegrand dimension
          (Fin.tail parameters) input.2) =
    (input.1 ^ (parameters 0 - 1) *
      (1 - input.1) ^
        ((∑ anchor : Fin (dimension + 1),
          (Fin.tail parameters) anchor) - (dimension + 1 : ℕ))) *
      dirichletGeneralIntegrand dimension
        (Fin.tail parameters) input.2
  ring

end FibonacciRibbonKernel
