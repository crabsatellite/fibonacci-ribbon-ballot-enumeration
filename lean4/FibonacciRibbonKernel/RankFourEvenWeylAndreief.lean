import FibonacciRibbonKernel.RankFiveRibbonAsymptotic
import FibonacciRibbonKernel.AndreiefWeightedIdentity

namespace FibonacciRibbonKernel

open MeasureTheory
open scoped BigOperators

noncomputable def rankFourEvenAndreiefBasis
    (index : Fin 2) (angle : ℝ) : ℝ :=
  2 * Real.cos (((index.val : ℝ) + 1 / 2) * angle)

noncomputable def rankFourEvenTrigMatrix
    (angles : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun row column => rankFourEvenAndreiefBasis column (angles row)

theorem continuous_rankFourEvenAndreiefBasis (index : Fin 2) :
    Continuous (rankFourEvenAndreiefBasis index) := by
  unfold rankFourEvenAndreiefBasis
  fun_prop

theorem cos_three_half (angle : ℝ) :
    Real.cos ((3 / 2 : ℝ) * angle) =
      Real.cos ((1 / 2 : ℝ) * angle) *
        (2 * Real.cos angle - 1) := by
  calc
    Real.cos ((3 / 2 : ℝ) * angle) =
        Real.cos (3 * (angle / 2)) := by
      congr 1
      ring
    _ = 4 * Real.cos (angle / 2) ^ 3 -
        3 * Real.cos (angle / 2) := Real.cos_three_mul _
    _ = Real.cos (angle / 2) *
        (2 * Real.cos (2 * (angle / 2)) - 1) := by
      rw [Real.cos_two_mul]
      ring
    _ = Real.cos ((1 / 2 : ℝ) * angle) *
        (2 * Real.cos angle - 1) := by
      rw [show angle / 2 = (1 / 2 : ℝ) * angle by ring,
        show 2 * ((1 / 2 : ℝ) * angle) = angle by ring]

theorem det_rankFourEvenTrigMatrix (angles : Fin 2 → ℝ) :
    (rankFourEvenTrigMatrix angles).det =
      8 * Real.cos (angles 0 / 2) * Real.cos (angles 1 / 2) *
        (Real.cos (angles 1) - Real.cos (angles 0)) := by
  rw [Matrix.det_fin_two]
  unfold rankFourEvenTrigMatrix rankFourEvenAndreiefBasis
  simp only [Fin.val_zero, Fin.val_one]
  norm_num
  rw [cos_three_half, cos_three_half]
  rw [show (1 / 2 : ℝ) * angles 0 = angles 0 / 2 by ring,
    show (1 / 2 : ℝ) * angles 1 = angles 1 / 2 by ring]
  ring

theorem evenWeylAngleWeight_two_formula (angles : Fin 2 → ℝ) :
    evenWeylAngleWeight 2 angles =
      (Real.cos (angles 1) - Real.cos (angles 0)) ^ 2 *
        (1 + Real.cos (angles 0)) * (1 + Real.cos (angles 1)) := by
  unfold evenWeylAngleWeight cosineVandermondeWeight
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
  rw [Finset.prod_insert (by decide : (0 : Fin 2) ∉ ({1} : Finset (Fin 2))),
    Finset.prod_singleton]
  have hzero : Finset.Iio (0 : Fin 2) = ∅ := by decide
  have hone : Finset.Iio (1 : Fin 2) = {0} := by decide
  rw [hzero, hone]
  simp only [Finset.prod_empty, Finset.prod_singleton, one_mul]
  rw [Finset.prod_insert (by decide : (0 : Fin 2) ∉ ({1} : Finset (Fin 2))),
    Finset.prod_singleton]
  ring

theorem det_rankFourEvenTrigMatrix_sq (angles : Fin 2 → ℝ) :
    (rankFourEvenTrigMatrix angles).det ^ 2 =
      16 * evenWeylAngleWeight 2 angles := by
  rw [det_rankFourEvenTrigMatrix, evenWeylAngleWeight_two_formula]
  have hzero := Real.cos_two_mul (angles 0 / 2)
  have hone := Real.cos_two_mul (angles 1 / 2)
  rw [show 2 * (angles 0 / 2) = angles 0 by ring] at hzero
  rw [show 2 * (angles 1 / 2) = angles 1 by ring] at hone
  rw [hzero, hone]
  ring

noncomputable def rankFourEvenExponentialFactor
    (parameter angle : ℝ) : ℝ :=
  Real.exp (parameter * Real.cos angle)

noncomputable def rankFourEvenWeylExponentialIntegral
    (parameter : ℝ) : ℝ :=
  ∫ angles : Fin 2 → ℝ,
    Real.exp (parameter * cosineCubeScale angles) *
      evenWeylAngleWeight 2 angles
    ∂cosineCubeProductMeasure 2

theorem continuous_rankFourEvenExponentialFactor (parameter : ℝ) :
    Continuous (rankFourEvenExponentialFactor parameter) := by
  unfold rankFourEvenExponentialFactor
  fun_prop

theorem andreiefWeightProduct_rankFourEven
    (parameter : ℝ) (angles : Fin 2 → ℝ) :
    andreiefWeightProduct (rankFourEvenExponentialFactor parameter) angles =
      Real.exp (parameter * cosineCubeScale angles) := by
  unfold andreiefWeightProduct rankFourEvenExponentialFactor
    cosineCubeScale
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
  rw [Finset.prod_insert (by decide : (0 : Fin 2) ∉ ({1} : Finset (Fin 2))),
    Finset.prod_singleton,
    Finset.sum_insert (by decide : (0 : Fin 2) ∉ ({1} : Finset (Fin 2))),
    Finset.sum_singleton]
  rw [show Real.exp (parameter * Real.cos (angles 0)) ^ 2 =
      Real.exp (2 * parameter * Real.cos (angles 0)) by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring]
  rw [show Real.exp (parameter * Real.cos (angles 1)) ^ 2 =
      Real.exp (2 * parameter * Real.cos (angles 1)) by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring]
  rw [← Real.exp_add]
  congr 1
  ring

theorem rankFourEvenWeylExponential_andreief (parameter : ℝ) :
    16 * rankFourEvenWeylExponentialIntegral parameter =
      (Nat.factorial 2 : ℝ) *
        (andreiefMomentMatrix
          (andreiefWeightedBasis rankFourEvenAndreiefBasis
            (rankFourEvenExponentialFactor parameter))).det := by
  have handreief := andreief_weighted_identity
    rankFourEvenAndreiefBasis (rankFourEvenExponentialFactor parameter)
    continuous_rankFourEvenAndreiefBasis
    (continuous_rankFourEvenExponentialFactor parameter)
  rw [show (fun angles : Fin 2 → ℝ =>
      andreiefWeightProduct (rankFourEvenExponentialFactor parameter) angles *
        (andreiefEvaluationMatrix rankFourEvenAndreiefBasis angles).det ^ 2) =
      fun angles => 16 *
        (Real.exp (parameter * cosineCubeScale angles) *
          evenWeylAngleWeight 2 angles) by
    funext angles
    rw [andreiefWeightProduct_rankFourEven]
    change _ * (rankFourEvenTrigMatrix angles).det ^ 2 = _
    rw [det_rankFourEvenTrigMatrix_sq]
    ring] at handreief
  unfold rankFourEvenWeylExponentialIntegral
  rw [integral_const_mul] at handreief
  exact handreief

noncomputable def rankFourEvenRealGesselMatrix
    (parameter : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun row column =>
    realBesselCosineIntegral ((row.val : ℤ) - column.val) parameter +
      realBesselCosineIntegral
        ((row.val + column.val + 1 : ℕ) : ℤ) parameter

theorem rankFourEvenWeightedBasis_product
    (parameter : ℝ) (row column : Fin 2) (angle : ℝ) :
    andreiefWeightedBasis rankFourEvenAndreiefBasis
          (rankFourEvenExponentialFactor parameter) row angle *
        andreiefWeightedBasis rankFourEvenAndreiefBasis
          (rankFourEvenExponentialFactor parameter) column angle =
      2 * (Real.exp (2 * parameter * Real.cos angle) *
        (Real.cos ((((row.val : ℤ) - column.val : ℤ) : ℝ) * angle) +
          Real.cos (((row.val + column.val + 1 : ℕ) : ℝ) * angle))) := by
  unfold andreiefWeightedBasis rankFourEvenAndreiefBasis
    rankFourEvenExponentialFactor
  have htrig := Real.two_mul_cos_mul_cos
    (((row.val : ℝ) + 1 / 2) * angle)
    (((column.val : ℝ) + 1 / 2) * angle)
  have hexp :
      Real.exp (parameter * Real.cos angle) *
        Real.exp (parameter * Real.cos angle) =
      Real.exp (2 * parameter * Real.cos angle) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hdiff :
      (((row.val : ℝ) + 1 / 2) * angle -
        ((column.val : ℝ) + 1 / 2) * angle) =
      (((row.val : ℤ) - column.val : ℤ) : ℝ) * angle := by
    push_cast
    ring
  have hsum :
      (((row.val : ℝ) + 1 / 2) * angle +
        ((column.val : ℝ) + 1 / 2) * angle) =
      ((row.val + column.val + 1 : ℕ) : ℝ) * angle := by
    push_cast
    ring
  calc
    (2 * Real.cos (((row.val : ℝ) + 1 / 2) * angle) *
        Real.exp (parameter * Real.cos angle)) *
      (2 * Real.cos (((column.val : ℝ) + 1 / 2) * angle) *
        Real.exp (parameter * Real.cos angle)) =
      2 * (2 * Real.cos (((row.val : ℝ) + 1 / 2) * angle) *
        Real.cos (((column.val : ℝ) + 1 / 2) * angle)) *
          (Real.exp (parameter * Real.cos angle) *
            Real.exp (parameter * Real.cos angle)) := by ring
    _ = 2 *
        (Real.cos ((((row.val : ℝ) + 1 / 2) * angle) -
            (((column.val : ℝ) + 1 / 2) * angle)) +
          Real.cos ((((row.val : ℝ) + 1 / 2) * angle) +
            (((column.val : ℝ) + 1 / 2) * angle))) *
        (Real.exp (parameter * Real.cos angle) *
          Real.exp (parameter * Real.cos angle)) := by rw [htrig]
    _ = _ := by rw [hexp, hdiff, hsum]; ring

theorem andreiefMomentMatrix_rankFourEven
    (parameter : ℝ) (row column : Fin 2) :
    andreiefMomentMatrix
        (andreiefWeightedBasis rankFourEvenAndreiefBasis
          (rankFourEvenExponentialFactor parameter)) row column =
      2 * rankFourEvenRealGesselMatrix parameter row column := by
  unfold andreiefMomentMatrix rankFourEvenRealGesselMatrix
  rw [show (fun angle : ℝ =>
      andreiefWeightedBasis rankFourEvenAndreiefBasis
          (rankFourEvenExponentialFactor parameter) row angle *
        andreiefWeightedBasis rankFourEvenAndreiefBasis
          (rankFourEvenExponentialFactor parameter) column angle) =
      fun angle => 2 *
        (Real.exp (2 * parameter * Real.cos angle) *
          (Real.cos ((((row.val : ℤ) - column.val : ℤ) : ℝ) * angle) +
            Real.cos (((row.val + column.val + 1 : ℕ) : ℝ) * angle))) by
    funext angle
    exact rankFourEvenWeightedBasis_product parameter row column angle,
    integral_const_mul]
  rw [show (fun angle : ℝ =>
      Real.exp (2 * parameter * Real.cos angle) *
        (Real.cos ((((row.val : ℤ) - column.val : ℤ) : ℝ) * angle) +
          Real.cos (((row.val + column.val + 1 : ℕ) : ℝ) * angle))) =
      fun angle =>
        Real.exp (2 * parameter * Real.cos angle) *
            Real.cos ((((row.val : ℤ) - column.val : ℤ) : ℝ) * angle) +
          Real.exp (2 * parameter * Real.cos angle) *
            Real.cos (((row.val + column.val + 1 : ℕ) : ℝ) * angle) by
    funext angle
    ring]
  rw [integral_add]
  · rfl
  · exact integrable_continuous_cosineInterval
      (continuous_realBesselIntegrand
        ((row.val : ℤ) - column.val) parameter)
  · exact integrable_continuous_cosineInterval
      (continuous_realBesselIntegrand
        ((row.val + column.val + 1 : ℕ) : ℤ) parameter)

theorem rankFourEvenWeylExponential_eq_realGessel (parameter : ℝ) :
    2 * rankFourEvenWeylExponentialIntegral parameter =
      (rankFourEvenRealGesselMatrix parameter).det := by
  have handreief := rankFourEvenWeylExponential_andreief parameter
  have hmatrix :
      andreiefMomentMatrix
          (andreiefWeightedBasis rankFourEvenAndreiefBasis
            (rankFourEvenExponentialFactor parameter)) =
        (2 : ℝ) • rankFourEvenRealGesselMatrix parameter := by
    ext row column
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact andreiefMomentMatrix_rankFourEven parameter row column
  rw [hmatrix, Matrix.det_smul,
    show Fintype.card (Fin 2) = 2 by simp] at handreief
  norm_num at handreief
  linarith

end FibonacciRibbonKernel
