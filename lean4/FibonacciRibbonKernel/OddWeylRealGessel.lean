import FibonacciRibbonKernel.OddWeylExponentialAndreief

namespace FibonacciRibbonKernel

open MeasureTheory

noncomputable def realBesselCosineIntegral
    (order : ℤ) (parameter : ℝ) : ℝ :=
  ∫ angle : ℝ,
    Real.exp (2 * parameter * Real.cos angle) *
      Real.cos ((order : ℝ) * angle)
    ∂cosineIntervalMeasure

noncomputable def oddRealGesselMatrix
    (dimension : ℕ) (parameter : ℝ) :
    Matrix (Fin dimension) (Fin dimension) ℝ :=
  fun row column =>
    realBesselCosineIntegral ((row.val : ℤ) - column.val) parameter -
      realBesselCosineIntegral
        ((row.val + column.val + 2 : ℕ) : ℤ) parameter

theorem continuous_realBesselIntegrand
    (order : ℤ) (parameter : ℝ) :
    Continuous (fun angle : ℝ =>
      Real.exp (2 * parameter * Real.cos angle) *
        Real.cos ((order : ℝ) * angle)) := by
  fun_prop

theorem integrable_continuous_cosineInterval
    {function : ℝ → ℝ} (hfunction : Continuous function) :
    Integrable function cosineIntervalMeasure := by
  unfold cosineIntervalMeasure
  exact hfunction.continuousOn.integrableOn_Icc.mono_set
    Set.Ioc_subset_Icc_self

theorem oddWeightedBasis_product_pointwise
    {dimension : ℕ} (hdimension : 1 ≤ dimension)
    (parameter : ℝ) (row column : Fin dimension) (angle : ℝ) :
    andreiefWeightedBasis oddAndreiefBasis
          (oddAndreiefExponentialFactor dimension parameter) row angle *
        andreiefWeightedBasis oddAndreiefBasis
          (oddAndreiefExponentialFactor dimension parameter) column angle =
      2 * Real.exp (parameter / dimension) *
        (Real.exp (2 * parameter * Real.cos angle) *
          (Real.cos ((((row.val : ℤ) - column.val : ℤ) : ℝ) * angle) -
            Real.cos (((row.val + column.val + 2 : ℕ) : ℝ) * angle))) := by
  unfold andreiefWeightedBasis oddAndreiefBasis
    oddAndreiefExponentialFactor
  have hdimensionNe : (dimension : ℝ) ≠ 0 := by positivity
  have htrig := two_mul_sin_mul_sin
    ((row.val + 1 : ℕ) : ℝ) ((column.val + 1 : ℕ) : ℝ) angle
  have hexp :
      Real.exp
          (parameter * (1 / (2 * (dimension : ℝ)) + Real.cos angle)) *
        Real.exp
          (parameter * (1 / (2 * (dimension : ℝ)) + Real.cos angle)) =
      Real.exp (parameter / dimension) *
        Real.exp (2 * parameter * Real.cos angle) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have hdiff :
      ((((row.val : ℤ) - column.val : ℤ) : ℝ)) =
        (row.val + 1 : ℝ) - (column.val + 1 : ℝ) := by
    push_cast
    ring
  have hsum :
      ((row.val + column.val + 2 : ℕ) : ℝ) =
        (row.val + 1 : ℝ) + (column.val + 1 : ℝ) := by
    push_cast
    ring
  have hcosDiff :
      Real.cos ((((row.val + 1 : ℕ) : ℝ) -
          ((column.val + 1 : ℕ) : ℝ)) * angle) =
        Real.cos ((((row.val : ℤ) - column.val : ℤ) : ℝ) * angle) := by
    rw [hdiff]
    congr 1
    push_cast
    ring
  have hcosSum :
      Real.cos ((((row.val + 1 : ℕ) : ℝ) +
          ((column.val + 1 : ℕ) : ℝ)) * angle) =
        Real.cos (((row.val + column.val + 2 : ℕ) : ℝ) * angle) := by
    rw [hsum]
    congr 1
    push_cast
    ring
  let exponential := Real.exp
    (parameter * (1 / (2 * (dimension : ℝ)) + Real.cos angle))
  calc
    2 * Real.sin ((row.val + 1 : ℕ) * angle) * exponential *
        (2 * Real.sin ((column.val + 1 : ℕ) * angle) * exponential) =
      2 * (2 * Real.sin ((row.val + 1 : ℕ) * angle) *
        Real.sin ((column.val + 1 : ℕ) * angle)) *
          (exponential * exponential) := by ring
    _ = 2 *
        (Real.cos ((((row.val + 1 : ℕ) : ℝ) -
            ((column.val + 1 : ℕ) : ℝ)) * angle) -
          Real.cos ((((row.val + 1 : ℕ) : ℝ) +
            ((column.val + 1 : ℕ) : ℝ)) * angle)) *
          (exponential * exponential) := by rw [htrig]
    _ = 2 * Real.exp (parameter / dimension) *
        (Real.exp (2 * parameter * Real.cos angle) *
          (Real.cos ((((row.val : ℤ) - column.val : ℤ) : ℝ) * angle) -
            Real.cos (((row.val + column.val + 2 : ℕ) : ℝ) * angle))) := by
      dsimp only [exponential]
      rw [hexp, hcosDiff, hcosSum]
      ring

theorem andreiefMomentMatrix_oddExponential
    {dimension : ℕ} (hdimension : 1 ≤ dimension)
    (parameter : ℝ) (row column : Fin dimension) :
    andreiefMomentMatrix
        (andreiefWeightedBasis oddAndreiefBasis
          (oddAndreiefExponentialFactor dimension parameter)) row column =
      2 * Real.exp (parameter / dimension) *
        oddRealGesselMatrix dimension parameter row column := by
  unfold andreiefMomentMatrix oddRealGesselMatrix
  rw [show (fun angle : ℝ =>
      andreiefWeightedBasis oddAndreiefBasis
          (oddAndreiefExponentialFactor dimension parameter) row angle *
        andreiefWeightedBasis oddAndreiefBasis
          (oddAndreiefExponentialFactor dimension parameter) column angle) =
      fun angle =>
        2 * Real.exp (parameter / dimension) *
          (Real.exp (2 * parameter * Real.cos angle) *
            (Real.cos ((((row.val : ℤ) - column.val : ℤ) : ℝ) * angle) -
              Real.cos (((row.val + column.val + 2 : ℕ) : ℝ) * angle))) by
    funext angle
    exact oddWeightedBasis_product_pointwise
      hdimension parameter row column angle]
  rw [integral_const_mul]
  rw [show (fun angle : ℝ =>
      Real.exp (2 * parameter * Real.cos angle) *
        (Real.cos ((((row.val : ℤ) - column.val : ℤ) : ℝ) * angle) -
          Real.cos (((row.val + column.val + 2 : ℕ) : ℝ) * angle))) =
      fun angle =>
        (Real.exp (2 * parameter * Real.cos angle) *
          Real.cos ((((row.val : ℤ) - column.val : ℤ) : ℝ) * angle)) -
        (Real.exp (2 * parameter * Real.cos angle) *
          Real.cos (((row.val + column.val + 2 : ℕ) : ℝ) * angle)) by
    funext angle
    ring]
  rw [integral_sub]
  · rfl
  · exact integrable_continuous_cosineInterval
      (continuous_realBesselIntegrand
        ((row.val : ℤ) - column.val) parameter)
  · exact integrable_continuous_cosineInterval
      (continuous_realBesselIntegrand
        ((row.val + column.val + 2 : ℕ) : ℤ) parameter)

theorem andreiefMomentMatrix_oddExponential_eq_smul
    {dimension : ℕ} (hdimension : 1 ≤ dimension)
    (parameter : ℝ) :
    andreiefMomentMatrix
        (andreiefWeightedBasis (oddAndreiefBasis (dimension := dimension))
          (oddAndreiefExponentialFactor dimension parameter)) =
      (2 * Real.exp (parameter / dimension)) •
        oddRealGesselMatrix dimension parameter := by
  ext row column
  rw [andreiefMomentMatrix_oddExponential hdimension]
  rfl

theorem det_andreiefMomentMatrix_oddExponential
    {dimension : ℕ} (hdimension : 1 ≤ dimension)
    (parameter : ℝ) :
    (andreiefMomentMatrix
      (andreiefWeightedBasis (oddAndreiefBasis (dimension := dimension))
        (oddAndreiefExponentialFactor dimension parameter))).det =
      (2 : ℝ) ^ dimension * Real.exp parameter *
        (oddRealGesselMatrix dimension parameter).det := by
  rw [andreiefMomentMatrix_oddExponential_eq_smul hdimension]
  rw [Matrix.det_smul (oddRealGesselMatrix dimension parameter)
    (2 * Real.exp (parameter / dimension)),
    Fintype.card_fin, mul_pow]
  have hdimensionNe : (dimension : ℝ) ≠ 0 := by positivity
  have hexp : Real.exp (parameter / dimension) ^ dimension =
      Real.exp parameter := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [hexp]

theorem oddWeylExponentialIntegral_eq_realGessel
    {dimension : ℕ} (hdimension : 1 ≤ dimension)
    (parameter : ℝ) :
    (2 : ℝ) ^ (dimension * (dimension + 1)) *
        oddWeylExponentialIntegral dimension parameter =
      (dimension.factorial : ℝ) * (2 : ℝ) ^ dimension *
        Real.exp parameter *
          (oddRealGesselMatrix dimension parameter).det := by
  rw [oddWeylExponentialIntegral_andreief hdimension,
    det_andreiefMomentMatrix_oddExponential hdimension]
  ring

end FibonacciRibbonKernel
