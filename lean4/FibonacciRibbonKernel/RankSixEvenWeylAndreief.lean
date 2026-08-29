import FibonacciRibbonKernel.RankFourAsymptotic

namespace FibonacciRibbonKernel

open Polynomial MeasureTheory
open scoped BigOperators

noncomputable def rankSixEvenPolynomial (index : Fin 3) : ℝ[X] :=
  match index.val with
  | 0 => 1
  | 1 => 2 * X - 1
  | _ => 4 * X ^ 2 - 2 * X - 1

theorem rankSixEvenPolynomial_natDegree (index : Fin 3) :
    (rankSixEvenPolynomial index).natDegree = index := by
  fin_cases index
  · norm_num [rankSixEvenPolynomial]
  · norm_num [rankSixEvenPolynomial]
    compute_degree
    all_goals norm_num
  · norm_num [rankSixEvenPolynomial]
    compute_degree
    all_goals norm_num

theorem rankSixEvenPolynomial_leadingCoeff (index : Fin 3) :
    (rankSixEvenPolynomial index).leadingCoeff = (2 : ℝ) ^ index.val := by
  rw [← coeff_natDegree, rankSixEvenPolynomial_natDegree]
  fin_cases index
  · norm_num [rankSixEvenPolynomial, Polynomial.coeff_sub,
      Polynomial.coeff_mul]
  · norm_num [rankSixEvenPolynomial, Polynomial.coeff_sub,
      Polynomial.coeff_mul]
    simp [Polynomial.coeff_one]
  · norm_num [rankSixEvenPolynomial, Polynomial.coeff_sub,
      Polynomial.coeff_mul]
    simp [Polynomial.coeff_one, Polynomial.coeff_X]

noncomputable def rankSixEvenAndreiefBasis
    (index : Fin 3) (angle : ℝ) : ℝ :=
  2 * Real.cos (((index.val : ℝ) + 1 / 2) * angle)

noncomputable def rankSixEvenTrigMatrix
    (angles : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun row column => rankSixEvenAndreiefBasis column (angles row)

noncomputable def rankSixEvenPolynomialMatrix
    (angles : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun row column =>
    (rankSixEvenPolynomial column).eval (Real.cos (angles row))

noncomputable def rankSixEvenRowScale
    (angles : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun row => 2 * Real.cos (angles row / 2)

theorem cos_five_half (angle : ℝ) :
    Real.cos ((5 / 2 : ℝ) * angle) =
      Real.cos (angle / 2) *
        (4 * Real.cos angle ^ 2 - 2 * Real.cos angle - 1) := by
  have hproduct := Real.two_mul_cos_mul_cos angle ((3 / 2 : ℝ) * angle)
  rw [show angle - (3 / 2 : ℝ) * angle = -(angle / 2) by ring,
    show angle + (3 / 2 : ℝ) * angle = (5 / 2 : ℝ) * angle by ring,
    Real.cos_neg] at hproduct
  rw [cos_three_half] at hproduct
  rw [show (1 / 2 : ℝ) * angle = angle / 2 by ring] at hproduct
  linarith

theorem rankSixEvenTrigMatrix_factorization (angles : Fin 3 → ℝ) :
    rankSixEvenTrigMatrix angles =
      Matrix.diagonal (rankSixEvenRowScale angles) *
        rankSixEvenPolynomialMatrix angles := by
  ext row column
  rw [Matrix.diagonal_mul]
  unfold rankSixEvenTrigMatrix rankSixEvenAndreiefBasis
    rankSixEvenRowScale rankSixEvenPolynomialMatrix
  rw [Matrix.of_apply]
  fin_cases column
  · norm_num [rankSixEvenPolynomial]
    ring
  · norm_num [rankSixEvenPolynomial]
    rw [cos_three_half]
    ring
  · norm_num [rankSixEvenPolynomial]
    rw [cos_five_half]
    ring

theorem det_rankSixEvenPolynomialMatrix (angles : Fin 3 → ℝ) :
    (rankSixEvenPolynomialMatrix angles).det =
      (Matrix.vandermonde (fun row => Real.cos (angles row))).det * 8 := by
  unfold rankSixEvenPolynomialMatrix
  rw [det_eval_matrixOfPolynomials_eq_vandermonde_mul_leading
    (fun row => Real.cos (angles row)) rankSixEvenPolynomial
    rankSixEvenPolynomial_natDegree]
  congr 1
  rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
  rw [Finset.prod_insert (by decide : (0 : Fin 3) ∉ ({1, 2} : Finset (Fin 3))),
    Finset.prod_insert (by decide : (1 : Fin 3) ∉ ({2} : Finset (Fin 3))),
    Finset.prod_singleton]
  norm_num [rankSixEvenPolynomial_leadingCoeff]

theorem det_rankSixEvenTrigMatrix (angles : Fin 3 → ℝ) :
    (rankSixEvenTrigMatrix angles).det =
      (∏ coordinate, 2 * Real.cos (angles coordinate / 2)) *
        (Matrix.vandermonde (fun row => Real.cos (angles row))).det * 8 := by
  rw [rankSixEvenTrigMatrix_factorization, Matrix.det_mul,
    Matrix.det_diagonal, det_rankSixEvenPolynomialMatrix]
  unfold rankSixEvenRowScale
  ring

theorem rankSixEvenRowScale_sq (angles : Fin 3 → ℝ) :
    (∏ coordinate, 2 * Real.cos (angles coordinate / 2)) ^ 2 =
      8 * ∏ coordinate, (1 + Real.cos (angles coordinate)) := by
  have hcoordinate : ∀ coordinate : Fin 3,
      (2 * Real.cos (angles coordinate / 2)) ^ 2 =
        2 * (1 + Real.cos (angles coordinate)) := by
    intro coordinate
    have h := Real.cos_two_mul (angles coordinate / 2)
    rw [show 2 * (angles coordinate / 2) = angles coordinate by ring] at h
    nlinarith
  calc
    (∏ coordinate, 2 * Real.cos (angles coordinate / 2)) ^ 2 =
        ∏ coordinate, (2 * Real.cos (angles coordinate / 2)) ^ 2 := by
      symm
      exact Finset.prod_pow (Finset.univ : Finset (Fin 3)) 2 _
    _ = ∏ coordinate, 2 * (1 + Real.cos (angles coordinate)) := by
      apply Finset.prod_congr rfl
      intro coordinate _hcoordinate
      exact hcoordinate coordinate
    _ = 8 * ∏ coordinate, (1 + Real.cos (angles coordinate)) := by
      rw [Finset.prod_mul_distrib]
      norm_num

theorem det_rankSixEvenTrigMatrix_sq (angles : Fin 3 → ℝ) :
    (rankSixEvenTrigMatrix angles).det ^ 2 =
      (2 : ℝ) ^ 9 * evenWeylAngleWeight 3 angles := by
  rw [det_rankSixEvenTrigMatrix]
  unfold evenWeylAngleWeight
  rw [mul_pow, mul_pow, rankSixEvenRowScale_sq,
    det_vandermonde_cos_sq, cosineVandermondeWeightIoi_eq]
  norm_num
  ring

theorem continuous_rankSixEvenAndreiefBasis (index : Fin 3) :
    Continuous (rankSixEvenAndreiefBasis index) := by
  unfold rankSixEvenAndreiefBasis
  fun_prop

noncomputable def rankSixEvenExponentialFactor
    (parameter angle : ℝ) : ℝ :=
  Real.exp (parameter * Real.cos angle)

noncomputable def rankSixEvenWeylExponentialIntegral (parameter : ℝ) : ℝ :=
  ∫ angles : Fin 3 → ℝ,
    Real.exp (parameter * cosineCubeScale angles) *
      evenWeylAngleWeight 3 angles
    ∂cosineCubeProductMeasure 3

theorem continuous_rankSixEvenExponentialFactor (parameter : ℝ) :
    Continuous (rankSixEvenExponentialFactor parameter) := by
  unfold rankSixEvenExponentialFactor
  fun_prop

theorem andreiefWeightProduct_rankSixEven
    (parameter : ℝ) (angles : Fin 3 → ℝ) :
    andreiefWeightProduct (rankSixEvenExponentialFactor parameter) angles =
      Real.exp (parameter * cosineCubeScale angles) := by
  unfold andreiefWeightProduct rankSixEvenExponentialFactor cosineCubeScale
  rw [show (∏ coordinate : Fin 3,
      Real.exp (parameter * Real.cos (angles coordinate)) ^ 2) =
      ∏ coordinate : Fin 3,
        Real.exp (2 * parameter * Real.cos (angles coordinate)) by
    apply Finset.prod_congr rfl
    intro coordinate _hcoordinate
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring]
  rw [← Real.exp_sum, ← Finset.mul_sum]
  congr 1
  ring

theorem rankSixEvenWeylExponential_andreief (parameter : ℝ) :
    (2 : ℝ) ^ 9 * rankSixEvenWeylExponentialIntegral parameter =
      (Nat.factorial 3 : ℝ) *
        (andreiefMomentMatrix
          (andreiefWeightedBasis rankSixEvenAndreiefBasis
            (rankSixEvenExponentialFactor parameter))).det := by
  have handreief := andreief_weighted_identity rankSixEvenAndreiefBasis
    (rankSixEvenExponentialFactor parameter)
    continuous_rankSixEvenAndreiefBasis
    (continuous_rankSixEvenExponentialFactor parameter)
  rw [show (fun angles : Fin 3 → ℝ =>
      andreiefWeightProduct (rankSixEvenExponentialFactor parameter) angles *
        (andreiefEvaluationMatrix rankSixEvenAndreiefBasis angles).det ^ 2) =
      fun angles => (2 : ℝ) ^ 9 *
        (Real.exp (parameter * cosineCubeScale angles) *
          evenWeylAngleWeight 3 angles) by
    funext angles
    rw [andreiefWeightProduct_rankSixEven]
    change _ * (rankSixEvenTrigMatrix angles).det ^ 2 = _
    rw [det_rankSixEvenTrigMatrix_sq]
    ring] at handreief
  unfold rankSixEvenWeylExponentialIntegral
  rw [integral_const_mul] at handreief
  exact handreief

noncomputable def rankSixEvenRealGesselMatrix
    (parameter : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun row column =>
    realBesselCosineIntegral ((row.val : ℤ) - column.val) parameter +
      realBesselCosineIntegral
        ((row.val + column.val + 1 : ℕ) : ℤ) parameter

theorem rankSixEvenWeightedBasis_product
    (parameter : ℝ) (row column : Fin 3) (angle : ℝ) :
    andreiefWeightedBasis rankSixEvenAndreiefBasis
          (rankSixEvenExponentialFactor parameter) row angle *
        andreiefWeightedBasis rankSixEvenAndreiefBasis
          (rankSixEvenExponentialFactor parameter) column angle =
      2 * (Real.exp (2 * parameter * Real.cos angle) *
        (Real.cos ((((row.val : ℤ) - column.val : ℤ) : ℝ) * angle) +
          Real.cos (((row.val + column.val + 1 : ℕ) : ℝ) * angle))) := by
  unfold andreiefWeightedBasis rankSixEvenAndreiefBasis
    rankSixEvenExponentialFactor
  have htrig := Real.two_mul_cos_mul_cos
    (((row.val : ℝ) + 1 / 2) * angle)
    (((column.val : ℝ) + 1 / 2) * angle)
  have hexp : Real.exp (parameter * Real.cos angle) *
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

theorem andreiefMomentMatrix_rankSixEven
    (parameter : ℝ) (row column : Fin 3) :
    andreiefMomentMatrix
        (andreiefWeightedBasis rankSixEvenAndreiefBasis
          (rankSixEvenExponentialFactor parameter)) row column =
      2 * rankSixEvenRealGesselMatrix parameter row column := by
  unfold andreiefMomentMatrix rankSixEvenRealGesselMatrix
  rw [show (fun angle : ℝ =>
      andreiefWeightedBasis rankSixEvenAndreiefBasis
          (rankSixEvenExponentialFactor parameter) row angle *
        andreiefWeightedBasis rankSixEvenAndreiefBasis
          (rankSixEvenExponentialFactor parameter) column angle) =
      fun angle => 2 *
        (Real.exp (2 * parameter * Real.cos angle) *
          (Real.cos ((((row.val : ℤ) - column.val : ℤ) : ℝ) * angle) +
            Real.cos (((row.val + column.val + 1 : ℕ) : ℝ) * angle))) by
    funext angle
    exact rankSixEvenWeightedBasis_product parameter row column angle,
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

theorem rankSixEvenWeylExponential_eq_realGessel (parameter : ℝ) :
    rankSixEvenWeylExponentialIntegral parameter =
      (3 / 32 : ℝ) * (rankSixEvenRealGesselMatrix parameter).det := by
  have h := rankSixEvenWeylExponential_andreief parameter
  have hmatrix :
      andreiefMomentMatrix
          (andreiefWeightedBasis rankSixEvenAndreiefBasis
            (rankSixEvenExponentialFactor parameter)) =
        (2 : ℝ) • rankSixEvenRealGesselMatrix parameter := by
    ext row column
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact andreiefMomentMatrix_rankSixEven parameter row column
  rw [hmatrix, Matrix.det_smul,
    show Fintype.card (Fin 3) = 3 by simp] at h
  norm_num at h
  linarith

end FibonacciRibbonKernel
