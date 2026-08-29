import FibonacciRibbonKernel.RankSixAsymptotic

namespace FibonacciRibbonKernel

open Polynomial MeasureTheory
open scoped BigOperators

noncomputable def evenChebyshevPolynomial (index : ℕ) : ℝ[X] :=
  Polynomial.Chebyshev.U ℝ (index : ℤ) -
    Polynomial.Chebyshev.U ℝ ((index : ℤ) - 1)

theorem evenChebyshevPolynomial_zero :
    evenChebyshevPolynomial 0 = 1 := by
  simp [evenChebyshevPolynomial, Polynomial.Chebyshev.U_zero,
    Polynomial.Chebyshev.U_neg_one]

theorem evenChebyshevPolynomial_one :
    evenChebyshevPolynomial 1 = 2 * X - 1 := by
  simp [evenChebyshevPolynomial, Polynomial.Chebyshev.U_one,
    Polynomial.Chebyshev.U_zero]

theorem evenChebyshevPolynomial_natDegree (index : ℕ) :
    (evenChebyshevPolynomial index).natDegree = index := by
  cases index with
  | zero => simp [evenChebyshevPolynomial_zero]
  | succ index =>
      unfold evenChebyshevPolynomial
      norm_num
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
      · exact Polynomial.Chebyshev.natDegree_U_natCast ℝ (index + 1)
      · rw [Polynomial.Chebyshev.natDegree_U_natCast ℝ index]
        change index <
          (Polynomial.Chebyshev.U ℝ ((index + 1 : ℕ) : ℤ)).natDegree
        rw [Polynomial.Chebyshev.natDegree_U_natCast]
        omega

theorem evenChebyshevPolynomial_leadingCoeff (index : ℕ) :
    (evenChebyshevPolynomial index).leadingCoeff = (2 : ℝ) ^ index := by
  cases index with
  | zero => simp [evenChebyshevPolynomial_zero]
  | succ index =>
      unfold evenChebyshevPolynomial
      norm_num
      rw [Polynomial.leadingCoeff_sub_of_degree_lt]
      · exact Polynomial.Chebyshev.leadingCoeff_U_natCast ℝ (index + 1)
      · exact Polynomial.degree_lt_degree (by
          rw [Polynomial.Chebyshev.natDegree_U_natCast ℝ index]
          change index <
            (Polynomial.Chebyshev.U ℝ ((index + 1 : ℕ) : ℤ)).natDegree
          rw [Polynomial.Chebyshev.natDegree_U_natCast]
          omega)

theorem evenChebyshevPolynomial_add_two (index : ℕ) :
    evenChebyshevPolynomial (index + 2) =
      2 * X * evenChebyshevPolynomial (index + 1) -
        evenChebyshevPolynomial index := by
  unfold evenChebyshevPolynomial
  push_cast
  rw [Polynomial.Chebyshev.U_add_two]
  have h := Polynomial.Chebyshev.U_add_one ℝ (index : ℤ)
  rw [show (index : ℤ) + 1 - 1 = (index : ℤ) by omega,
    show (index : ℤ) + 2 - 1 = (index : ℤ) + 1 by omega]
  linear_combination -h

theorem evenChebyshevPolynomial_eval_half_cos
    (index : ℕ) (angle : ℝ) :
    (evenChebyshevPolynomial index).eval (Real.cos angle) *
        (2 * Real.cos (angle / 2)) =
      2 * Real.cos (((index : ℝ) + 1 / 2) * angle) := by
  induction index using Nat.twoStepInduction with
  | zero =>
      rw [evenChebyshevPolynomial_zero]
      norm_num
      congr 2
      ring
  | one =>
      rw [evenChebyshevPolynomial_one]
      norm_num
      rw [cos_three_half]
      ring
  | more index hzero hone =>
      rw [evenChebyshevPolynomial_add_two]
      simp only [eval_sub, eval_mul, eval_ofNat, eval_X]
      rw [show ((index + 2 : ℕ) : ℝ) + 1 / 2 =
          ((index : ℝ) + 5 / 2) by push_cast; ring]
      rw [show ((index + 1 : ℕ) : ℝ) + 1 / 2 =
          ((index : ℝ) + 3 / 2) by push_cast; ring] at hone
      rw [show (index : ℝ) + 1 / 2 =
          ((index : ℝ) + 1 / 2) by rfl] at hzero
      have htrig := Real.two_mul_cos_mul_cos angle
        (((index : ℝ) + 3 / 2) * angle)
      rw [show angle - ((index : ℝ) + 3 / 2) * angle =
          -(((index : ℝ) + 1 / 2) * angle) by ring,
        show angle + ((index : ℝ) + 3 / 2) * angle =
          ((index : ℝ) + 5 / 2) * angle by ring,
        Real.cos_neg] at htrig
      calc
        (2 * Real.cos angle *
              (evenChebyshevPolynomial (index + 1)).eval (Real.cos angle) -
            (evenChebyshevPolynomial index).eval (Real.cos angle)) *
              (2 * Real.cos (angle / 2)) =
          2 * Real.cos angle *
              ((evenChebyshevPolynomial (index + 1)).eval (Real.cos angle) *
                (2 * Real.cos (angle / 2))) -
            (evenChebyshevPolynomial index).eval (Real.cos angle) *
              (2 * Real.cos (angle / 2)) := by ring
        _ = 2 * Real.cos angle *
              (2 * Real.cos (((index : ℝ) + 3 / 2) * angle)) -
            2 * Real.cos (((index : ℝ) + 1 / 2) * angle) := by
          rw [hone, hzero]
        _ = _ := by linarith

noncomputable def evenAndreiefBasis
    {dimension : ℕ} (index : Fin dimension) (angle : ℝ) : ℝ :=
  2 * Real.cos (((index.val : ℝ) + 1 / 2) * angle)

noncomputable def evenTrigEvaluationMatrix
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    Matrix (Fin dimension) (Fin dimension) ℝ :=
  fun row column => evenAndreiefBasis column (angles row)

noncomputable def evenPolynomialEvaluationMatrix
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    Matrix (Fin dimension) (Fin dimension) ℝ :=
  Matrix.of fun row column =>
    (evenChebyshevPolynomial column.val).eval (Real.cos (angles row))

noncomputable def evenTrigRowScale
    {dimension : ℕ} (angles : Fin dimension → ℝ) : Fin dimension → ℝ :=
  fun row => 2 * Real.cos (angles row / 2)

theorem evenTrigEvaluationMatrix_factorization
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    evenTrigEvaluationMatrix dimension angles =
      Matrix.diagonal (evenTrigRowScale angles) *
        evenPolynomialEvaluationMatrix dimension angles := by
  ext row column
  rw [Matrix.diagonal_mul]
  unfold evenTrigEvaluationMatrix evenAndreiefBasis evenTrigRowScale
    evenPolynomialEvaluationMatrix
  rw [Matrix.of_apply]
  calc
    2 * Real.cos (((column.val : ℝ) + 1 / 2) * angles row) =
        (evenChebyshevPolynomial column.val).eval (Real.cos (angles row)) *
          (2 * Real.cos (angles row / 2)) :=
      (evenChebyshevPolynomial_eval_half_cos column.val (angles row)).symm
    _ = _ := by ring

theorem det_evenPolynomialEvaluationMatrix
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    (evenPolynomialEvaluationMatrix dimension angles).det =
      (Matrix.vandermonde (fun row => Real.cos (angles row))).det *
        (2 : ℝ) ^ (dimension * (dimension - 1) / 2) := by
  unfold evenPolynomialEvaluationMatrix
  rw [det_eval_matrixOfPolynomials_eq_vandermonde_mul_leading
    (fun row => Real.cos (angles row))
    (fun index : Fin dimension => evenChebyshevPolynomial index.val)
    (fun index => evenChebyshevPolynomial_natDegree index.val)]
  simp_rw [evenChebyshevPolynomial_leadingCoeff]
  rw [prod_two_pow_fin_eq]

theorem evenTrigRowScale_sq
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    (∏ coordinate, 2 * Real.cos (angles coordinate / 2)) ^ 2 =
      (2 : ℝ) ^ dimension *
        ∏ coordinate, (1 + Real.cos (angles coordinate)) := by
  have hc : ∀ coordinate : Fin dimension,
      (2 * Real.cos (angles coordinate / 2)) ^ 2 =
        2 * (1 + Real.cos (angles coordinate)) := by
    intro coordinate
    have h := Real.cos_two_mul (angles coordinate / 2)
    rw [show 2 * (angles coordinate / 2) = angles coordinate by ring] at h
    nlinarith
  calc
    _ = ∏ coordinate, (2 * Real.cos (angles coordinate / 2)) ^ 2 := by
      symm
      exact Finset.prod_pow (Finset.univ : Finset (Fin dimension)) 2 _
    _ = ∏ coordinate, 2 * (1 + Real.cos (angles coordinate)) := by
      apply Finset.prod_congr rfl
      intro coordinate _
      exact hc coordinate
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

theorem det_evenTrigEvaluationMatrix_sq
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    (evenTrigEvaluationMatrix dimension angles).det ^ 2 =
      (2 : ℝ) ^ (dimension ^ 2) * evenWeylAngleWeight dimension angles := by
  rw [evenTrigEvaluationMatrix_factorization, Matrix.det_mul,
    Matrix.det_diagonal, det_evenPolynomialEvaluationMatrix,
    mul_pow, mul_pow]
  change (∏ coordinate, 2 * Real.cos (angles coordinate / 2)) ^ 2 *
      ((Matrix.vandermonde (fun row => Real.cos (angles row))).det ^ 2 *
        ((2 : ℝ) ^ (dimension * (dimension - 1) / 2)) ^ 2) = _
  rw [evenTrigRowScale_sq, det_vandermonde_cos_sq,
    cosineVandermondeWeightIoi_eq]
  unfold evenWeylAngleWeight
  have hexponent : dimension +
      2 * (dimension * (dimension - 1) / 2) = dimension ^ 2 := by
    have hdouble : 2 * (dimension * (dimension - 1) / 2) =
        dimension * (dimension - 1) := by
      calc
        _ = (dimension * (dimension - 1) / 2) * 2 := by omega
        _ = (∑ index ∈ Finset.range dimension, index) * 2 := by
          rw [Finset.sum_range_id]
        _ = _ := Finset.sum_range_id_mul_two dimension
    rw [hdouble]
    by_cases hz : dimension = 0
    · simp [hz]
    · have hp : 1 ≤ dimension := Nat.one_le_iff_ne_zero.2 hz
      calc
        dimension + dimension * (dimension - 1) =
            dimension * ((dimension - 1) + 1) := by ring
        _ = dimension * dimension := by rw [Nat.sub_add_cancel hp]
        _ = dimension ^ 2 := by rw [pow_two]
  rw [show ((2 : ℝ) ^ (dimension * (dimension - 1) / 2)) ^ 2 =
      (2 : ℝ) ^ (2 * (dimension * (dimension - 1) / 2)) by
    rw [← pow_mul]
    congr 1
    omega]
  calc
    ((2 : ℝ) ^ dimension *
          ∏ coordinate, (1 + Real.cos (angles coordinate))) *
        (cosineVandermondeWeight dimension angles *
          (2 : ℝ) ^ (2 * (dimension * (dimension - 1) / 2))) =
      ((2 : ℝ) ^ dimension *
          (2 : ℝ) ^ (2 * (dimension * (dimension - 1) / 2))) *
        (cosineVandermondeWeight dimension angles *
          ∏ coordinate, (1 + Real.cos (angles coordinate))) := by ring
    _ = (2 : ℝ) ^
          (dimension + 2 * (dimension * (dimension - 1) / 2)) *
        (cosineVandermondeWeight dimension angles *
          ∏ coordinate, (1 + Real.cos (angles coordinate))) := by
      rw [← pow_add]
    _ = _ := by rw [hexponent]

theorem continuous_evenAndreiefBasis
    {dimension : ℕ} (index : Fin dimension) :
    Continuous (evenAndreiefBasis index) := by
  unfold evenAndreiefBasis
  fun_prop

noncomputable def evenAndreiefExponentialFactor
    (parameter angle : ℝ) : ℝ :=
  Real.exp (parameter * Real.cos angle)

noncomputable def evenWeylExponentialIntegral
    (dimension : ℕ) (parameter : ℝ) : ℝ :=
  ∫ angles : Fin dimension → ℝ,
    Real.exp (parameter * cosineCubeScale angles) *
      evenWeylAngleWeight dimension angles
    ∂cosineCubeProductMeasure dimension

theorem continuous_evenAndreiefExponentialFactor (parameter : ℝ) :
    Continuous (evenAndreiefExponentialFactor parameter) := by
  unfold evenAndreiefExponentialFactor
  fun_prop

theorem andreiefWeightProduct_evenExponential
    (dimension : ℕ) (parameter : ℝ) (angles : Fin dimension → ℝ) :
    andreiefWeightProduct (evenAndreiefExponentialFactor parameter) angles =
      Real.exp (parameter * cosineCubeScale angles) := by
  unfold andreiefWeightProduct evenAndreiefExponentialFactor cosineCubeScale
  rw [show (∏ coordinate : Fin dimension,
      Real.exp (parameter * Real.cos (angles coordinate)) ^ 2) =
      ∏ coordinate, Real.exp (2 * parameter * Real.cos (angles coordinate)) by
    apply Finset.prod_congr rfl
    intro coordinate _
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring]
  rw [← Real.exp_sum, ← Finset.mul_sum]
  congr 1
  ring

theorem evenWeylExponentialIntegral_andreief
    (dimension : ℕ) (parameter : ℝ) :
    (2 : ℝ) ^ (dimension ^ 2) *
        evenWeylExponentialIntegral dimension parameter =
      (dimension.factorial : ℝ) *
        (andreiefMomentMatrix
          (andreiefWeightedBasis (evenAndreiefBasis (dimension := dimension))
            (evenAndreiefExponentialFactor parameter))).det := by
  have ha := andreief_weighted_identity
    (evenAndreiefBasis (dimension := dimension))
    (evenAndreiefExponentialFactor parameter)
    continuous_evenAndreiefBasis
    (continuous_evenAndreiefExponentialFactor parameter)
  rw [show (fun angles : Fin dimension → ℝ =>
      andreiefWeightProduct (evenAndreiefExponentialFactor parameter) angles *
        (andreiefEvaluationMatrix evenAndreiefBasis angles).det ^ 2) =
      fun angles => (2 : ℝ) ^ (dimension ^ 2) *
        (Real.exp (parameter * cosineCubeScale angles) *
          evenWeylAngleWeight dimension angles) by
    funext angles
    rw [andreiefWeightProduct_evenExponential,
      show andreiefEvaluationMatrix evenAndreiefBasis angles =
          evenTrigEvaluationMatrix dimension angles by rfl,
      det_evenTrigEvaluationMatrix_sq]
    ring] at ha
  unfold evenWeylExponentialIntegral
  rw [integral_const_mul] at ha
  exact ha

noncomputable def evenRealGesselMatrix
    (dimension : ℕ) (parameter : ℝ) :
    Matrix (Fin dimension) (Fin dimension) ℝ :=
  fun row column =>
    realBesselCosineIntegral ((row.val : ℤ) - column.val) parameter +
      realBesselCosineIntegral
        ((row.val + column.val + 1 : ℕ) : ℤ) parameter

theorem andreiefMomentMatrix_evenExponential
    {dimension : ℕ} (parameter : ℝ) (row column : Fin dimension) :
    andreiefMomentMatrix
        (andreiefWeightedBasis evenAndreiefBasis
          (evenAndreiefExponentialFactor parameter)) row column =
      2 * evenRealGesselMatrix dimension parameter row column := by
  unfold andreiefMomentMatrix evenRealGesselMatrix
  rw [show (fun angle : ℝ =>
      andreiefWeightedBasis evenAndreiefBasis
          (evenAndreiefExponentialFactor parameter) row angle *
        andreiefWeightedBasis evenAndreiefBasis
          (evenAndreiefExponentialFactor parameter) column angle) =
      fun angle => 2 *
        (Real.exp (2 * parameter * Real.cos angle) *
          (Real.cos ((((row.val : ℤ) - column.val : ℤ) : ℝ) * angle) +
            Real.cos (((row.val + column.val + 1 : ℕ) : ℝ) * angle))) by
    funext angle
    unfold andreiefWeightedBasis evenAndreiefBasis
      evenAndreiefExponentialFactor
    have ht := Real.two_mul_cos_mul_cos
      (((row.val : ℝ) + 1 / 2) * angle)
      (((column.val : ℝ) + 1 / 2) * angle)
    have he : Real.exp (parameter * Real.cos angle) *
        Real.exp (parameter * Real.cos angle) =
        Real.exp (2 * parameter * Real.cos angle) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hd : (((row.val : ℝ) + 1 / 2) * angle -
        ((column.val : ℝ) + 1 / 2) * angle) =
        (((row.val : ℤ) - column.val : ℤ) : ℝ) * angle := by
      push_cast
      ring
    have hs : (((row.val : ℝ) + 1 / 2) * angle +
        ((column.val : ℝ) + 1 / 2) * angle) =
        ((row.val + column.val + 1 : ℕ) : ℝ) * angle := by
      push_cast
      ring
    calc
      _ = 2 * (2 * Real.cos (((row.val : ℝ) + 1 / 2) * angle) *
          Real.cos (((column.val : ℝ) + 1 / 2) * angle)) *
          (Real.exp (parameter * Real.cos angle) *
            Real.exp (parameter * Real.cos angle)) := by ring
      _ = 2 * (Real.cos ((((row.val : ℝ) + 1 / 2) * angle) -
            (((column.val : ℝ) + 1 / 2) * angle)) +
          Real.cos ((((row.val : ℝ) + 1 / 2) * angle) +
            (((column.val : ℝ) + 1 / 2) * angle))) *
          (Real.exp (parameter * Real.cos angle) *
            Real.exp (parameter * Real.cos angle)) := by rw [ht]
      _ = _ := by rw [he, hd, hs]; ring,
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
    ring, integral_add]
  · rfl
  · exact integrable_continuous_cosineInterval
      (continuous_realBesselIntegrand ((row.val : ℤ) - column.val) parameter)
  · exact integrable_continuous_cosineInterval
      (continuous_realBesselIntegrand
        ((row.val + column.val + 1 : ℕ) : ℤ) parameter)

theorem evenWeylExponentialIntegral_eq_realGessel
    (dimension : ℕ) (parameter : ℝ) :
    (2 : ℝ) ^ (dimension ^ 2) *
        evenWeylExponentialIntegral dimension parameter =
      (dimension.factorial : ℝ) * (2 : ℝ) ^ dimension *
        (evenRealGesselMatrix dimension parameter).det := by
  rw [evenWeylExponentialIntegral_andreief]
  have hm :
      andreiefMomentMatrix
          (andreiefWeightedBasis (evenAndreiefBasis (dimension := dimension))
            (evenAndreiefExponentialFactor parameter)) =
        (2 : ℝ) • evenRealGesselMatrix dimension parameter := by
    ext row column
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact andreiefMomentMatrix_evenExponential parameter row column
  rw [hm, Matrix.det_smul, Fintype.card_fin]
  ring

end FibonacciRibbonKernel
