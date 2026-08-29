import FibonacciRibbonKernel.PolynomialEvaluationDeterminant

namespace FibonacciRibbonKernel

open Polynomial
open scoped BigOperators

noncomputable def cosineVandermondeWeightIoi
    (dimension : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  ∏ lower : Fin dimension,
    ∏ upper ∈ Finset.Ioi lower,
      (Real.cos (angles upper) - Real.cos (angles lower)) ^ 2

noncomputable def oddWeylAngleWeightIoi
    (dimension : ℕ) (angles : Fin dimension → ℝ) : ℝ :=
  cosineVandermondeWeightIoi dimension angles *
    ∏ coordinate, Real.sin (angles coordinate) ^ 2

noncomputable def oddTrigEvaluationMatrix
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    Matrix (Fin dimension) (Fin dimension) ℝ :=
  fun row column =>
    2 * Real.sin ((column.val + 1 : ℕ) * angles row)

noncomputable def oddPolynomialEvaluationMatrix
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    Matrix (Fin dimension) (Fin dimension) ℝ :=
  Matrix.of fun row column =>
    (oddChebyshevPolynomial column.val).eval (Real.cos (angles row))

noncomputable def oddTrigRowScale
    {dimension : ℕ} (angles : Fin dimension → ℝ) : Fin dimension → ℝ :=
  fun row => 2 * Real.sin (angles row)

theorem oddTrigEvaluationMatrix_factorization
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    oddTrigEvaluationMatrix dimension angles =
      Matrix.diagonal (oddTrigRowScale angles) *
        oddPolynomialEvaluationMatrix dimension angles := by
  ext row column
  rw [Matrix.diagonal_mul]
  unfold oddTrigEvaluationMatrix oddTrigRowScale
    oddPolynomialEvaluationMatrix
  rw [Matrix.of_apply]
  rw [← oddChebyshevPolynomial_eval_mul_sin]
  ring

theorem det_oddPolynomialEvaluationMatrix
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    (oddPolynomialEvaluationMatrix dimension angles).det =
      (Matrix.vandermonde (fun row => Real.cos (angles row))).det *
        (2 : ℝ) ^ (dimension * (dimension - 1) / 2) := by
  unfold oddPolynomialEvaluationMatrix
  rw [det_eval_matrixOfPolynomials_eq_vandermonde_mul_leading
    (fun row => Real.cos (angles row))
    (fun index : Fin dimension => oddChebyshevPolynomial index.val)
    (fun index => oddChebyshevPolynomial_natDegree index.val)]
  simp_rw [oddChebyshevPolynomial_leadingCoeff]
  rw [prod_two_pow_fin_eq]

theorem det_vandermonde_cos_sq
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    (Matrix.vandermonde (fun row => Real.cos (angles row))).det ^ 2 =
      cosineVandermondeWeightIoi dimension angles := by
  rw [Matrix.det_vandermonde]
  unfold cosineVandermondeWeightIoi
  calc
    (∏ lower : Fin dimension,
        ∏ upper ∈ Finset.Ioi lower,
          (Real.cos (angles upper) - Real.cos (angles lower))) ^ 2 =
      ∏ lower : Fin dimension,
        (∏ upper ∈ Finset.Ioi lower,
          (Real.cos (angles upper) - Real.cos (angles lower))) ^ 2 := by
        symm
        simpa using Finset.prod_pow (Finset.univ : Finset (Fin dimension))
          2 (fun lower => ∏ upper ∈ Finset.Ioi lower,
            (Real.cos (angles upper) - Real.cos (angles lower)))
    _ = _ := by
      apply Finset.prod_congr rfl
      intro lower _hlower
      symm
      exact Finset.prod_pow (Finset.Ioi lower) 2
        (fun upper => Real.cos (angles upper) - Real.cos (angles lower))

theorem det_oddTrigEvaluationMatrix
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    (oddTrigEvaluationMatrix dimension angles).det =
      ((∏ coordinate, 2 * Real.sin (angles coordinate)) *
        (Matrix.vandermonde (fun row => Real.cos (angles row))).det) *
          (2 : ℝ) ^ (dimension * (dimension - 1) / 2) := by
  rw [oddTrigEvaluationMatrix_factorization, Matrix.det_mul,
    Matrix.det_diagonal, det_oddPolynomialEvaluationMatrix]
  change (∏ coordinate, 2 * Real.sin (angles coordinate)) *
      ((Matrix.vandermonde (fun row => Real.cos (angles row))).det *
        (2 : ℝ) ^ (dimension * (dimension - 1) / 2)) = _
  ring

theorem det_oddTrigEvaluationMatrix_sq
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    (oddTrigEvaluationMatrix dimension angles).det ^ 2 =
      (2 : ℝ) ^ (dimension * (dimension + 1)) *
        oddWeylAngleWeightIoi dimension angles := by
  rw [det_oddTrigEvaluationMatrix]
  unfold oddWeylAngleWeightIoi
  have htwoProd : (∏ _coordinate : Fin dimension, (2 : ℝ) ^ 2) =
      (2 : ℝ) ^ (2 * dimension) := by
    calc
      (∏ _coordinate : Fin dimension, (2 : ℝ) ^ 2) =
          ((2 : ℝ) ^ 2) ^ dimension := by simp
      _ = (2 : ℝ) ^ (2 * dimension) := by rw [← pow_mul]
  have hrow :
      (∏ coordinate : Fin dimension,
        2 * Real.sin (angles coordinate)) ^ 2 =
      (2 : ℝ) ^ (2 * dimension) *
        ∏ coordinate, Real.sin (angles coordinate) ^ 2 := by
    calc
      (∏ coordinate : Fin dimension,
          2 * Real.sin (angles coordinate)) ^ 2 =
        ∏ coordinate : Fin dimension,
          (2 * Real.sin (angles coordinate)) ^ 2 := by
            symm
            simpa using Finset.prod_pow
              (Finset.univ : Finset (Fin dimension)) 2
              (fun coordinate => 2 * Real.sin (angles coordinate))
      _ = (∏ _coordinate : Fin dimension, (2 : ℝ) ^ 2) *
          ∏ coordinate, Real.sin (angles coordinate) ^ 2 := by
            simp_rw [mul_pow]
            rw [Finset.prod_mul_distrib]
      _ = _ := by rw [htwoProd]
  have hexponent :
      2 * dimension + 2 * (dimension * (dimension - 1) / 2) =
        dimension * (dimension + 1) := by
    have hdouble : 2 * (dimension * (dimension - 1) / 2) =
        dimension * (dimension - 1) := by
      calc
        2 * (dimension * (dimension - 1) / 2) =
            (dimension * (dimension - 1) / 2) * 2 := by omega
        _ = (∑ index ∈ Finset.range dimension, index) * 2 := by
          rw [Finset.sum_range_id]
        _ = dimension * (dimension - 1) :=
          Finset.sum_range_id_mul_two dimension
    rw [hdouble]
    by_cases hzero : dimension = 0
    · simp [hzero]
    · have hpositive : 1 ≤ dimension := Nat.one_le_iff_ne_zero.2 hzero
      calc
        2 * dimension + dimension * (dimension - 1) =
            dimension * ((dimension - 1) + 2) := by ring
        _ = dimension * (dimension + 1) := by
          congr 1
          omega
  rw [mul_pow, mul_pow, hrow, det_vandermonde_cos_sq]
  have hscalePow :
      ((2 : ℝ) ^ (dimension * (dimension - 1) / 2)) ^ 2 =
        (2 : ℝ) ^ (2 * (dimension * (dimension - 1) / 2)) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [hscalePow]
  calc
    ((2 : ℝ) ^ (2 * dimension) *
          ∏ coordinate, Real.sin (angles coordinate) ^ 2) *
        cosineVandermondeWeightIoi dimension angles *
          (2 : ℝ) ^ (2 * (dimension * (dimension - 1) / 2)) =
      ((2 : ℝ) ^ (2 * dimension) *
          (2 : ℝ) ^ (2 * (dimension * (dimension - 1) / 2))) *
        (cosineVandermondeWeightIoi dimension angles *
          ∏ coordinate, Real.sin (angles coordinate) ^ 2) := by ring
    _ = _ := by rw [← pow_add, hexponent]

theorem pairProductIoi_eq_Iio
    {dimension : ℕ} {M : Type*} [CommMonoid M]
    (function : Fin dimension → Fin dimension → M) :
    (∏ lower : Fin dimension,
      ∏ upper ∈ Finset.Ioi lower, function lower upper) =
      ∏ upper : Fin dimension,
        ∏ lower ∈ Finset.Iio upper, function lower upper := by
  let pairs : Finset (Fin dimension × Fin dimension) :=
    (Finset.univ.product Finset.univ).filter fun pair => pair.1 < pair.2
  calc
    (∏ lower : Fin dimension,
        ∏ upper ∈ Finset.Ioi lower, function lower upper) =
      ∏ pair ∈ pairs, function pair.1 pair.2 := by
        symm
        apply Finset.prod_finset_product' pairs Finset.univ
          (fun lower => Finset.Ioi lower)
        intro pair
        simp [pairs]
    _ = ∏ upper : Fin dimension,
        ∏ lower ∈ Finset.Iio upper, function lower upper := by
      apply Finset.prod_finset_product_right' pairs Finset.univ
        (fun upper => Finset.Iio upper)
      intro pair
      simp [pairs]

theorem cosineVandermondeWeightIoi_eq
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    cosineVandermondeWeightIoi dimension angles =
      cosineVandermondeWeight dimension angles := by
  unfold cosineVandermondeWeightIoi cosineVandermondeWeight
  exact pairProductIoi_eq_Iio fun lower upper =>
    (Real.cos (angles upper) - Real.cos (angles lower)) ^ 2

theorem oddWeylAngleWeightIoi_eq
    (dimension : ℕ) (angles : Fin dimension → ℝ) :
    oddWeylAngleWeightIoi dimension angles =
      oddWeylAngleWeight dimension angles := by
  unfold oddWeylAngleWeightIoi oddWeylAngleWeight
  rw [cosineVandermondeWeightIoi_eq]
  congr 1
  apply Finset.prod_congr rfl
  intro coordinate _hcoordinate
  have htrig := Real.sin_sq_add_cos_sq (angles coordinate)
  nlinarith

end FibonacciRibbonKernel
