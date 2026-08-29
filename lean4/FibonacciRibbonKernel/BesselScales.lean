import FibonacciRibbonKernel.BesselSystem

namespace FibonacciRibbonKernel

/-- Change-of-basis polynomial `(T+1)^p(T-1)^q`. -/
noncomputable def signedBesselPolynomial (plusPower minusPower : ℕ) : Polynomial ℚ :=
  (Polynomial.X + Polynomial.C 1) ^ plusPower *
    (Polynomial.X - Polynomial.C 1) ^ minusPower

theorem derivative_signedBesselPolynomial (plusPower minusPower : ℕ) :
    (signedBesselPolynomial plusPower minusPower).derivative =
      Polynomial.C (plusPower : ℚ) *
          (Polynomial.X + Polynomial.C 1) ^ (plusPower - 1) *
          (Polynomial.X - Polynomial.C 1) ^ minusPower +
        Polynomial.C (minusPower : ℚ) *
          (Polynomial.X + Polynomial.C 1) ^ plusPower *
          (Polynomial.X - Polynomial.C 1) ^ (minusPower - 1) := by
  unfold signedBesselPolynomial
  rw [Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_pow]
  have hplus : (Polynomial.X + Polynomial.C (1 : ℚ)).derivative = 1 := by
    simp
  have hminus : (Polynomial.X - Polynomial.C (1 : ℚ)).derivative = 1 := by
    simp
  rw [hplus, hminus]
  simp only [mul_one]
  ring

/-- Polynomial realization of the even constant matrix `M₀`. -/
noncomputable def besselScaleOperator
    (degree : ℕ) (polynomial : Polynomial ℚ) : Polynomial ℚ :=
  Polynomial.C 2 * (Polynomial.C 1 - Polynomial.X ^ 2) *
      polynomial.derivative +
    Polynomial.C (2 * degree : ℚ) * Polynomial.X * polynomial

theorem one_sub_X_sq_factor :
    (Polynomial.C 1 - Polynomial.X ^ 2 : Polynomial ℚ) =
      -(Polynomial.X - Polynomial.C 1) *
        (Polynomial.X + Polynomial.C 1) := by
  norm_num
  ring

/-- General diagonal action on `(T+1)^p(T-1)^q`. -/
theorem signedBesselPolynomial_operator
    (plusPower minusPower : ℕ) :
    besselScaleOperator (plusPower + minusPower)
        (signedBesselPolynomial plusPower minusPower) =
      Polynomial.C (2 * plusPower - 2 * minusPower : ℚ) *
        signedBesselPolynomial plusPower minusPower := by
  unfold besselScaleOperator
  rw [derivative_signedBesselPolynomial, one_sub_X_sq_factor]
  have hCtwo : Polynomial.C (R := ℚ) 2 = (2 : Polynomial ℚ) :=
    map_ofNat (Polynomial.C : ℚ →+* Polynomial ℚ) 2
  by_cases hplusZero : plusPower = 0
  · subst plusPower
    simp only [Nat.cast_zero, map_zero, zero_mul, zero_add,
      signedBesselPolynomial, pow_zero, one_mul]
    by_cases hminusZero : minusPower = 0
    · subst minusPower
      simp
    · have hminusPos : 1 ≤ minusPower := Nat.one_le_iff_ne_zero.mpr hminusZero
      have hpow : (Polynomial.X - Polynomial.C (1 : ℚ)) ^ minusPower =
          (Polynomial.X - Polynomial.C 1) *
            (Polynomial.X - Polynomial.C 1) ^ (minusPower - 1) := by
        calc
          _ = (Polynomial.X - Polynomial.C 1) ^ ((minusPower - 1) + 1) :=
            congrArg (fun exponent : ℕ =>
              (Polynomial.X - Polynomial.C (1 : ℚ)) ^ exponent) (by omega)
          _ = _ := pow_succ' _ _
      rw [hpow]
      norm_num
      rw [hCtwo]
      ring
  · have hplusPos : 1 ≤ plusPower := Nat.one_le_iff_ne_zero.mpr hplusZero
    by_cases hminusZero : minusPower = 0
    · subst minusPower
      simp only [Nat.cast_zero, map_zero, zero_mul, add_zero,
        signedBesselPolynomial, pow_zero, mul_one]
      have hpow : (Polynomial.X + Polynomial.C (1 : ℚ)) ^ plusPower =
          (Polynomial.X + Polynomial.C 1) *
            (Polynomial.X + Polynomial.C 1) ^ (plusPower - 1) := by
        calc
          _ = (Polynomial.X + Polynomial.C 1) ^ ((plusPower - 1) + 1) :=
            congrArg (fun exponent : ℕ =>
              (Polynomial.X + Polynomial.C (1 : ℚ)) ^ exponent) (by omega)
          _ = _ := pow_succ' _ _
      rw [hpow]
      norm_num
      rw [hCtwo]
      ring
    · have hminusPos : 1 ≤ minusPower := Nat.one_le_iff_ne_zero.mpr hminusZero
      have hpowPlus : (Polynomial.X + Polynomial.C (1 : ℚ)) ^ plusPower =
          (Polynomial.X + Polynomial.C 1) *
            (Polynomial.X + Polynomial.C 1) ^ (plusPower - 1) := by
        calc
          _ = (Polynomial.X + Polynomial.C 1) ^ ((plusPower - 1) + 1) :=
            congrArg (fun exponent : ℕ =>
              (Polynomial.X + Polynomial.C (1 : ℚ)) ^ exponent) (by omega)
          _ = _ := pow_succ' _ _
      have hpowMinus : (Polynomial.X - Polynomial.C (1 : ℚ)) ^ minusPower =
          (Polynomial.X - Polynomial.C 1) *
            (Polynomial.X - Polynomial.C 1) ^ (minusPower - 1) := by
        calc
          _ = (Polynomial.X - Polynomial.C 1) ^ ((minusPower - 1) + 1) :=
            congrArg (fun exponent : ℕ =>
              (Polynomial.X - Polynomial.C (1 : ℚ)) ^ exponent) (by omega)
          _ = _ := pow_succ' _ _
      rw [hpowPlus, hpowMinus]
      unfold signedBesselPolynomial
      rw [hpowPlus, hpowMinus]
      norm_num
      rw [hCtwo]
      ring

/-- Diagonalization identity giving the even scales `2d-4r`. -/
theorem signedBesselPolynomial_eigen
    (degree scaleIndex : ℕ) (hscale : scaleIndex ≤ degree) :
    besselScaleOperator degree
        (signedBesselPolynomial (degree - scaleIndex) scaleIndex) =
      Polynomial.C (2 * degree - 4 * scaleIndex : ℚ) *
        signedBesselPolynomial (degree - scaleIndex) scaleIndex := by
  have h := signedBesselPolynomial_operator (degree - scaleIndex) scaleIndex
  rw [Nat.sub_add_cancel hscale] at h
  have hcast : ((degree - scaleIndex : ℕ) : ℚ) =
      (degree : ℚ) - scaleIndex := Nat.cast_sub hscale
  rw [hcast] at h
  have hscalar : (2 * (degree - scaleIndex) - 2 * scaleIndex : ℚ) =
      2 * degree - 4 * scaleIndex := by
    ring
  rw [hscalar] at h
  exact h

/-- Odd rank adds the scale `1`, giving `2d+1-4r`. -/
theorem odd_signedBesselPolynomial_eigen
    (degree scaleIndex : ℕ) (hscale : scaleIndex ≤ degree) :
    besselScaleOperator degree
          (signedBesselPolynomial (degree - scaleIndex) scaleIndex) +
        signedBesselPolynomial (degree - scaleIndex) scaleIndex =
      Polynomial.C (2 * degree + 1 - 4 * scaleIndex : ℚ) *
        signedBesselPolynomial (degree - scaleIndex) scaleIndex := by
  rw [signedBesselPolynomial_eigen degree scaleIndex hscale]
  have hscalar : (2 * degree - 4 * scaleIndex : ℚ) + 1 =
      2 * degree + 1 - 4 * scaleIndex := by ring
  let polynomial := signedBesselPolynomial (degree - scaleIndex) scaleIndex
  calc
    Polynomial.C (2 * degree - 4 * scaleIndex : ℚ) * polynomial + polynomial =
        Polynomial.C (2 * degree - 4 * scaleIndex : ℚ) * polynomial +
          Polynomial.C 1 * polynomial := by simp
    _ = (Polynomial.C (2 * degree - 4 * scaleIndex : ℚ) +
          Polynomial.C 1) * polynomial := (add_mul _ _ _).symm
    _ = Polynomial.C ((2 * degree - 4 * scaleIndex : ℚ) + 1) * polynomial := by
          rw [← map_add]
    _ = Polynomial.C (2 * degree + 1 - 4 * scaleIndex : ℚ) * polynomial := by
          rw [hscalar]

end FibonacciRibbonKernel
