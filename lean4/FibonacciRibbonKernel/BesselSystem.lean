import FibonacciRibbonKernel.DefinitionFormulas
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Data.Matrix.Basic

namespace FibonacciRibbonKernel

open PowerSeries

/-- `J₀(x)=Σ x^{2m}/(m!)²`. -/
noncomputable def besselJ0 : ℚ⟦X⟧ :=
  PowerSeries.mk fun n =>
    if Even n then
      1 / (((n / 2).factorial : ℚ) ^ 2)
    else 0

/-- `J₁(x)=Σ x^{2m+1}/(m!(m+1)!)`. -/
noncomputable def besselJ1 : ℚ⟦X⟧ :=
  PowerSeries.mk fun n =>
    if Odd n then
      1 / (((n / 2).factorial : ℚ) * ((n / 2 + 1).factorial : ℚ))
    else 0

theorem coeff_two_mul (series : ℚ⟦X⟧) (n : ℕ) :
    PowerSeries.coeff n (2 * series) =
      2 * PowerSeries.coeff n series := by
  change PowerSeries.coeff n (PowerSeries.C (R := ℚ) 2 * series) = _
  rw [PowerSeries.coeff_C_mul]

theorem besselJ0_coeff_even (m : ℕ) :
    PowerSeries.coeff (2 * m) besselJ0 =
      1 / ((m.factorial : ℚ) ^ 2) := by
  simp [besselJ0, even_iff_two_dvd]

theorem besselJ0_coeff_odd (m : ℕ) :
    PowerSeries.coeff (2 * m + 1) besselJ0 = 0 := by
  simp [besselJ0]

theorem besselJ1_coeff_even (m : ℕ) :
    PowerSeries.coeff (2 * m) besselJ1 = 0 := by
  simp [besselJ1]

theorem besselJ1_coeff_odd (m : ℕ) :
    PowerSeries.coeff (2 * m + 1) besselJ1 =
      1 / ((m.factorial : ℚ) * ((m + 1).factorial : ℚ)) := by
  rw [besselJ1, PowerSeries.coeff_mk, if_pos]
  · have hdiv : (2 * m + 1) / 2 = m := by omega
    rw [hdiv]
  · exact ⟨m, by omega⟩

theorem derivative_besselJ0 :
    PowerSeries.derivative ℚ besselJ0 = 2 * besselJ1 := by
  ext n
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [PowerSeries.coeff_derivative, besselJ0_coeff_odd,
      zero_mul]
    rw [coeff_two_mul, besselJ1_coeff_even, mul_zero]
  · rw [PowerSeries.coeff_derivative]
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega,
      besselJ0_coeff_even]
    rw [coeff_two_mul, besselJ1_coeff_odd]
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

theorem X_mul_derivative_besselJ1 :
    X * PowerSeries.derivative ℚ besselJ1 =
      2 * X * besselJ0 - besselJ1 := by
  rw [show 2 * X * besselJ0 = X * (2 * besselJ0) by ring]
  ext n
  cases n with
  | zero => simp [besselJ1]
  | succ n =>
      rw [show (X : ℚ⟦X⟧) = X ^ 1 by simp]
      rw [PowerSeries.coeff_X_pow_mul
        (PowerSeries.derivative ℚ besselJ1) 1 n]
      rw [map_sub]
      rw [PowerSeries.coeff_X_pow_mul (2 * besselJ0) 1 n]
      rw [PowerSeries.coeff_derivative]
      rw [coeff_two_mul]
      obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
      · rw [besselJ1_coeff_odd, besselJ0_coeff_even]
        rw [Nat.factorial_succ]
        push_cast
        field_simp
        ring
      · rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega]
        rw [besselJ1_coeff_even, besselJ0_coeff_odd]
        simp

/-- Homogeneous monomial basis used in the finite Bessel system. -/
noncomputable def besselMonomial (degree a : ℕ) : ℚ⟦X⟧ :=
  besselJ0 ^ a * besselJ1 ^ (degree - a)

/-- Coordinate differential identity before packaging into matrices. -/
theorem X_mul_derivative_besselMonomial
    (degree a : ℕ) (ha : a ≤ degree) :
    X * PowerSeries.derivative ℚ (besselMonomial degree a) =
      ((2 * a : ℕ) : ℚ⟦X⟧) * X * besselJ0 ^ (a - 1) *
          besselJ1 ^ (degree - a + 1) +
        ((2 * (degree - a) : ℕ) : ℚ⟦X⟧) * X * besselJ0 ^ (a + 1) *
          besselJ1 ^ (degree - a - 1) -
        ((degree - a : ℕ) : ℚ⟦X⟧) * besselMonomial degree a := by
  unfold besselMonomial
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  rw [PowerSeries.derivative_pow, PowerSeries.derivative_pow,
    derivative_besselJ0]
  by_cases ha0 : a = 0
  · subst a
    simp
    rw [show X *
        (((degree : ℕ) : ℚ⟦X⟧) * besselJ1 ^ (degree - 1) *
          PowerSeries.derivative ℚ besselJ1) =
        ((degree : ℕ) : ℚ⟦X⟧) * besselJ1 ^ (degree - 1) *
          (X * PowerSeries.derivative ℚ besselJ1) by ring]
    rw [X_mul_derivative_besselJ1]
    by_cases hd0 : degree = 0
    · subst degree
      simp
    · have hd : 1 ≤ degree := Nat.one_le_iff_ne_zero.mpr hd0
      rw [show degree = (degree - 1) + 1 by omega, pow_succ']
      push_cast
      ring
  · have haPos : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
    by_cases htop : a = degree
    · subst degree
      simp
      ring
    · have hbelow : a < degree := lt_of_le_of_ne ha htop
      have hdualPos : 1 ≤ degree - a := by omega
      rw [show X *
          (besselJ0 ^ a *
              (((degree - a : ℕ) : ℚ⟦X⟧) * besselJ1 ^ (degree - a - 1) *
                PowerSeries.derivative ℚ besselJ1) +
            besselJ1 ^ (degree - a) *
              (((a : ℕ) : ℚ⟦X⟧) * besselJ0 ^ (a - 1) * (2 * besselJ1))) =
          besselJ0 ^ a * ((degree - a : ℕ) : ℚ⟦X⟧) *
              besselJ1 ^ (degree - a - 1) *
              (X * PowerSeries.derivative ℚ besselJ1) +
            X * (besselJ1 ^ (degree - a) *
              (((a : ℕ) : ℚ⟦X⟧) * besselJ0 ^ (a - 1) * (2 * besselJ1))) by ring]
      rw [X_mul_derivative_besselJ1]
      push_cast
      have hpow0 : besselJ0 ^ a = besselJ0 * besselJ0 ^ (a - 1) := by
        calc
          besselJ0 ^ a = besselJ0 ^ ((a - 1) + 1) :=
            congrArg (fun exponent : ℕ => besselJ0 ^ exponent) (by omega)
          _ = besselJ0 ^ (a - 1) * besselJ0 := pow_succ _ _
          _ = besselJ0 * besselJ0 ^ (a - 1) := mul_comm _ _
      have hpow1 : besselJ1 ^ (degree - a) =
          besselJ1 * besselJ1 ^ (degree - a - 1) := by
        calc
          besselJ1 ^ (degree - a) =
              besselJ1 ^ ((degree - a - 1) + 1) :=
            congrArg (fun exponent : ℕ => besselJ1 ^ exponent) (by omega)
          _ = besselJ1 ^ (degree - a - 1) * besselJ1 := pow_succ _ _
          _ = besselJ1 * besselJ1 ^ (degree - a - 1) := mul_comm _ _
      rw [pow_succ' besselJ1 (degree - a), pow_succ' besselJ0 a]
      rw [hpow0, hpow1]
      ring

/-- Bessel monomial basis vector of total degree `degree`. -/
noncomputable def besselBasisVector (degree : ℕ) :
    Fin (degree + 1) → ℚ⟦X⟧ :=
  fun index => besselMonomial degree index.val

/-- Constant tridiagonal `M₀` action in the monomial basis. -/
noncomputable def besselM0Action (degree : ℕ)
    (vector : Fin (degree + 1) → ℚ⟦X⟧) :
    Fin (degree + 1) → ℚ⟦X⟧ :=
  fun index =>
    (if hpositive : 0 < index.val then
      PowerSeries.C (2 * index.val : ℚ) *
        vector ⟨index.val - 1, by omega⟩
    else 0) +
    (if hbelow : index.val < degree then
      PowerSeries.C (2 * (degree - index.val) : ℚ) *
        vector ⟨index.val + 1, by omega⟩
    else 0)

/-- Constant diagonal `M₁` action. -/
noncomputable def besselM1Action (degree : ℕ)
    (vector : Fin (degree + 1) → ℚ⟦X⟧) :
    Fin (degree + 1) → ℚ⟦X⟧ :=
  fun index =>
    PowerSeries.C (-(degree - index.val : ℚ)) * vector index

/-- Multiplied form of `F'=(M₀+X⁻¹M₁)F`. -/
theorem bessel_finite_system (degree : ℕ) (index : Fin (degree + 1)) :
    X * PowerSeries.derivative ℚ (besselBasisVector degree index) =
      X * besselM0Action degree (besselBasisVector degree) index +
        besselM1Action degree (besselBasisVector degree) index := by
  have hraw := X_mul_derivative_besselMonomial degree index.val
    (Nat.le_of_lt_succ index.isLt)
  change X * PowerSeries.derivative ℚ (besselMonomial degree index.val) = _
  rw [hraw]
  unfold besselBasisVector besselM0Action besselM1Action
  dsimp only
  have hCtwo : PowerSeries.C (R := ℚ) 2 = (2 : ℚ⟦X⟧) :=
    map_ofNat (PowerSeries.C (R := ℚ)) 2
  by_cases hpositive : 0 < index.val
  · by_cases hbelow : index.val < degree
    · have hpred : degree - (index.val - 1) =
          degree - index.val + 1 := by omega
      have hsucc : degree - (index.val + 1) =
          degree - index.val - 1 := by omega
      have hpow0 : besselJ0 ^ index.val =
          besselJ0 * besselJ0 ^ (index.val - 1) := by
        calc
          besselJ0 ^ index.val = besselJ0 ^ ((index.val - 1) + 1) :=
            congrArg (fun exponent : ℕ => besselJ0 ^ exponent) (by omega)
          _ = besselJ0 ^ (index.val - 1) * besselJ0 := pow_succ _ _
          _ = _ := mul_comm _ _
      have hpow1 : besselJ1 ^ (degree - index.val) =
          besselJ1 * besselJ1 ^ (degree - index.val - 1) := by
        calc
          besselJ1 ^ (degree - index.val) =
              besselJ1 ^ ((degree - index.val - 1) + 1) :=
            congrArg (fun exponent : ℕ => besselJ1 ^ exponent) (by omega)
          _ = besselJ1 ^ (degree - index.val - 1) * besselJ1 := pow_succ _ _
          _ = _ := mul_comm _ _
      have hcast : ((degree - index.val : ℕ) : ℚ⟦X⟧) =
          (degree : ℚ⟦X⟧) - (index.val : ℚ⟦X⟧) := by
        exact Nat.cast_sub (Nat.le_of_lt hbelow)
      simp [hpositive, hbelow, besselMonomial, hpred, hsucc]
      rw [hCtwo, hpow0, hpow1, hcast]
      ring
    · have htop : index.val = degree := by omega
      have hd : 0 < degree := by omega
      have hsub : degree - (degree - 1) = 1 := by omega
      simp [htop, hd, besselMonomial, hsub]
      rw [hCtwo]
      ring
  · have hzero : index.val = 0 := by omega
    by_cases hd : 0 < degree
    · simp [hzero, hd, besselMonomial]
      rw [hCtwo]
      ring
    · have hd0 : degree = 0 := by omega
      simp [hzero, hd0, besselMonomial]

/-- Coefficient-level actions of the two constant matrices. -/
def besselM0CoeffAction (degree : ℕ)
    (vector : Fin (degree + 1) → ℚ) : Fin (degree + 1) → ℚ :=
  fun index =>
    (if hpositive : 0 < index.val then
      (2 * index.val : ℚ) * vector ⟨index.val - 1, by omega⟩
    else 0) +
    (if hbelow : index.val < degree then
      (2 * (degree - index.val) : ℚ) * vector ⟨index.val + 1, by omega⟩
    else 0)

def besselM1CoeffAction (degree : ℕ)
    (vector : Fin (degree + 1) → ℚ) : Fin (degree + 1) → ℚ :=
  fun index => (-(degree - index.val : ℚ)) * vector index

theorem coeff_besselM0Action (degree coefficient : ℕ)
    (vector : Fin (degree + 1) → ℚ⟦X⟧) (index : Fin (degree + 1)) :
    PowerSeries.coeff coefficient (besselM0Action degree vector index) =
      besselM0CoeffAction degree
        (fun coordinate => PowerSeries.coeff coefficient (vector coordinate)) index := by
  unfold besselM0Action besselM0CoeffAction
  dsimp only
  split_ifs <;>
    simp only [map_add, map_zero, PowerSeries.coeff_C_mul,
      zero_add, add_zero]

theorem coeff_besselM1Action (degree coefficient : ℕ)
    (vector : Fin (degree + 1) → ℚ⟦X⟧) (index : Fin (degree + 1)) :
    PowerSeries.coeff coefficient (besselM1Action degree vector index) =
      besselM1CoeffAction degree
        (fun coordinate => PowerSeries.coeff coefficient (vector coordinate)) index := by
  unfold besselM1Action besselM1CoeffAction
  dsimp only
  rw [PowerSeries.coeff_C_mul]

theorem besselM0CoeffAction_smul (degree : ℕ) (scalar : ℚ)
    (vector : Fin (degree + 1) → ℚ) (index : Fin (degree + 1)) :
    besselM0CoeffAction degree (fun coordinate => scalar * vector coordinate) index =
      scalar * besselM0CoeffAction degree vector index := by
  unfold besselM0CoeffAction
  dsimp only
  split_ifs <;> ring

theorem besselM1CoeffAction_smul (degree : ℕ) (scalar : ℚ)
    (vector : Fin (degree + 1) → ℚ) (index : Fin (degree + 1)) :
    besselM1CoeffAction degree (fun coordinate => scalar * vector coordinate) index =
      scalar * besselM1CoeffAction degree vector index := by
  unfold besselM1CoeffAction
  ring

/-- Exponential coefficient vector `f_k=k![X^k]F`. -/
noncomputable def besselFactorialCoeff (degree coefficient : ℕ) :
    Fin (degree + 1) → ℚ :=
  fun index => (coefficient.factorial : ℚ) *
    PowerSeries.coeff coefficient (besselBasisVector degree index)

/-- Coefficient recurrence `(kI-M₁)f_k=kM₀f_{k-1}`. -/
theorem bessel_factorial_coefficient_recurrence
    (degree coefficient : ℕ) (index : Fin (degree + 1)) :
    (coefficient : ℚ) * besselFactorialCoeff degree coefficient index -
        besselM1CoeffAction degree (besselFactorialCoeff degree coefficient) index =
      (coefficient : ℚ) *
        besselM0CoeffAction degree
          (besselFactorialCoeff degree (coefficient - 1)) index := by
  have hsystem := congrArg (PowerSeries.coeff coefficient)
    (bessel_finite_system degree index)
  cases coefficient with
  | zero =>
      simp only [Nat.cast_zero, zero_mul, Nat.zero_sub,
        besselFactorialCoeff, Nat.factorial_zero, Nat.cast_one, one_mul,
        sub_eq_zero]
      simp only [map_add] at hsystem
      have hleft : PowerSeries.coeff 0
          (X * PowerSeries.derivative ℚ (besselBasisVector degree index)) = 0 := by
        simp
      have hM0 : PowerSeries.coeff 0
          (X * besselM0Action degree (besselBasisVector degree) index) = 0 := by
        simp
      rw [hleft, hM0, zero_add, coeff_besselM1Action] at hsystem
      have hfactorialZero : besselFactorialCoeff degree 0 =
          (fun coordinate => PowerSeries.coeff 0
            (besselBasisVector degree coordinate)) := by
        funext coordinate
        simp [besselFactorialCoeff]
      rw [hfactorialZero]
      exact hsystem
  | succ n =>
      have hcoeff :
          (n + 1 : ℚ) * PowerSeries.coeff (n + 1)
              (besselBasisVector degree index) =
            besselM0CoeffAction degree
                (fun coordinate => PowerSeries.coeff n
                  (besselBasisVector degree coordinate)) index +
              besselM1CoeffAction degree
                (fun coordinate => PowerSeries.coeff (n + 1)
                  (besselBasisVector degree coordinate)) index := by
        rw [show (X : ℚ⟦X⟧) = X ^ 1 by simp] at hsystem
        rw [map_add, PowerSeries.coeff_X_pow_mul
          (PowerSeries.derivative ℚ (besselBasisVector degree index)) 1 n,
          PowerSeries.coeff_derivative,
          PowerSeries.coeff_X_pow_mul
            (besselM0Action degree (besselBasisVector degree) index) 1 n,
          coeff_besselM0Action, coeff_besselM1Action] at hsystem
        simpa [mul_comm] using hsystem
      unfold besselFactorialCoeff
      rw [besselM1CoeffAction_smul, besselM0CoeffAction_smul]
      rw [Nat.factorial_succ]
      push_cast
      linear_combination ((n + 1) * n.factorial : ℚ) * hcoeff

/-- Ordinary generating series of the factorial-scaled coefficient vector. -/
noncomputable def besselOrdinarySeries (degree : ℕ) :
    Fin (degree + 1) → ℚ⟦X⟧ :=
  fun index => PowerSeries.mk fun coefficient =>
    besselFactorialCoeff degree coefficient index

@[simp] theorem besselOrdinarySeries_coeff
    (degree coefficient : ℕ) (index : Fin (degree + 1)) :
    PowerSeries.coeff coefficient (besselOrdinarySeries degree index) =
      besselFactorialCoeff degree coefficient index := by
  simp [besselOrdinarySeries]

/-- Coordinate form of the ordinary Bessel system in the manuscript. -/
theorem bessel_ordinary_system
    (degree : ℕ) (index : Fin (degree + 1)) :
    X *
        (PowerSeries.derivative ℚ (besselOrdinarySeries degree index) -
          X * besselM0Action degree
            (fun coordinate =>
              PowerSeries.derivative ℚ (besselOrdinarySeries degree coordinate)) index) =
      (besselM1Action degree (besselOrdinarySeries degree) index +
          X * besselM0Action degree (besselOrdinarySeries degree) index) -
        PowerSeries.C
          (besselM1CoeffAction degree
            (besselFactorialCoeff degree 0) index) := by
  ext coefficient
  have hf0 : (fun coordinate =>
      PowerSeries.constantCoeff (besselOrdinarySeries degree coordinate)) =
      besselFactorialCoeff degree 0 := by
    funext coordinate
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    exact besselOrdinarySeries_coeff degree 0 coordinate
  cases coefficient with
  | zero =>
      simp only [map_sub, map_add, map_mul, PowerSeries.coeff_C,
        PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_X,
        zero_mul]
      have hM1 := coeff_besselM1Action degree 0
        (besselOrdinarySeries degree) index
      rw [PowerSeries.coeff_zero_eq_constantCoeff] at hM1
      rw [hM1]
      rw [hf0]
      simp
  | succ coefficient =>
      rw [show (X : ℚ⟦X⟧) = X ^ 1 by simp]
      rw [PowerSeries.coeff_X_pow_mul _ 1 coefficient]
      rw [map_sub, PowerSeries.coeff_derivative]
      rw [PowerSeries.coeff_X_pow_mul' _ 1 coefficient]
      rw [map_sub, map_add, PowerSeries.coeff_C]
      rw [PowerSeries.coeff_X_pow_mul _ 1 coefficient]
      rw [coeff_besselM1Action, besselOrdinarySeries_coeff]
      by_cases hcoefficient : coefficient = 0
      · subst coefficient
        simp only [if_neg (by omega : ¬ 1 ≤ 0),
          PowerSeries.coeff_zero_eq_constantCoeff,
          besselOrdinarySeries_coeff, Nat.cast_zero,
          zero_add, sub_zero]
        have hM0zero := coeff_besselM0Action degree 0
          (besselOrdinarySeries degree) index
        rw [PowerSeries.coeff_zero_eq_constantCoeff] at hM0zero
        rw [hM0zero]
        rw [hf0]
        have hrec := bessel_factorial_coefficient_recurrence degree 1 index
        norm_num at hrec ⊢
        linear_combination hrec
      · have hpositive : 1 ≤ coefficient := Nat.one_le_iff_ne_zero.mpr hcoefficient
        rw [if_pos hpositive]
        rw [coeff_besselM0Action, coeff_besselM0Action]
        simp only [besselOrdinarySeries_coeff, PowerSeries.coeff_derivative]
        have hNat : coefficient - 1 + 1 = coefficient :=
          Nat.sub_add_cancel hpositive
        simp only [hNat]
        have hscalar : ((coefficient - 1 : ℕ) : ℚ) + 1 = coefficient := by
          exact_mod_cast hNat
        rw [hscalar]
        have hfun : (fun coordinate =>
            besselFactorialCoeff degree coefficient coordinate * (coefficient : ℚ)) =
            (fun coordinate =>
              (coefficient : ℚ) * besselFactorialCoeff degree coefficient coordinate) := by
          funext coordinate
          ring
        rw [hfun, besselM0CoeffAction_smul]
        simp only [if_neg (by omega : ¬ coefficient + 1 = 0)]
        have hrec := bessel_factorial_coefficient_recurrence
          degree (coefficient + 1) index
        simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hrec
        linear_combination hrec

/-- Odd-rank basis: the even basis multiplied by `e^X`. -/
noncomputable def oddBesselBasisVector (degree : ℕ) :
    Fin (degree + 1) → ℚ⟦X⟧ :=
  fun index => PowerSeries.exp ℚ * besselBasisVector degree index

/-- Odd-rank constant matrix `M₀+I`. -/
noncomputable def oddBesselM0Action (degree : ℕ)
    (vector : Fin (degree + 1) → ℚ⟦X⟧) :
    Fin (degree + 1) → ℚ⟦X⟧ :=
  fun index => vector index + besselM0Action degree vector index

theorem besselM0Action_mul_left (degree : ℕ) (factor : ℚ⟦X⟧)
    (vector : Fin (degree + 1) → ℚ⟦X⟧) (index : Fin (degree + 1)) :
    besselM0Action degree (fun coordinate => factor * vector coordinate) index =
      factor * besselM0Action degree vector index := by
  unfold besselM0Action
  dsimp only
  split_ifs <;> ring

theorem besselM1Action_mul_left (degree : ℕ) (factor : ℚ⟦X⟧)
    (vector : Fin (degree + 1) → ℚ⟦X⟧) (index : Fin (degree + 1)) :
    besselM1Action degree (fun coordinate => factor * vector coordinate) index =
      factor * besselM1Action degree vector index := by
  unfold besselM1Action
  ring

/-- Odd-rank multiplied Bessel system. -/
theorem odd_bessel_finite_system (degree : ℕ) (index : Fin (degree + 1)) :
    X * PowerSeries.derivative ℚ (oddBesselBasisVector degree index) =
      X * oddBesselM0Action degree (oddBesselBasisVector degree) index +
        besselM1Action degree (oddBesselBasisVector degree) index := by
  unfold oddBesselBasisVector oddBesselM0Action
  rw [Derivation.leibniz]
  simp only [smul_eq_mul, PowerSeries.derivative_exp]
  rw [besselM0Action_mul_left, besselM1Action_mul_left]
  have heven := bessel_finite_system degree index
  linear_combination PowerSeries.exp ℚ * heven

def oddBesselM0CoeffAction (degree : ℕ)
    (vector : Fin (degree + 1) → ℚ) : Fin (degree + 1) → ℚ :=
  fun index => vector index + besselM0CoeffAction degree vector index

theorem coeff_oddBesselM0Action (degree coefficient : ℕ)
    (vector : Fin (degree + 1) → ℚ⟦X⟧) (index : Fin (degree + 1)) :
    PowerSeries.coeff coefficient (oddBesselM0Action degree vector index) =
      oddBesselM0CoeffAction degree
        (fun coordinate => PowerSeries.coeff coefficient (vector coordinate)) index := by
  unfold oddBesselM0Action oddBesselM0CoeffAction
  rw [map_add, coeff_besselM0Action]

theorem oddBesselM0CoeffAction_smul (degree : ℕ) (scalar : ℚ)
    (vector : Fin (degree + 1) → ℚ) (index : Fin (degree + 1)) :
    oddBesselM0CoeffAction degree (fun coordinate => scalar * vector coordinate) index =
      scalar * oddBesselM0CoeffAction degree vector index := by
  unfold oddBesselM0CoeffAction
  rw [besselM0CoeffAction_smul]
  ring

noncomputable def oddBesselFactorialCoeff (degree coefficient : ℕ) :
    Fin (degree + 1) → ℚ :=
  fun index => (coefficient.factorial : ℚ) *
    PowerSeries.coeff coefficient (oddBesselBasisVector degree index)

theorem odd_bessel_factorial_coefficient_recurrence
    (degree coefficient : ℕ) (index : Fin (degree + 1)) :
    (coefficient : ℚ) * oddBesselFactorialCoeff degree coefficient index -
        besselM1CoeffAction degree (oddBesselFactorialCoeff degree coefficient) index =
      (coefficient : ℚ) *
        oddBesselM0CoeffAction degree
          (oddBesselFactorialCoeff degree (coefficient - 1)) index := by
  have hsystem := congrArg (PowerSeries.coeff coefficient)
    (odd_bessel_finite_system degree index)
  cases coefficient with
  | zero =>
      simp only [Nat.cast_zero, zero_mul, Nat.zero_sub,
        oddBesselFactorialCoeff, Nat.factorial_zero, Nat.cast_one, one_mul,
        sub_eq_zero]
      simp only [map_add] at hsystem
      have hleft : PowerSeries.coeff 0
          (X * PowerSeries.derivative ℚ (oddBesselBasisVector degree index)) = 0 := by
        simp
      have hM0 : PowerSeries.coeff 0
          (X * oddBesselM0Action degree (oddBesselBasisVector degree) index) = 0 := by
        simp
      rw [hleft, hM0, zero_add, coeff_besselM1Action] at hsystem
      have hfactorialZero : oddBesselFactorialCoeff degree 0 =
          (fun coordinate => PowerSeries.coeff 0
            (oddBesselBasisVector degree coordinate)) := by
        funext coordinate
        simp [oddBesselFactorialCoeff]
      rw [hfactorialZero]
      exact hsystem
  | succ n =>
      have hcoeff :
          (n + 1 : ℚ) * PowerSeries.coeff (n + 1)
              (oddBesselBasisVector degree index) =
            oddBesselM0CoeffAction degree
                (fun coordinate => PowerSeries.coeff n
                  (oddBesselBasisVector degree coordinate)) index +
              besselM1CoeffAction degree
                (fun coordinate => PowerSeries.coeff (n + 1)
                  (oddBesselBasisVector degree coordinate)) index := by
        rw [show (X : ℚ⟦X⟧) = X ^ 1 by simp] at hsystem
        rw [map_add, PowerSeries.coeff_X_pow_mul
          (PowerSeries.derivative ℚ (oddBesselBasisVector degree index)) 1 n,
          PowerSeries.coeff_derivative,
          PowerSeries.coeff_X_pow_mul
            (oddBesselM0Action degree (oddBesselBasisVector degree) index) 1 n,
          coeff_oddBesselM0Action, coeff_besselM1Action] at hsystem
        simpa [mul_comm] using hsystem
      unfold oddBesselFactorialCoeff
      rw [besselM1CoeffAction_smul, oddBesselM0CoeffAction_smul]
      rw [Nat.factorial_succ]
      push_cast
      linear_combination ((n + 1) * n.factorial : ℚ) * hcoeff

noncomputable def oddBesselOrdinarySeries (degree : ℕ) :
    Fin (degree + 1) → ℚ⟦X⟧ :=
  fun index => PowerSeries.mk fun coefficient =>
    oddBesselFactorialCoeff degree coefficient index

@[simp] theorem oddBesselOrdinarySeries_coeff
    (degree coefficient : ℕ) (index : Fin (degree + 1)) :
    PowerSeries.coeff coefficient (oddBesselOrdinarySeries degree index) =
      oddBesselFactorialCoeff degree coefficient index := by
  simp [oddBesselOrdinarySeries]

theorem odd_bessel_ordinary_system
    (degree : ℕ) (index : Fin (degree + 1)) :
    X *
        (PowerSeries.derivative ℚ (oddBesselOrdinarySeries degree index) -
          X * oddBesselM0Action degree
            (fun coordinate =>
              PowerSeries.derivative ℚ
                (oddBesselOrdinarySeries degree coordinate)) index) =
      (besselM1Action degree (oddBesselOrdinarySeries degree) index +
          X * oddBesselM0Action degree (oddBesselOrdinarySeries degree) index) -
        PowerSeries.C
          (besselM1CoeffAction degree
            (oddBesselFactorialCoeff degree 0) index) := by
  ext coefficient
  have hf0 : (fun coordinate =>
      PowerSeries.constantCoeff (oddBesselOrdinarySeries degree coordinate)) =
      oddBesselFactorialCoeff degree 0 := by
    funext coordinate
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    exact oddBesselOrdinarySeries_coeff degree 0 coordinate
  cases coefficient with
  | zero =>
      simp only [map_sub, map_add, map_mul, PowerSeries.coeff_C,
        PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_X,
        zero_mul]
      have hM1 := coeff_besselM1Action degree 0
        (oddBesselOrdinarySeries degree) index
      rw [PowerSeries.coeff_zero_eq_constantCoeff] at hM1
      rw [hM1, hf0]
      simp
  | succ coefficient =>
      rw [show (X : ℚ⟦X⟧) = X ^ 1 by simp]
      rw [PowerSeries.coeff_X_pow_mul _ 1 coefficient]
      rw [map_sub, PowerSeries.coeff_derivative]
      rw [PowerSeries.coeff_X_pow_mul' _ 1 coefficient]
      rw [map_sub, map_add, PowerSeries.coeff_C]
      rw [PowerSeries.coeff_X_pow_mul _ 1 coefficient]
      rw [coeff_besselM1Action, oddBesselOrdinarySeries_coeff]
      by_cases hcoefficient : coefficient = 0
      · subst coefficient
        simp only [if_neg (by omega : ¬ 1 ≤ 0),
          PowerSeries.coeff_zero_eq_constantCoeff,
          oddBesselOrdinarySeries_coeff, Nat.cast_zero,
          zero_add, sub_zero]
        have hM0zero := coeff_oddBesselM0Action degree 0
          (oddBesselOrdinarySeries degree) index
        rw [PowerSeries.coeff_zero_eq_constantCoeff] at hM0zero
        rw [hM0zero, hf0]
        have hrec := odd_bessel_factorial_coefficient_recurrence degree 1 index
        norm_num at hrec ⊢
        linear_combination hrec
      · have hpositive : 1 ≤ coefficient := Nat.one_le_iff_ne_zero.mpr hcoefficient
        rw [if_pos hpositive]
        rw [coeff_oddBesselM0Action, coeff_oddBesselM0Action]
        simp only [oddBesselOrdinarySeries_coeff, PowerSeries.coeff_derivative]
        have hNat : coefficient - 1 + 1 = coefficient :=
          Nat.sub_add_cancel hpositive
        simp only [hNat]
        have hscalar : ((coefficient - 1 : ℕ) : ℚ) + 1 = coefficient := by
          exact_mod_cast hNat
        rw [hscalar]
        have hfun : (fun coordinate =>
            oddBesselFactorialCoeff degree coefficient coordinate * (coefficient : ℚ)) =
            (fun coordinate =>
              (coefficient : ℚ) *
                oddBesselFactorialCoeff degree coefficient coordinate) := by
          funext coordinate
          ring
        rw [hfun, oddBesselM0CoeffAction_smul]
        simp only [if_neg (by omega : ¬ coefficient + 1 = 0)]
        have hrec := odd_bessel_factorial_coefficient_recurrence
          degree (coefficient + 1) index
        simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hrec
        linear_combination hrec

end FibonacciRibbonKernel
