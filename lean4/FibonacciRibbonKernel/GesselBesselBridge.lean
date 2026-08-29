import FibonacciRibbonKernel.HeightSixBessel

namespace FibonacciRibbonKernel

open PowerSeries

/-- Literal source series `J_r(X)=sum_m X^(2m+r)/(m!(m+r)!)`. -/
noncomputable def literalBesselJ (order : ℕ) : ℚ⟦X⟧ :=
  by
    classical
    exact PowerSeries.mk fun degree =>
      if h : ∃ index : ℕ, degree = 2 * index + order then
        let index := Nat.find h
        1 / ((index.factorial : ℚ) * ((index + order).factorial : ℚ))
      else 0

theorem literalBesselJ_coeff_of_eq
    (order index : ℕ) :
    PowerSeries.coeff (2 * index + order) (literalBesselJ order) =
      1 / ((index.factorial : ℚ) * ((index + order).factorial : ℚ)) := by
  classical
  rw [literalBesselJ, PowerSeries.coeff_mk, dif_pos]
  · have hfind : Nat.find (show ∃ candidate : ℕ,
        2 * index + order = 2 * candidate + order from ⟨index, rfl⟩) = index := by
      apply (Nat.find_eq_iff _).2
      constructor
      · rfl
      · intro candidate hcandidate heq
        omega
    rw [hfind]
  · exact ⟨index, rfl⟩

theorem literalBesselJ_coeff_eq_zero
    (order degree : ℕ)
    (hdegree : ¬ ∃ index : ℕ, degree = 2 * index + order) :
    PowerSeries.coeff degree (literalBesselJ order) = 0 := by
  classical
  rw [literalBesselJ, PowerSeries.coeff_mk, dif_neg hdegree]

theorem literalBesselJ_zero : literalBesselJ 0 = besselJ0 := by
  ext degree
  obtain ⟨index, rfl | rfl⟩ := Nat.even_or_odd' degree
  · calc
      PowerSeries.coeff (2 * index) (literalBesselJ 0) =
          1 / ((index.factorial : ℚ) * (index.factorial : ℚ)) := by
            simpa using literalBesselJ_coeff_of_eq 0 index
      _ = 1 / ((index.factorial : ℚ) ^ 2) := by rw [pow_two]
      _ = PowerSeries.coeff (2 * index) besselJ0 :=
        (besselJ0_coeff_even index).symm
  · rw [besselJ0_coeff_odd]
    apply literalBesselJ_coeff_eq_zero
    rintro ⟨candidate, heq⟩
    omega

theorem literalBesselJ_one : literalBesselJ 1 = besselJ1 := by
  ext degree
  obtain ⟨index, rfl | rfl⟩ := Nat.even_or_odd' degree
  · rw [besselJ1_coeff_even]
    apply literalBesselJ_coeff_eq_zero
    rintro ⟨candidate, heq⟩
    omega
  · calc
      PowerSeries.coeff (2 * index + 1) (literalBesselJ 1) =
          1 / ((index.factorial : ℚ) * ((index + 1).factorial : ℚ)) :=
        literalBesselJ_coeff_of_eq 1 index
      _ = PowerSeries.coeff (2 * index + 1) besselJ1 :=
        (besselJ1_coeff_odd index).symm

/-- The exact modified-Bessel recurrence, cleared of the source's `X⁻¹`:
`X J_(r+2)=X J_r-(r+1)J_(r+1)`. -/
theorem literalBesselJ_recurrence (order : ℕ) :
    X * literalBesselJ (order + 2) =
      X * literalBesselJ order -
        (order + 1 : ℚ⟦X⟧) * literalBesselJ (order + 1) := by
  ext degree
  have hscalar : PowerSeries.C (order + 1 : ℚ) =
      (order + 1 : ℚ⟦X⟧) :=
    by
      convert map_natCast (PowerSeries.C : ℚ →+* ℚ⟦X⟧) (order + 1) using 1 <;>
        push_cast <;> ring
  cases degree with
  | zero =>
      rw [map_sub]
      have hzero : PowerSeries.coeff 0 (literalBesselJ (order + 1)) = 0 := by
        apply literalBesselJ_coeff_eq_zero
        rintro ⟨index, heq⟩
        omega
      have hzeroConst :
          PowerSeries.constantCoeff (literalBesselJ (order + 1)) = 0 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
        exact hzero
      rw [show (X : ℚ⟦X⟧) = X ^ 1 by simp,
        PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
      norm_num
      exact Or.inr hzeroConst
  | succ degree =>
      rw [map_sub]
      rw [show (X : ℚ⟦X⟧) = X ^ 1 by simp,
        PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_X_pow_mul,
        ← hscalar, PowerSeries.coeff_C_mul]
      change PowerSeries.coeff degree (literalBesselJ (order + 2)) =
        PowerSeries.coeff degree (literalBesselJ order) -
          (order + 1 : ℚ) *
            PowerSeries.coeff (degree + 1) (literalBesselJ (order + 1))
      by_cases hmain : ∃ index : ℕ, degree = 2 * index + order
      · obtain ⟨index, rfl⟩ := hmain
        cases index with
        | zero =>
            have hhigh : ¬ ∃ candidate : ℕ,
                order = 2 * candidate + (order + 2) := by
              rintro ⟨candidate, heq⟩
              omega
            have hbase : PowerSeries.coeff order (literalBesselJ order) =
                1 / (((Nat.factorial 0 : ℕ) : ℚ) *
                  ((0 + order).factorial : ℚ)) := by
              simpa using literalBesselJ_coeff_of_eq order 0
            have hmiddle :
                PowerSeries.coeff (order + 1) (literalBesselJ (order + 1)) =
                  1 / (((Nat.factorial 0 : ℕ) : ℚ) *
                    ((0 + (order + 1)).factorial : ℚ)) := by
              simpa using literalBesselJ_coeff_of_eq (order + 1) 0
            norm_num only [Nat.zero_add, Nat.mul_zero, zero_add] at *
            rw [literalBesselJ_coeff_eq_zero _ _ hhigh, hbase, hmiddle]
            rw [Nat.factorial_succ]
            push_cast
            have hfactorial : (order.factorial : ℚ) ≠ 0 := by positivity
            field_simp
            ring
        | succ index =>
            have hleft := literalBesselJ_coeff_of_eq (order + 2) index
            have hbase := literalBesselJ_coeff_of_eq order (index + 1)
            have hmiddle := literalBesselJ_coeff_of_eq (order + 1) (index + 1)
            have hbaseDegree :
                2 * index + (order + 2) = 2 * (index + 1) + order := by omega
            have hleftCurrent :
                PowerSeries.coeff (2 * (index + 1) + order)
                    (literalBesselJ (order + 2)) =
                  1 / ((index.factorial : ℚ) *
                    ((index + (order + 2)).factorial : ℚ)) := by
              rw [← hbaseDegree]
              exact hleft
            have hmiddleCurrent :
                PowerSeries.coeff (2 * (index + 1) + order + 1)
                    (literalBesselJ (order + 1)) =
                  1 / (((index + 1).factorial : ℚ) *
                    ((index + 1 + (order + 1)).factorial : ℚ)) := by
              simpa only [Nat.add_assoc] using hmiddle
            rw [hleftCurrent, hbase, hmiddleCurrent]
            rw [show index + 1 + order = index + order + 1 by omega,
              show index + 1 + (order + 1) = index + order + 2 by omega,
              show index + (order + 2) = index + order + 2 by omega]
            have hindexFactorial :
                (index + 1).factorial =
                  (index + 1) * index.factorial :=
              Nat.factorial_succ index
            have htailFactorial :
                (index + order + 2).factorial =
                  (index + order + 2) *
                    (index + order + 1).factorial := by
              exact Nat.factorial_succ (index + order + 1)
            rw [hindexFactorial, htailFactorial]
            push_cast
            have hindex : (index.factorial : ℚ) ≠ 0 := by positivity
            have htail : ((index + order + 1).factorial : ℚ) ≠ 0 := by positivity
            field_simp
            ring
      · have hhigh : ¬ ∃ index : ℕ,
            degree = 2 * index + (order + 2) := by
          rintro ⟨index, heq⟩
          apply hmain
          exact ⟨index + 1, by omega⟩
        have hmiddle : ¬ ∃ index : ℕ,
            degree + 1 = 2 * index + (order + 1) := by
          rintro ⟨index, heq⟩
          apply hmain
          exact ⟨index, by omega⟩
        rw [literalBesselJ_coeff_eq_zero _ _ hhigh,
          literalBesselJ_coeff_eq_zero _ _ hmain,
          literalBesselJ_coeff_eq_zero _ _ hmiddle]
        ring

/-- Odd-height Gessel determinant for five-row bounded tableaux. -/
noncomputable def gesselHeightFiveSeries : ℚ⟦X⟧ :=
  PowerSeries.exp ℚ *
    ((literalBesselJ 0 - literalBesselJ 2) *
        (literalBesselJ 0 - literalBesselJ 4) -
      (literalBesselJ 1 - literalBesselJ 3) ^ 2)

theorem X_mul_literalBesselJ_zero_sub_two :
    X * (literalBesselJ 0 - literalBesselJ 2) = literalBesselJ 1 := by
  have hrec := literalBesselJ_recurrence 0
  norm_num at hrec
  linear_combination -hrec

theorem X_sq_mul_literalBesselJ_one_sub_three :
    X ^ 2 * (literalBesselJ 1 - literalBesselJ 3) =
      2 * (X * literalBesselJ 0 - literalBesselJ 1) := by
  have hrec0 := literalBesselJ_recurrence 0
  have hrec1 := literalBesselJ_recurrence 1
  norm_num at hrec0 hrec1
  linear_combination -X * hrec1 + 2 * hrec0

theorem X_cube_mul_literalBesselJ_zero_sub_four :
    X ^ 3 * (literalBesselJ 0 - literalBesselJ 4) =
      4 * X ^ 2 * literalBesselJ 1 -
        6 * X * literalBesselJ 0 + 6 * literalBesselJ 1 := by
  have hrec0 := literalBesselJ_recurrence 0
  have hrec1 := literalBesselJ_recurrence 1
  have hrec2 := literalBesselJ_recurrence 2
  norm_num at hrec0 hrec1 hrec2
  linear_combination -X ^ 2 * hrec2 + 3 * X * hrec1 -
    (X ^ 2 + 6) * hrec0

theorem gesselHeightFiveSeries_eq_besselSeries :
    gesselHeightFiveSeries = heightFiveBesselSeries := by
  apply PowerSeries.X_pow_mul_cancel (k := 4)
  rw [heightFiveBesselNumerator_factor]
  rw [gesselHeightFiveSeries]
  calc
    X ^ 4 *
        (PowerSeries.exp ℚ *
          ((literalBesselJ 0 - literalBesselJ 2) *
              (literalBesselJ 0 - literalBesselJ 4) -
            (literalBesselJ 1 - literalBesselJ 3) ^ 2)) =
      PowerSeries.exp ℚ *
        ((X * (literalBesselJ 0 - literalBesselJ 2)) *
            (X ^ 3 * (literalBesselJ 0 - literalBesselJ 4)) -
          (X ^ 2 * (literalBesselJ 1 - literalBesselJ 3)) ^ 2) := by ring
    _ = PowerSeries.exp ℚ *
        (literalBesselJ 1 *
            (4 * X ^ 2 * literalBesselJ 1 -
              6 * X * literalBesselJ 0 + 6 * literalBesselJ 1) -
          (2 * (X * literalBesselJ 0 - literalBesselJ 1)) ^ 2) := by
      rw [X_mul_literalBesselJ_zero_sub_two,
        X_sq_mul_literalBesselJ_one_sub_three,
        X_cube_mul_literalBesselJ_zero_sub_four]
    _ = heightFiveBesselNumerator := by
      rw [heightFiveBesselNumerator, literalBesselJ_zero,
        literalBesselJ_one]
      ring

/-- The literal `3 x 3` even-height Gessel matrix for six rows. -/
noncomputable def gesselHeightSixMatrix : Matrix (Fin 3) (Fin 3) ℚ⟦X⟧ :=
  !![literalBesselJ 0 + literalBesselJ 1,
      literalBesselJ 1 + literalBesselJ 2,
      literalBesselJ 2 + literalBesselJ 3;
     literalBesselJ 1 + literalBesselJ 2,
      literalBesselJ 0 + literalBesselJ 3,
      literalBesselJ 1 + literalBesselJ 4;
     literalBesselJ 2 + literalBesselJ 3,
      literalBesselJ 1 + literalBesselJ 4,
      literalBesselJ 0 + literalBesselJ 5]

noncomputable def gesselHeightSixSeries : ℚ⟦X⟧ :=
  (literalBesselJ 0 + literalBesselJ 1) *
      (literalBesselJ 0 + literalBesselJ 3) *
      (literalBesselJ 0 + literalBesselJ 5) -
    (literalBesselJ 0 + literalBesselJ 1) *
      (literalBesselJ 1 + literalBesselJ 4) ^ 2 -
    (literalBesselJ 1 + literalBesselJ 2) ^ 2 *
      (literalBesselJ 0 + literalBesselJ 5) +
    2 * (literalBesselJ 1 + literalBesselJ 2) *
      (literalBesselJ 1 + literalBesselJ 4) *
      (literalBesselJ 2 + literalBesselJ 3) -
    (literalBesselJ 2 + literalBesselJ 3) ^ 2 *
      (literalBesselJ 0 + literalBesselJ 3)

theorem gesselHeightSixSeries_eq_det :
    gesselHeightSixSeries = Matrix.det gesselHeightSixMatrix := by
  rw [Matrix.det_fin_three]
  unfold gesselHeightSixSeries
  change _ =
    (literalBesselJ 0 + literalBesselJ 1) *
          (literalBesselJ 0 + literalBesselJ 3) *
          (literalBesselJ 0 + literalBesselJ 5) -
        (literalBesselJ 0 + literalBesselJ 1) *
          (literalBesselJ 1 + literalBesselJ 4) *
          (literalBesselJ 1 + literalBesselJ 4) -
      (literalBesselJ 1 + literalBesselJ 2) *
          (literalBesselJ 1 + literalBesselJ 2) *
          (literalBesselJ 0 + literalBesselJ 5) +
        (literalBesselJ 1 + literalBesselJ 2) *
          (literalBesselJ 1 + literalBesselJ 4) *
          (literalBesselJ 2 + literalBesselJ 3) +
      (literalBesselJ 2 + literalBesselJ 3) *
          (literalBesselJ 1 + literalBesselJ 2) *
          (literalBesselJ 1 + literalBesselJ 4) -
        (literalBesselJ 2 + literalBesselJ 3) *
          (literalBesselJ 0 + literalBesselJ 3) *
          (literalBesselJ 2 + literalBesselJ 3)
  ring

/-- Polynomial obtained by clearing the exact total power `X^6` from the
six-row determinant. -/
noncomputable def gesselHeightSixScaledExpression
    (A B S2 S3 S4 S5 : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  A ^ 3 * X ^ 6 + A ^ 2 * B * X ^ 6 + A ^ 2 * S3 * X ^ 4 +
    A ^ 2 * S5 * X ^ 2 - 2 * A * B ^ 2 * X ^ 6 -
    2 * A * B * S2 * X ^ 5 + A * B * S3 * X ^ 4 -
    2 * A * B * S4 * X ^ 3 + A * B * S5 * X ^ 2 -
    2 * A * S2 ^ 2 * X ^ 4 - 2 * A * S2 * S3 * X ^ 3 -
    A * S3 ^ 2 * X ^ 2 + A * S3 * S5 - A * S4 ^ 2 -
    B ^ 3 * X ^ 6 + 2 * B ^ 2 * S2 * X ^ 5 +
    2 * B ^ 2 * S3 * X ^ 4 - 2 * B ^ 2 * S4 * X ^ 3 -
    B ^ 2 * S5 * X ^ 2 + 2 * B * S2 ^ 2 * X ^ 4 +
    2 * B * S2 * S3 * X ^ 3 + 2 * B * S2 * S4 * X ^ 2 -
    2 * B * S2 * S5 * X + 2 * B * S3 * S4 * X +
    B * S3 * S5 - B * S4 ^ 2 - S2 ^ 2 * S3 * X ^ 2 +
    2 * S2 ^ 2 * S4 * X - S2 ^ 2 * S5 -
    2 * S2 * S3 ^ 2 * X + 2 * S2 * S3 * S4 - S3 ^ 3

theorem X_six_mul_gesselHeightSixSeries :
    X ^ 6 * gesselHeightSixSeries =
      gesselHeightSixScaledExpression
        (literalBesselJ 0) (literalBesselJ 1)
        (X * literalBesselJ 2) (X ^ 2 * literalBesselJ 3)
        (X ^ 3 * literalBesselJ 4) (X ^ 4 * literalBesselJ 5) := by
  unfold gesselHeightSixSeries gesselHeightSixScaledExpression
  ring

theorem X_sq_mul_literalBesselJ_three :
    X ^ 2 * literalBesselJ 3 =
      X ^ 2 * literalBesselJ 1 - 2 * X * literalBesselJ 0 +
        2 * literalBesselJ 1 := by
  have hrec0 := literalBesselJ_recurrence 0
  have hrec1 := literalBesselJ_recurrence 1
  norm_num at hrec0 hrec1
  linear_combination X * hrec1 - 2 * hrec0

theorem X_cube_mul_literalBesselJ_four :
    X ^ 3 * literalBesselJ 4 =
      X ^ 3 * literalBesselJ 0 - 4 * X ^ 2 * literalBesselJ 1 +
        6 * X * literalBesselJ 0 - 6 * literalBesselJ 1 := by
  have hrec0 := literalBesselJ_recurrence 0
  have hrec2 := literalBesselJ_recurrence 2
  have hscaled3 := X_sq_mul_literalBesselJ_three
  norm_num at hrec0 hrec2
  linear_combination X ^ 2 * hrec2 + X ^ 2 * hrec0 - 3 * hscaled3

theorem X_four_mul_literalBesselJ_five :
    X ^ 4 * literalBesselJ 5 =
      X ^ 4 * literalBesselJ 1 - 6 * X ^ 3 * literalBesselJ 0 +
        18 * X ^ 2 * literalBesselJ 1 - 24 * X * literalBesselJ 0 +
        24 * literalBesselJ 1 := by
  have hrec3 := literalBesselJ_recurrence 3
  have hscaled3 := X_sq_mul_literalBesselJ_three
  have hscaled4 := X_cube_mul_literalBesselJ_four
  norm_num at hrec3
  linear_combination X ^ 3 * hrec3 + X ^ 2 * hscaled3 - 4 * hscaled4

theorem gesselHeightSixSeries_eq_besselSeries :
    gesselHeightSixSeries = heightSixBesselSeries := by
  apply PowerSeries.X_pow_mul_cancel (k := 6)
  rw [heightSixBesselNumerator_factor, X_six_mul_gesselHeightSixSeries]
  rw [show X * literalBesselJ 2 =
      X * literalBesselJ 0 - literalBesselJ 1 by
        simpa using literalBesselJ_recurrence 0,
    X_sq_mul_literalBesselJ_three,
    X_cube_mul_literalBesselJ_four,
    X_four_mul_literalBesselJ_five]
  rw [heightSixBesselNumerator_eq_X_sq_core, heightSixBesselCore,
    literalBesselJ_zero, literalBesselJ_one]
  unfold gesselHeightSixScaledExpression
  rw [← X_mul_besselJ1DivX]
  ring

end FibonacciRibbonKernel
