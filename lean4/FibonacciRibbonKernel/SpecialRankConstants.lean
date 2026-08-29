import FibonacciRibbonKernel.FixedRankLocalGeometry
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace FibonacciRibbonKernel

theorem fixedRankExponent_four : fixedRankExponent 4 = 3 := by
  norm_num [fixedRankExponent]

theorem fixedRankExponent_five : fixedRankExponent 5 = 5 := by
  norm_num [fixedRankExponent]

theorem fixedRankExponent_six : fixedRankExponent 6 = 15 / 2 := by
  norm_num [fixedRankExponent]

theorem fixedRankGrowth_four :
    fixedRankGrowth 4 = 2 + Real.sqrt 3 := by
  rw [fixedRankGrowth]
  norm_num
  have hsqrt : Real.sqrt (12 : ℝ) = 2 * Real.sqrt 3 := by
    calc
      Real.sqrt (12 : ℝ) = Real.sqrt (4 * 3) := by norm_num
      _ = Real.sqrt 4 * Real.sqrt 3 := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 4)]
      _ = 2 * Real.sqrt 3 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2)]
  rw [hsqrt]
  ring

theorem fixedRankGrowth_five :
    fixedRankGrowth 5 = (5 + Real.sqrt 21) / 2 := by
  rw [fixedRankGrowth]
  norm_num

theorem fixedRankGrowth_six :
    fixedRankGrowth 6 = 3 + 2 * Real.sqrt 2 := by
  rw [fixedRankGrowth]
  norm_num
  have hsqrt : Real.sqrt (32 : ℝ) = 4 * Real.sqrt 2 := by
    calc
      Real.sqrt (32 : ℝ) = Real.sqrt (16 * 2) := by norm_num
      _ = Real.sqrt 16 * Real.sqrt 2 := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 16)]
      _ = 4 * Real.sqrt 2 := by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num,
          Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 4)]
  rw [hsqrt]
  ring

theorem gamma_three_halves :
    Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
  have hhalf : (1 / 2 : ℝ) ≠ 0 := by norm_num
  have hrec := Real.Gamma_add_one hhalf
  rw [show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num,
    Real.Gamma_one_half_eq] at hrec
  nlinarith

theorem gamma_two : Real.Gamma 2 = 1 := by
  convert Real.Gamma_nat_eq_factorial 1 using 1 <;> norm_num

theorem gamma_five_halves :
    Real.Gamma (5 / 2) = 3 * Real.sqrt Real.pi / 4 := by
  have hthree : (3 / 2 : ℝ) ≠ 0 := by norm_num
  have hrec := Real.Gamma_add_one hthree
  rw [show (3 / 2 : ℝ) + 1 = 5 / 2 by norm_num,
    gamma_three_halves] at hrec
  nlinarith

theorem gamma_three : Real.Gamma 3 = 2 := by
  convert Real.Gamma_nat_eq_factorial 2 using 1 <;> norm_num

theorem gamma_seven_halves :
    Real.Gamma (7 / 2) = 15 * Real.sqrt Real.pi / 8 := by
  have hfive : (5 / 2 : ℝ) ≠ 0 := by norm_num
  have hrec := Real.Gamma_add_one hfive
  rw [show (5 / 2 : ℝ) + 1 = 7 / 2 by norm_num,
    gamma_five_halves] at hrec
  nlinarith

theorem gamma_four : Real.Gamma 4 = 6 := by
  convert Real.Gamma_nat_eq_factorial 3 using 1 <;> norm_num

theorem regevConstant_four :
    regevConstant 4 = 32 / Real.pi := by
  rw [regevConstant]
  norm_num [fixedRankExponent, Finset.prod_range_succ]
  rw [gamma_three_halves, gamma_five_halves]
  have hsqrt : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
    Real.sq_sqrt Real.pi_nonneg
  have hsqrtNe : Real.sqrt Real.pi ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  nlinarith

theorem regevConstant_five :
    regevConstant 5 = 9375 / (8 * Real.pi) := by
  rw [regevConstant]
  norm_num [fixedRankExponent, Finset.prod_range_succ]
  rw [gamma_three_halves, gamma_five_halves, gamma_seven_halves]
  have hsqrt : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
    Real.sq_sqrt Real.pi_nonneg
  have hsqrtNe : Real.sqrt Real.pi ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  nlinarith

theorem pi_rpow_three_halves :
    Real.pi ^ (3 / 2 : ℝ) = Real.pi * Real.sqrt Real.pi := by
  calc
    Real.pi ^ (3 / 2 : ℝ) = Real.pi ^ ((1 : ℝ) + 1 / 2) := by norm_num
    _ = Real.pi ^ (1 : ℝ) * Real.pi ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_add Real.pi_pos]
    _ = Real.pi * Real.sqrt Real.pi := by
      rw [Real.rpow_one, Real.sqrt_eq_rpow]

theorem regevConstant_six :
    regevConstant 6 =
      (3 / 4 : ℝ) * 6 ^ (15 / 2 : ℝ) /
        Real.pi ^ (3 / 2 : ℝ) := by
  rw [regevConstant]
  norm_num [fixedRankExponent, Finset.prod_range_succ]
  rw [gamma_three_halves, gamma_five_halves, gamma_seven_halves,
    pi_rpow_three_halves]
  have hsqrt : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
    Real.sq_sqrt Real.pi_nonneg
  have hsqrtNe : Real.sqrt Real.pi ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring_nf at hsqrt ⊢
  nlinarith

/-- The fixed-rank constant after the manuscript substitution transfer. -/
noncomputable def transferredFixedRankConstant (alphabetSize : ℕ) : ℝ :=
  regevConstant alphabetSize * fixedRankGrowth alphabetSize / alphabetSize *
    (Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4) / alphabetSize) ^
      (fixedRankExponent alphabetSize - 1)

theorem transferredFixedRankConstant_four :
    transferredFixedRankConstant 4 =
      6 * (2 + Real.sqrt 3) / Real.pi := by
  rw [transferredFixedRankConstant, regevConstant_four,
    fixedRankGrowth_four, fixedRankExponent_four]
  norm_num [Real.rpow_two]
  have hsqrt : Real.sqrt (12 : ℝ) = 2 * Real.sqrt 3 := by
    calc
      Real.sqrt (12 : ℝ) = Real.sqrt (4 * 3) := by norm_num
      _ = Real.sqrt 4 * Real.sqrt 3 := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 4)]
      _ = 2 * Real.sqrt 3 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2)]
  rw [hsqrt]
  have hsqrtSq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
    Real.sq_sqrt (by positivity)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  nlinarith

theorem transferredFixedRankConstant_five :
    transferredFixedRankConstant 5 =
      1323 * fixedRankGrowth 5 / (8 * Real.pi) := by
  rw [transferredFixedRankConstant, regevConstant_five,
    fixedRankExponent_five]
  norm_num [Real.rpow_natCast]
  have hsqrtSq : (Real.sqrt (21 : ℝ)) ^ 2 = 21 :=
    Real.sq_sqrt (by positivity)
  have hsqrtFourth : (Real.sqrt (21 : ℝ)) ^ 4 = 441 := by
    calc
      (Real.sqrt (21 : ℝ)) ^ 4 =
          ((Real.sqrt (21 : ℝ)) ^ 2) ^ 2 := by ring
      _ = 441 := by rw [hsqrtSq]; norm_num
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [div_pow, hsqrtFourth]
  field_simp
  ring

theorem six_local_scale_power_identity :
    6 ^ (15 / 2 : ℝ) / 6 *
        (Real.sqrt (32 : ℝ) / 6) ^ (13 / 2 : ℝ) =
      2 ^ (65 / 4 : ℝ) := by
  have hsqrt : Real.sqrt (32 : ℝ) = 4 * Real.sqrt 2 := by
    calc
      Real.sqrt (32 : ℝ) = Real.sqrt (16 * 2) := by norm_num
      _ = Real.sqrt 16 * Real.sqrt 2 := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 16)]
      _ = 4 * Real.sqrt 2 := by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num,
          Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 4)]
  have htwoThreeHalves :
      (2 : ℝ) ^ (3 / 2 : ℝ) = 2 * Real.sqrt 2 := by
    calc
      (2 : ℝ) ^ (3 / 2 : ℝ) =
          2 ^ ((1 : ℝ) + 1 / 2) := by norm_num
      _ = 2 ^ (1 : ℝ) * 2 ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_add (by positivity)]
      _ = 2 * Real.sqrt 2 := by
        rw [Real.rpow_one, Real.sqrt_eq_rpow]
  have hscale :
      Real.sqrt (32 : ℝ) / 6 =
        (2 : ℝ) ^ (3 / 2 : ℝ) / 3 := by
    rw [hsqrt, htwoThreeHalves]
    ring
  rw [hscale]
  rw [show (6 : ℝ) = 2 * 3 by norm_num,
    Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ 3),
    Real.div_rpow (by positivity : (0 : ℝ) ≤ 2 ^ (3 / 2 : ℝ))
      (by positivity : (0 : ℝ) ≤ 3)]
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2)
    (3 / 2 : ℝ) (13 / 2 : ℝ)]
  norm_num only at *
  have htwo :
      (2 : ℝ) ^ (15 / 2 : ℝ) * 2 ^ (39 / 4 : ℝ) =
        2 ^ (69 / 4 : ℝ) := by
    rw [← Real.rpow_add (by positivity : (0 : ℝ) < 2)]
    congr 1
    norm_num
  have hthree :
      (3 : ℝ) ^ (15 / 2 : ℝ) =
        3 * 3 ^ (13 / 2 : ℝ) := by
    calc
      (3 : ℝ) ^ (15 / 2 : ℝ) = 3 ^ ((1 : ℝ) + 13 / 2) := by norm_num
      _ = 3 ^ (1 : ℝ) * 3 ^ (13 / 2 : ℝ) := by
        rw [Real.rpow_add (by positivity)]
      _ = 3 * 3 ^ (13 / 2 : ℝ) := by rw [Real.rpow_one]
  have htwoShift :
      (2 : ℝ) ^ (69 / 4 : ℝ) =
        2 * 2 ^ (65 / 4 : ℝ) := by
    calc
      (2 : ℝ) ^ (69 / 4 : ℝ) = 2 ^ ((1 : ℝ) + 65 / 4) := by norm_num
      _ = 2 ^ (1 : ℝ) * 2 ^ (65 / 4 : ℝ) := by
        rw [Real.rpow_add (by positivity)]
      _ = 2 * 2 ^ (65 / 4 : ℝ) := by rw [Real.rpow_one]
  calc
    (2 : ℝ) ^ (15 / 2 : ℝ) * (3 : ℝ) ^ (15 / 2 : ℝ) / 6 *
          ((2 : ℝ) ^ (39 / 4 : ℝ) / (3 : ℝ) ^ (13 / 2 : ℝ)) =
        ((2 : ℝ) ^ (15 / 2 : ℝ) * (2 : ℝ) ^ (39 / 4 : ℝ)) *
          ((3 : ℝ) ^ (15 / 2 : ℝ) /
            ((6 : ℝ) * (3 : ℝ) ^ (13 / 2 : ℝ))) := by ring
    _ = (2 : ℝ) ^ (69 / 4 : ℝ) *
          (((3 : ℝ) * (3 : ℝ) ^ (13 / 2 : ℝ)) /
            ((6 : ℝ) * (3 : ℝ) ^ (13 / 2 : ℝ))) := by rw [htwo, hthree]
    _ = (2 : ℝ) ^ (65 / 4 : ℝ) := by
      rw [htwoShift]
      have hthreeNe : (3 : ℝ) ^ (13 / 2 : ℝ) ≠ 0 := by positivity
      field_simp
      norm_num

theorem transferredFixedRankConstant_six :
    transferredFixedRankConstant 6 =
      3 * 2 ^ (57 / 4 : ℝ) * fixedRankGrowth 6 /
        Real.pi ^ (3 / 2 : ℝ) := by
  rw [transferredFixedRankConstant, regevConstant_six,
    fixedRankExponent_six]
  norm_num only
  have hscale := six_local_scale_power_identity
  have htwoShift :
      (2 : ℝ) ^ (65 / 4 : ℝ) =
        4 * 2 ^ (57 / 4 : ℝ) := by
    calc
      (2 : ℝ) ^ (65 / 4 : ℝ) = 2 ^ ((2 : ℝ) + 57 / 4) := by norm_num
      _ = 2 ^ (2 : ℝ) * 2 ^ (57 / 4 : ℝ) := by
        rw [Real.rpow_add (by positivity)]
      _ = 4 * 2 ^ (57 / 4 : ℝ) := by norm_num [Real.rpow_two]
  have hpiPow : Real.pi ^ (3 / 2 : ℝ) ≠ 0 := by positivity
  calc
    (3 / 4 : ℝ) * 6 ^ (15 / 2 : ℝ) /
          Real.pi ^ (3 / 2 : ℝ) * fixedRankGrowth 6 / 6 *
        (Real.sqrt 32 / 6) ^ (13 / 2 : ℝ) =
      (3 / 4 : ℝ) * fixedRankGrowth 6 /
          Real.pi ^ (3 / 2 : ℝ) *
        (6 ^ (15 / 2 : ℝ) / 6 *
          (Real.sqrt 32 / 6) ^ (13 / 2 : ℝ)) := by ring
    _ = (3 / 4 : ℝ) * fixedRankGrowth 6 /
          Real.pi ^ (3 / 2 : ℝ) * 2 ^ (65 / 4 : ℝ) := by rw [hscale]
    _ = 3 * 2 ^ (57 / 4 : ℝ) * fixedRankGrowth 6 /
          Real.pi ^ (3 / 2 : ℝ) := by rw [htwoShift]; ring

end FibonacciRibbonKernel
