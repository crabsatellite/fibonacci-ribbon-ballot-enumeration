import FibonacciRibbonKernel.BesselOneFactorAsymptotic
import FibonacciRibbonKernel.FixedRankLocalGeometry

namespace FibonacciRibbonKernel

open Filter Asymptotics

noncomputable def fibonacciScaleKernel (scale : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => scale
  | power + 2 =>
      scale * fibonacciScaleKernel scale (power + 1) -
        fibonacciScaleKernel scale power

@[simp] theorem fibonacciScaleKernel_zero (scale : ℝ) :
    fibonacciScaleKernel scale 0 = 1 := rfl

@[simp] theorem fibonacciScaleKernel_one (scale : ℝ) :
    fibonacciScaleKernel scale 1 = scale := rfl

@[simp] theorem fibonacciScaleKernel_succ_succ (scale : ℝ) (power : ℕ) :
    fibonacciScaleKernel scale (power + 2) =
      scale * fibonacciScaleKernel scale (power + 1) -
        fibonacciScaleKernel scale power := rfl

theorem fibonacciScaleKernel_closed
    (scale alpha rho : ℝ) (hsum : alpha + rho = scale)
    (hproduct : alpha * rho = 1) (hdiff : alpha ≠ rho)
    (power : ℕ) :
    fibonacciScaleKernel scale power =
      (alpha ^ (power + 1) - rho ^ (power + 1)) / (alpha - rho) := by
  induction power using Nat.twoStepInduction with
  | zero =>
      rw [fibonacciScaleKernel_zero]
      simp only [zero_add, pow_one]
      field_simp
  | one =>
      rw [fibonacciScaleKernel_one]
      simp only [one_add_one_eq_two]
      apply (eq_div_iff (sub_ne_zero.mpr hdiff)).2
      rw [← hsum]
      ring
  | more power hzero hone =>
      rw [fibonacciScaleKernel_succ_succ, hzero, hone]
      apply (eq_div_iff (sub_ne_zero.mpr hdiff)).2
      field_simp [sub_ne_zero.mpr hdiff]
      have halpha : rho * alpha ^ (power + 2) = alpha ^ (power + 1) := by
        rw [show power + 2 = (power + 1) + 1 by omega, pow_succ]
        calc
          rho * (alpha ^ (power + 1) * alpha) =
              alpha ^ (power + 1) * (alpha * rho) := by ring
          _ = alpha ^ (power + 1) := by rw [hproduct, mul_one]
      have hrho : alpha * rho ^ (power + 2) = rho ^ (power + 1) := by
        rw [show power + 2 = (power + 1) + 1 by omega, pow_succ]
        calc
          alpha * (rho ^ (power + 1) * rho) =
              rho ^ (power + 1) * (alpha * rho) := by ring
          _ = rho ^ (power + 1) := by rw [hproduct, mul_one]
      rw [← hsum]
      rw [show power + 1 + 1 = power + 2 by omega]
      rw [show power + 2 + 1 = (power + 2) + 1 by omega,
        pow_succ, pow_succ]
      calc
        (alpha + rho) *
              (alpha ^ (power + 2) - rho ^ (power + 2)) -
            (alpha ^ (power + 1) - rho ^ (power + 1)) =
          alpha ^ (power + 2) * alpha - rho ^ (power + 2) * rho +
            (rho * alpha ^ (power + 2) - alpha ^ (power + 1)) -
            (alpha * rho ^ (power + 2) - rho ^ (power + 1)) := by ring
        _ = alpha ^ (power + 2) * alpha - rho ^ (power + 2) * rho := by
          rw [halpha, hrho]
          ring

noncomputable def fixedRankFibonacciKernel
    (alphabetSize power : ℕ) : ℝ :=
  fibonacciScaleKernel alphabetSize power

noncomputable def fixedRankFibonacciKernelLeading
    (alphabetSize power : ℕ) : ℝ :=
  fixedRankGrowth alphabetSize ^ (power + 1) /
    Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4)

theorem fixedRankFibonacciKernel_closed
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) (power : ℕ) :
    fixedRankFibonacciKernel alphabetSize power =
      (fixedRankGrowth alphabetSize ^ (power + 1) -
        fixedRankPreimage alphabetSize ^ (power + 1)) /
      Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4) := by
  unfold fixedRankFibonacciKernel
  have hdiff : fixedRankGrowth alphabetSize -
      fixedRankPreimage alphabetSize =
      Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4) := by
    simp only [fixedRankGrowth, fixedRankPreimage]
    ring
  have hne : fixedRankGrowth alphabetSize ≠
      fixedRankPreimage alphabetSize := by
    intro heq
    have hzero : Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4) = 0 := by
      rw [← hdiff, heq, sub_self]
    exact (fixedRank_sqrt_pos alphabetSize hsize).ne' hzero
  have hclosed := fibonacciScaleKernel_closed (alphabetSize : ℝ)
    (fixedRankGrowth alphabetSize) (fixedRankPreimage alphabetSize)
    (fixedRankGrowth_add_preimage alphabetSize)
    (fixedRankGrowth_mul_preimage alphabetSize hsize) hne power
  rw [hdiff] at hclosed
  exact hclosed

theorem fixedRankPreimage_div_growth_nonneg
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    0 ≤ fixedRankPreimage alphabetSize / fixedRankGrowth alphabetSize := by
  exact (div_pos (fixedRankPreimage_pos alphabetSize hsize)
    (fixedRankGrowth_pos alphabetSize hsize)).le

theorem fixedRankPreimage_div_growth_lt_one
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    fixedRankPreimage alphabetSize / fixedRankGrowth alphabetSize < 1 := by
  rw [div_lt_one (fixedRankGrowth_pos alphabetSize hsize)]
  have hdiff : fixedRankGrowth alphabetSize - fixedRankPreimage alphabetSize =
      Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4) := by
    simp only [fixedRankGrowth, fixedRankPreimage]
    ring
  linarith [fixedRank_sqrt_pos alphabetSize hsize]

theorem fixedRankFibonacciKernel_isEquivalent
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    fixedRankFibonacciKernel alphabetSize ~[atTop]
      fixedRankFibonacciKernelLeading alphabetSize := by
  have hdenominator : ∀ᶠ power : ℕ in atTop,
      fixedRankFibonacciKernelLeading alphabetSize power ≠ 0 := by
    filter_upwards with power
    unfold fixedRankFibonacciKernelLeading
    exact div_ne_zero (pow_ne_zero _
      (fixedRankGrowth_pos alphabetSize hsize).ne')
      (fixedRank_sqrt_pos alphabetSize hsize).ne'
  rw [isEquivalent_iff_tendsto_one hdenominator]
  have hratio := tendsto_pow_atTop_nhds_zero_of_lt_one
    (fixedRankPreimage_div_growth_nonneg alphabetSize hsize)
    (fixedRankPreimage_div_growth_lt_one alphabetSize hsize)
  have hshift := hratio.comp (tendsto_add_atTop_nat 1)
  have htarget : Tendsto
      (fun power : ℕ => 1 -
        (fixedRankPreimage alphabetSize / fixedRankGrowth alphabetSize) ^
          (power + 1)) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hshift
  apply htarget.congr'
  filter_upwards with power
  rw [Pi.div_apply, fixedRankFibonacciKernel_closed alphabetSize hsize]
  unfold fixedRankFibonacciKernelLeading
  have halpha := (fixedRankGrowth_pos alphabetSize hsize).ne'
  have hroot := (fixedRank_sqrt_pos alphabetSize hsize).ne'
  field_simp
  rw [div_pow]
  field_simp

end FibonacciRibbonKernel
