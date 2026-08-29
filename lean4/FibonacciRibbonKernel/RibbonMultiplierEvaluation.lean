import FibonacciRibbonKernel.GeneralizedBinomialConvergence
import Mathlib.Analysis.Normed.Ring.InfiniteSum

namespace FibonacciRibbonKernel

open PowerSeries

/-!
# Evaluation and absolute convergence of the ribbon analytic multiplier

The explicit multiplier from `RibbonAnalyticMultiplier` is evaluated as an
absolutely convergent double generalized-binomial series.  Keeping the pair
index `(i,j)` records the exact coefficient shift `i+2j`, which is the carrier
consumed by the convolution-transfer theorem.
-/

noncomputable def ribbonSecondaryWeightedTerm
    (parameter rho x : ℝ) (index : ℕ) : ℝ :=
  PowerSeries.coeff index (rescaledBinomialSeries parameter rho) * x ^ index

noncomputable def ribbonDenominatorWeightedTerm
    (parameter x : ℝ) (index : ℕ) : ℝ :=
  Ring.choose (-(parameter + 1)) index * (x ^ 2) ^ index

noncomputable def ribbonMultiplierPairWeightedTerm
    (parameter rho x : ℝ) (pair : ℕ × ℕ) : ℝ :=
  ribbonSecondaryWeightedTerm parameter rho x pair.1 *
    ribbonDenominatorWeightedTerm parameter x pair.2

noncomputable def ribbonMultiplierPairCoefficient
    (parameter rho : ℝ) (pair : ℕ × ℕ) : ℝ :=
  PowerSeries.coeff pair.1 (rescaledBinomialSeries parameter rho) *
    Ring.choose (-(parameter + 1)) pair.2

def ribbonMultiplierPairShift (pair : ℕ × ℕ) : ℕ :=
  pair.1 + 2 * pair.2

theorem ribbonMultiplierPairWeightedTerm_eq
    (parameter rho x : ℝ) (pair : ℕ × ℕ) :
    ribbonMultiplierPairWeightedTerm parameter rho x pair =
      ribbonMultiplierPairCoefficient parameter rho pair *
        x ^ ribbonMultiplierPairShift pair := by
  unfold ribbonMultiplierPairWeightedTerm ribbonSecondaryWeightedTerm
  unfold ribbonDenominatorWeightedTerm ribbonMultiplierPairCoefficient
  unfold ribbonMultiplierPairShift
  rw [pow_add, pow_mul]
  ring

theorem ribbonSecondaryWeighted_hasSum
    (parameter rho x : ℝ) (hproduct : |rho * x| < 1) :
    HasSum (ribbonSecondaryWeightedTerm parameter rho x)
      ((1 - rho * x) ^ parameter) := by
  have hsum := generalizedBinomial_hasSum parameter (-rho * x) (by
    simpa [abs_mul] using hproduct)
  convert hsum using 1
  · funext index
    unfold ribbonSecondaryWeightedTerm
    rw [rescaledBinomialSeries_coeff]
    rw [show (-rho * x) ^ index = (-rho) ^ index * x ^ index by
      rw [mul_pow]]
    ring
  · congr 1
    ring

theorem ribbonSecondaryWeighted_summable_abs
    (parameter rho x : ℝ) (hproduct : |rho * x| < 1) :
    Summable (fun index : ℕ =>
      |ribbonSecondaryWeightedTerm parameter rho x index|) := by
  have hsum := generalizedBinomial_summable_abs parameter (-rho * x) (by
    simpa [abs_mul] using hproduct)
  apply hsum.congr
  intro index
  congr 1
  unfold ribbonSecondaryWeightedTerm
  rw [rescaledBinomialSeries_coeff]
  rw [show (-rho * x) ^ index = (-rho) ^ index * x ^ index by
    rw [mul_pow]]
  ring

theorem ribbonDenominatorWeighted_hasSum
    (parameter x : ℝ) (hx : |x| < 1) :
    HasSum (ribbonDenominatorWeightedTerm parameter x)
      ((1 + x ^ 2) ^ (-(parameter + 1))) := by
  have hxSq : |x ^ 2| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg x) hx (by omega)
  convert generalizedBinomial_hasSum (-(parameter + 1)) (x ^ 2) hxSq using 1
  · funext index
    unfold ribbonDenominatorWeightedTerm
    rfl

theorem ribbonDenominatorWeighted_summable_abs
    (parameter x : ℝ) (hx : |x| < 1) :
    Summable (fun index : ℕ =>
      |ribbonDenominatorWeightedTerm parameter x index|) := by
  have hxSq : |x ^ 2| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg x) hx (by omega)
  convert generalizedBinomial_summable_abs
    (-(parameter + 1)) (x ^ 2) hxSq using 1
  funext index
  unfold ribbonDenominatorWeightedTerm
  rfl

theorem ribbonMultiplierPairWeighted_summable
    (parameter rho x : ℝ) (hproduct : |rho * x| < 1)
    (hx : |x| < 1) :
    Summable (ribbonMultiplierPairWeightedTerm parameter rho x) := by
  have hsecondary := ribbonSecondaryWeighted_summable_abs
    parameter rho x hproduct
  have hdenominator := ribbonDenominatorWeighted_summable_abs parameter x hx
  unfold ribbonMultiplierPairWeightedTerm
  exact summable_mul_of_summable_norm hsecondary hdenominator

theorem ribbonMultiplierPairWeighted_summable_abs
    (parameter rho x : ℝ) (hproduct : |rho * x| < 1)
    (hx : |x| < 1) :
    Summable (fun pair : ℕ × ℕ =>
      |ribbonMultiplierPairWeightedTerm parameter rho x pair|) := by
  have hsecondary := ribbonSecondaryWeighted_summable_abs
    parameter rho x hproduct
  have hdenominator := ribbonDenominatorWeighted_summable_abs parameter x hx
  have hproductAbs : Summable (fun pair : ℕ × ℕ =>
      |ribbonSecondaryWeightedTerm parameter rho x pair.1| *
        |ribbonDenominatorWeightedTerm parameter x pair.2|) := by
    exact hsecondary.mul_of_nonneg hdenominator
      (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)
  apply hproductAbs.congr
  intro pair
  unfold ribbonMultiplierPairWeightedTerm
  rw [abs_mul]

theorem ribbonMultiplierPairWeighted_hasSum
    (parameter rho x : ℝ) (hproduct : |rho * x| < 1)
    (hx : |x| < 1) :
    HasSum (ribbonMultiplierPairWeightedTerm parameter rho x)
      ((1 - rho * x) ^ parameter *
        (1 + x ^ 2) ^ (-(parameter + 1))) := by
  have hsecondary := ribbonSecondaryWeighted_hasSum
    parameter rho x hproduct
  have hdenominator := ribbonDenominatorWeighted_hasSum parameter x hx
  exact hsecondary.mul hdenominator
    (ribbonMultiplierPairWeighted_summable parameter rho x hproduct hx)

theorem fixedRankPreimage_abs_lt_one
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    |fixedRankPreimage alphabetSize| < 1 := by
  rw [abs_of_pos (fixedRankPreimage_pos alphabetSize hsize)]
  exact fixedRankPreimage_lt_one alphabetSize hsize

theorem fixedRankPreimage_sq_abs_lt_one
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    |fixedRankPreimage alphabetSize * fixedRankPreimage alphabetSize| < 1 := by
  rw [abs_mul]
  rw [abs_of_pos (fixedRankPreimage_pos alphabetSize hsize)]
  have hpos := fixedRankPreimage_pos alphabetSize hsize
  have hlt := fixedRankPreimage_lt_one alphabetSize hsize
  nlinarith

/-- Exact value of the analytic multiplier at the leading preimage. -/
theorem ribbonMultiplierPairWeighted_at_preimage_hasSum
    (parameter : ℝ) (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    HasSum
      (ribbonMultiplierPairWeightedTerm parameter
        (fixedRankPreimage alphabetSize)
        (fixedRankPreimage alphabetSize))
      ((1 - fixedRankPreimage alphabetSize ^ 2) ^ parameter *
        (1 + fixedRankPreimage alphabetSize ^ 2) ^
          (-(parameter + 1))) := by
  simpa [pow_two] using
    ribbonMultiplierPairWeighted_hasSum parameter
      (fixedRankPreimage alphabetSize) (fixedRankPreimage alphabetSize)
        (fixedRankPreimage_sq_abs_lt_one alphabetSize hsize)
        (fixedRankPreimage_abs_lt_one alphabetSize hsize)

theorem fixedRankPreimage_localScale_ratio
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    (1 - fixedRankPreimage alphabetSize ^ 2) /
        (1 + fixedRankPreimage alphabetSize ^ 2) =
      Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4) / alphabetSize := by
  let alpha := fixedRankGrowth alphabetSize
  let rho := fixedRankPreimage alphabetSize
  let root := Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4)
  have hsum : alpha + rho = (alphabetSize : ℝ) :=
    fixedRankGrowth_add_preimage alphabetSize
  have hmul : alpha * rho = 1 :=
    fixedRankGrowth_mul_preimage alphabetSize hsize
  have hdiff : alpha - rho = root := by
    simp only [alpha, rho, root, fixedRankGrowth, fixedRankPreimage]
    ring
  have hrho : 0 < rho := fixedRankPreimage_pos alphabetSize hsize
  have hn : (alphabetSize : ℝ) ≠ 0 := by positivity
  have hdenom : 1 + rho ^ 2 ≠ 0 := by positivity
  have hNrho : (alphabetSize : ℝ) * rho = 1 + rho ^ 2 := by
    calc
      (alphabetSize : ℝ) * rho = (alpha + rho) * rho := by rw [hsum]
      _ = 1 + rho ^ 2 := by rw [add_mul, hmul]; ring
  have hOneMinus : 1 - rho ^ 2 = rho * root := by
    calc
      1 - rho ^ 2 = alpha * rho - rho ^ 2 := by rw [hmul]
      _ = rho * (alpha - rho) := by ring
      _ = rho * root := by rw [hdiff]
  change (1 - rho ^ 2) / (1 + rho ^ 2) =
      root / (alphabetSize : ℝ)
  rw [hOneMinus, ← hNrho]
  field_simp [hn, hrho.ne']

theorem ribbonMultiplierValue_eq_localScale
    (parameter : ℝ) (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    (1 - fixedRankPreimage alphabetSize ^ 2) ^ parameter *
        (1 + fixedRankPreimage alphabetSize ^ 2) ^ (-(parameter + 1)) =
      fixedRankGrowth alphabetSize / alphabetSize *
        (Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4) / alphabetSize) ^
          parameter := by
  let rho := fixedRankPreimage alphabetSize
  have hrhoLt : rho < 1 := fixedRankPreimage_lt_one alphabetSize hsize
  have hrhoPos : 0 < rho := fixedRankPreimage_pos alphabetSize hsize
  have hA : 0 < 1 - rho ^ 2 := by nlinarith
  have hB : 0 < 1 + rho ^ 2 := by positivity
  have hratio :
      (1 - rho ^ 2) / (1 + rho ^ 2) =
        Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4) / alphabetSize :=
    fixedRankPreimage_localScale_ratio alphabetSize hsize
  have hprefactor :
      1 / (1 + rho ^ 2) = fixedRankGrowth alphabetSize / alphabetSize :=
    ribbonPrefactorReal_fixedRankPreimage alphabetSize hsize
  change (1 - rho ^ 2) ^ parameter *
      (1 + rho ^ 2) ^ (-(parameter + 1)) = _
  calc
    (1 - rho ^ 2) ^ parameter *
        (1 + rho ^ 2) ^ (-(parameter + 1)) =
      ((1 - rho ^ 2) / (1 + rho ^ 2)) ^ parameter *
        (1 / (1 + rho ^ 2)) := by
          rw [show -(parameter + 1) = -parameter + -1 by ring,
            Real.rpow_add hB, Real.rpow_neg hB.le,
            Real.rpow_neg_one, Real.div_rpow hA.le hB.le]
          simp only [div_eq_mul_inv, one_mul]
          ring
    _ = fixedRankGrowth alphabetSize / alphabetSize *
        (Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4) / alphabetSize) ^
          parameter := by
            rw [hratio, hprefactor]
            ring

theorem ribbonMultiplierPairWeighted_at_preimage_localScale_hasSum
    (parameter : ℝ) (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    HasSum
      (ribbonMultiplierPairWeightedTerm parameter
        (fixedRankPreimage alphabetSize)
        (fixedRankPreimage alphabetSize))
      (fixedRankGrowth alphabetSize / alphabetSize *
        (Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4) / alphabetSize) ^
          parameter) := by
  rw [← ribbonMultiplierValue_eq_localScale parameter alphabetSize hsize]
  exact ribbonMultiplierPairWeighted_at_preimage_hasSum
    parameter alphabetSize hsize

end FibonacciRibbonKernel
