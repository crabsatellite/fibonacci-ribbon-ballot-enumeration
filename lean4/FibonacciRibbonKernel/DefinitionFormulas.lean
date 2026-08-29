import FibonacciRibbonKernel.GeneratingSubstitution
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace FibonacciRibbonKernel

/-- Manuscript exponent `β_n=n(n-1)/4`. -/
noncomputable def fixedRankExponent (alphabetSize : ℕ) : ℝ :=
  (alphabetSize : ℝ) * (alphabetSize - 1 : ℕ) / 4

/-- Dominant growth root `α_n=(n+√(n²-4))/2`. -/
noncomputable def fixedRankGrowth (alphabetSize : ℕ) : ℝ :=
  ((alphabetSize : ℝ) + Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4)) / 2

/-- The literal Regev--Mehta constant displayed in `eq:regev-constant`. -/
noncomputable def regevConstant (alphabetSize : ℕ) : ℝ :=
  (alphabetSize : ℝ) ^ fixedRankExponent alphabetSize /
      (alphabetSize.factorial : ℝ) *
    ∏ j ∈ Finset.range alphabetSize,
      Real.Gamma (1 + ((j + 1 : ℕ) : ℝ) / 2) /
        Real.Gamma (3 / 2)

theorem regevConstant_formula (alphabetSize : ℕ) :
    regevConstant alphabetSize =
      (alphabetSize : ℝ) ^ fixedRankExponent alphabetSize /
          (alphabetSize.factorial : ℝ) *
        ∏ j ∈ Finset.range alphabetSize,
          Real.Gamma (1 + ((j + 1 : ℕ) : ℝ) / 2) /
            Real.Gamma (3 / 2) := rfl

/-- First row length of a bounded partition. -/
def BoundedPartition.firstRow
    {rank columns : ℕ} (shape : BoundedPartition rank columns) : ℕ :=
  shape.1 0

/--
Literal finite sum `E_s(m)` from `eq:tail-tableaux`.  Rank `m` supplies
`m+1` rows, so every partition of `m` occurs exactly once with trailing zero
rows.
-/
noncomputable def tailTableauSum (tailBound size : ℕ) : ℕ :=
  ∑ shape : BoundedPartition size size,
    if size - shape.firstRow ≤ tailBound then
      standardTableauNumber shape
    else 0

theorem tailTableauSum_formula (tailBound size : ℕ) :
    tailTableauSum tailBound size =
      ∑ shape : BoundedPartition size size,
        if size - shape.firstRow ≤ tailBound then
          standardTableauNumber shape
        else 0 := rfl

end FibonacciRibbonKernel
