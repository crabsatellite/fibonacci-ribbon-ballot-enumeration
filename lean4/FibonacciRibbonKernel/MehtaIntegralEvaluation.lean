import FibonacciRibbonKernel.SelbergMehtaGammaLimit

namespace FibonacciRibbonKernel

open Filter
open scoped Classical Topology BigOperators

theorem standardMehtaChamberIntegral_evaluation (dimension : ℕ) :
    standardMehtaChamberIntegral dimension =
      expectedMehtaIntegralByDimension dimension := by
  exact tendsto_nhds_unique
    (tendsto_normalizedExpectedSelberg_to_standardMehta dimension)
    (tendsto_normalizedExpectedSelberg_explicit dimension)

theorem expectedMehtaIntegralByDimension_succ (rank : ℕ) :
    expectedMehtaIntegralByDimension (rank + 1) =
      expectedStandardMehtaChamberIntegral rank := by
  rfl

theorem standardMehtaChamberEvaluation_all (rank : ℕ) :
    StandardMehtaChamberEvaluation rank := by
  unfold StandardMehtaChamberEvaluation
  rw [standardMehtaChamberIntegral_evaluation]
  exact expectedMehtaIntegralByDimension_succ rank

theorem regevMehtaChamberEvaluation_all (rank : ℕ) :
    RegevMehtaChamberEvaluation rank :=
  (RegevMehtaChamberEvaluation_iff_standard rank).mpr
    (standardMehtaChamberEvaluation_all rank)

theorem fixedRankUnrestrictedAsymptotic_all
    (rank : ℕ) (hrank : 2 ≤ rank) :
    FixedRankUnrestrictedAsymptotic (rank + 1) :=
  fixedRankUnrestrictedAsymptotic_of_mehta rank hrank
    (regevMehtaChamberEvaluation_all rank)

end FibonacciRibbonKernel
