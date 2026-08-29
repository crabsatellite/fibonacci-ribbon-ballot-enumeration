import FibonacciRibbonKernel.RankThreeAsymptotic

namespace FibonacciRibbonKernel

open Filter Asymptotics

theorem fixedRankRibbonAsymptotic_all
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    FixedRankRibbonAsymptotic alphabetSize := by
  obtain ⟨dimension, rfl | rfl⟩ := Nat.even_or_odd' alphabetSize
  · exact fixedRankRibbonAsymptotic_even_all (by omega)
  · by_cases hone : dimension = 1
    · subst dimension
      norm_num
      exact fixedRankRibbonAsymptotic_three
    · exact fixedRankRibbonAsymptotic_odd_all (by omega)

theorem fixedRankUnrestrictedAsymptotic_all_alphabet
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    FixedRankUnrestrictedAsymptotic alphabetSize := by
  have hrank : 2 ≤ alphabetSize - 1 := by omega
  have h := fixedRankUnrestrictedAsymptotic_all
    (alphabetSize - 1) hrank
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ alphabetSize)] using h

theorem fixedRankDensityAsymptotic_all
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    (fun index : ℕ =>
      (ribbonCount (alphabetSize - 1) index : ℝ) /
        unrestrictedCount (alphabetSize - 1) index)
      ~[atTop] fixedRankDensityLeadingTerm alphabetSize :=
  fixedRankDensityAsymptotic_of_leading_asymptotics alphabetSize hsize
    (fixedRankRibbonAsymptotic_all alphabetSize hsize)
    (fixedRankUnrestrictedAsymptotic_all_alphabet alphabetSize hsize)

theorem fixedRankDensity_tendsto_zero_all
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    Tendsto (fun index : ℕ =>
      (ribbonCount (alphabetSize - 1) index : ℝ) /
        unrestrictedCount (alphabetSize - 1) index)
      atTop (nhds 0) :=
  fixedRankDensity_tendsto_zero_of_leading_asymptotics alphabetSize hsize
    (fixedRankRibbonAsymptotic_all alphabetSize hsize)
    (fixedRankUnrestrictedAsymptotic_all_alphabet alphabetSize hsize)

end FibonacciRibbonKernel
