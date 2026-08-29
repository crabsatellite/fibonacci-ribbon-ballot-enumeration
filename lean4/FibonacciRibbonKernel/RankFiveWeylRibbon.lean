import FibonacciRibbonKernel.RankFiveWeylCount

namespace FibonacciRibbonKernel

theorem heightFiveRibbonCount_eq_normalized_oddWeylFibonacciMoment
    (power : ℕ) :
    (ribbonCount 4 power : ℝ) =
      (8 / Real.pi ^ 2) * oddWeylFibonacciMoment 2 power := by
  symm
  apply oddWeylMoment_count_transfer 2 (by omega) (8 / Real.pi ^ 2)
  intro degree
  exact (heightFiveTableauCount_eq_normalized_oddWeylMoment degree).symm

theorem heightFiveWeylNormalization_pos :
    0 < (8 / Real.pi ^ 2 : ℝ) := by positivity

end FibonacciRibbonKernel
