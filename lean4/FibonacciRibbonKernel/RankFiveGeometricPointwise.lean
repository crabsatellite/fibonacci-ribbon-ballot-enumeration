import FibonacciRibbonKernel.RankFiveFullLimit

namespace FibonacciRibbonKernel

open Filter
open scoped BigOperators

noncomputable def normalizedRankFiveGeometricKernel
    (coordinates : Fin 2 → ℝ) (index : ℕ) : ℝ :=
  (oddCosineSumScale coordinates index / 5) ^ index

theorem tendsto_log_oddCosineSum_microscopic_five
    (coordinates : Fin 2 → ℝ) :
    Tendsto
      (fun index : ℕ =>
        (index + 1 : ℝ) *
          (Real.log (oddCosineSumScale coordinates index) - Real.log 5))
      atTop
      (nhds ((-∑ coordinate, coordinates coordinate ^ 2) / 5)) := by
  have hderiv : HasDerivAt Real.log (1 / 5) 5 := by
    simpa using Real.hasDerivAt_log (by norm_num : (5 : ℝ) ≠ 0)
  have h := tendsto_variable_microscopic_derivative hderiv
    (tendsto_cosineSumDisplacement coordinates)
  have h' : Tendsto
      (fun index : ℕ =>
        (index + 1 : ℝ) *
          (Real.log (5 + cosineSumDisplacement coordinates index /
            (index + 1 : ℝ)) - Real.log 5))
      atTop (nhds ((-∑ coordinate, coordinates coordinate ^ 2) / 5)) := by
    simpa only [div_eq_mul_inv, one_mul] using h
  apply h'.congr'
  filter_upwards with index
  rw [oddCosineSumScale_displacement]
  norm_num

theorem tendsto_rankFiveGeometricRatio_pow_succ
    (coordinates : Fin 2 → ℝ) :
    Tendsto
      (fun index : ℕ =>
        (oddCosineSumScale coordinates index / 5) ^ (index + 1))
      atTop
      (nhds (Real.exp
        ((-∑ coordinate, coordinates coordinate ^ 2) / 5))) := by
  have hlog := tendsto_log_oddCosineSum_microscopic_five coordinates
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hlog
  have hscale := tendsto_oddCosineSumScale coordinates
  have heventuallyPositive : ∀ᶠ index : ℕ in atTop,
      0 < oddCosineSumScale coordinates index :=
    (tendsto_order.1 hscale).1 0 (by norm_num)
  apply hexp.congr'
  filter_upwards [heventuallyPositive] with index hindex
  have hratio : 0 < oddCosineSumScale coordinates index / 5 := by positivity
  simp only [Function.comp_apply]
  rw [← Real.exp_log hratio, ← Real.exp_nat_mul,
    Real.log_div hindex.ne' (by norm_num : (5 : ℝ) ≠ 0)]
  push_cast
  rfl

theorem tendsto_normalizedRankFiveGeometricKernel
    (coordinates : Fin 2 → ℝ) :
    Tendsto (fun index => normalizedRankFiveGeometricKernel coordinates index)
      atTop
      (nhds (Real.exp
        ((-∑ coordinate, coordinates coordinate ^ 2) / 5))) := by
  have hpow := tendsto_rankFiveGeometricRatio_pow_succ coordinates
  have hratio : Tendsto
      (fun index => oddCosineSumScale coordinates index / 5)
      atTop (nhds 1) := by
    have h := (tendsto_oddCosineSumScale coordinates).div_const 5
    norm_num at h ⊢
    exact h
  have hinverse := hratio.inv₀ (by norm_num)
  have hproduct := hpow.mul hinverse
  rw [inv_one, mul_one] at hproduct
  have heventuallyPositive : ∀ᶠ index : ℕ in atTop,
      0 < oddCosineSumScale coordinates index :=
    (tendsto_order.1 (tendsto_oddCosineSumScale coordinates)).1 0 (by norm_num)
  unfold normalizedRankFiveGeometricKernel
  apply hproduct.congr'
  filter_upwards [heventuallyPositive] with index hindex
  have hratioNe : oddCosineSumScale coordinates index / 5 ≠ 0 := by
    positivity
  rw [pow_succ]
  field_simp

end FibonacciRibbonKernel
