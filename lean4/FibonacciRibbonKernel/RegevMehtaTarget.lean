import FibonacciRibbonKernel.RegevStirlingRenormalization

namespace FibonacciRibbonKernel

open Filter Asymptotics
open scoped Classical Topology

noncomputable def expectedRegevChamberIntegral (rank : ℕ) : ℝ :=
  regevConstant (rank + 1) / regevIntegralScaleConstant rank

def RegevMehtaChamberEvaluation (rank : ℕ) : Prop :=
  regevFullChamberIntegral rank = expectedRegevChamberIntegral rank

theorem integralLeadingCoefficient_eq_regevConstant_of_mehta
    (rank : ℕ) (hmehta : RegevMehtaChamberEvaluation rank) :
    regevIntegralLeadingCoefficient rank = regevConstant (rank + 1) := by
  unfold RegevMehtaChamberEvaluation expectedRegevChamberIntegral at hmehta
  unfold regevIntegralLeadingCoefficient
  rw [hmehta]
  have hscale : regevIntegralScaleConstant rank ≠ 0 := by
    unfold regevIntegralScaleConstant
    positivity
  field_simp

theorem unrestrictedCount_normalized_tendsto_regevConstant_of_mehta
    (rank : ℕ) (hmehta : RegevMehtaChamberEvaluation rank) :
    Tendsto
      (fun size => (unrestrictedCount rank size : ℝ) /
        generalRegevBaseScale rank size)
      atTop (nhds (regevConstant (rank + 1))) := by
  rw [← integralLeadingCoefficient_eq_regevConstant_of_mehta rank hmehta]
  exact unrestrictedCount_normalized_tendsto_integralCoefficient rank

theorem generalRegevBaseScale_eq_leading_base
    (rank size : ℕ) :
    generalRegevBaseScale rank size =
      ((rank + 1 : ℕ) : ℝ) ^ size *
        (size : ℝ) ^ (-fixedRankExponent (rank + 1)) := rfl

theorem fixedRankUnrestrictedAsymptotic_of_mehta
    (rank : ℕ) (hrank : 2 ≤ rank)
    (hmehta : RegevMehtaChamberEvaluation rank) :
    FixedRankUnrestrictedAsymptotic (rank + 1) := by
  unfold FixedRankUnrestrictedAsymptotic
  have hconstantPos : 0 < regevConstant (rank + 1) :=
    regevConstant_pos (rank + 1) (by omega)
  have hdenominator : ∀ᶠ size : ℕ in atTop,
      fixedRankUnrestrictedLeadingTerm (rank + 1) size ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with size hsize
    unfold fixedRankUnrestrictedLeadingTerm
    positivity
  rw [isEquivalent_iff_tendsto_one hdenominator]
  have hnormalized :=
    unrestrictedCount_normalized_tendsto_regevConstant_of_mehta rank hmehta
  have hdivide := hnormalized.div_const (regevConstant (rank + 1))
  have hlimit : regevConstant (rank + 1) / regevConstant (rank + 1) = 1 :=
    div_self hconstantPos.ne'
  rw [hlimit] at hdivide
  apply hdivide.congr'
  filter_upwards [eventually_ge_atTop 1] with size hsize
  simp only [Pi.div_apply, Nat.add_sub_cancel]
  change ((unrestrictedCount rank size : ℝ) /
      generalRegevBaseScale rank size) /
        regevConstant (rank + 1) =
    (unrestrictedCount rank size : ℝ) /
      fixedRankUnrestrictedLeadingTerm (rank + 1) size
  unfold fixedRankUnrestrictedLeadingTerm generalRegevBaseScale
  have hbase : 0 < ((rank + 1 : ℕ) : ℝ) ^ size *
      (size : ℝ) ^ (-fixedRankExponent (rank + 1)) := by positivity
  field_simp

end FibonacciRibbonKernel
