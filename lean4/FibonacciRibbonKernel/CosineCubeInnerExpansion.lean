import FibonacciRibbonKernel.CosineCubeFubini

namespace FibonacciRibbonKernel

open MeasureTheory
open scoped BigOperators

noncomputable def cosineCubePlusInnerTerm
    (plusPower minusPower power : ℕ) (angle : ℝ)
    (index : Fin (power + 1))
    (tail : Fin (plusPower + minusPower) → ℝ) : ℝ :=
  ((Nat.choose power index.val : ℝ) *
      (2 * Real.cos angle) ^ (power - index.val) *
      cosineFactorWeight true angle) *
    cosineCubeRawIntegrand plusPower minusPower index.val tail

theorem integrable_cosineCubePlusInnerTerm
    (plusPower minusPower power : ℕ) (angle : ℝ)
    (index : Fin (power + 1)) :
    Integrable (cosineCubePlusInnerTerm plusPower minusPower power angle index)
      (cosineCubeProductMeasure (plusPower + minusPower)) := by
  unfold cosineCubePlusInnerTerm
  exact (integrable_cosineCubeRawIntegrand
    plusPower minusPower index.val).const_mul _

theorem cosineCubeRawIntegrand_plus_eq_inner_sum
    (plusPower minusPower power : ℕ) (angle : ℝ)
    (tail : Fin (plusPower + minusPower) → ℝ) :
    cosineCubeRawIntegrand (plusPower + 1) minusPower power
        (cosinePlusCons plusPower minusPower angle tail) =
      ∑ index : Fin (power + 1),
        cosineCubePlusInnerTerm plusPower minusPower power angle index tail := by
  rw [cosineCubeRawIntegrand_plus_finCons]
  rw [add_comm (2 * Real.cos angle), add_pow]
  rw [← Fin.sum_univ_eq_sum_range]
  unfold cosineCubePlusInnerTerm cosineCubeRawIntegrand
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro index _hindex
  ring

theorem cosineCubeRawInner_plus_expand
    (plusPower minusPower power : ℕ) (angle : ℝ) :
    (∫ tail : Fin (plusPower + minusPower) → ℝ,
        cosineCubeRawIntegrand (plusPower + 1) minusPower power
          (cosinePlusCons plusPower minusPower angle tail)
        ∂cosineCubeProductMeasure (plusPower + minusPower)) =
      cosineFactorWeight true angle *
        ∑ index : Fin (power + 1),
          (Nat.choose power index.val : ℝ) *
            (2 * Real.cos angle) ^ (power - index.val) *
            (∫ tail : Fin (plusPower + minusPower) → ℝ,
              cosineCubeRawIntegrand plusPower minusPower index.val tail
              ∂cosineCubeProductMeasure (plusPower + minusPower)) := by
  calc
    _ = ∫ tail : Fin (plusPower + minusPower) → ℝ,
        ∑ index : Fin (power + 1),
          cosineCubePlusInnerTerm plusPower minusPower power angle index tail
        ∂cosineCubeProductMeasure (plusPower + minusPower) := by
      apply integral_congr_ae
      filter_upwards with tail
      exact cosineCubeRawIntegrand_plus_eq_inner_sum
        plusPower minusPower power angle tail
    _ = ∑ index : Fin (power + 1),
        ∫ tail : Fin (plusPower + minusPower) → ℝ,
          cosineCubePlusInnerTerm plusPower minusPower power angle index tail
          ∂cosineCubeProductMeasure (plusPower + minusPower) := by
      rw [integral_finsetSum]
      intro index _hindex
      exact integrable_cosineCubePlusInnerTerm
        plusPower minusPower power angle index
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro index _hindex
      unfold cosineCubePlusInnerTerm
      rw [integral_const_mul]
      ring

noncomputable def cosineCubeMinusInnerTerm
    (minusPower power : ℕ) (angle : ℝ) (index : Fin (power + 1))
    (tail : Fin (0 + minusPower) → ℝ) : ℝ :=
  ((Nat.choose power index.val : ℝ) *
      (2 * Real.cos angle) ^ (power - index.val) *
      cosineFactorWeight false angle) *
    cosineCubeRawIntegrand 0 minusPower index.val tail

theorem integrable_cosineCubeMinusInnerTerm
    (minusPower power : ℕ) (angle : ℝ) (index : Fin (power + 1)) :
    Integrable (cosineCubeMinusInnerTerm minusPower power angle index)
      (cosineCubeProductMeasure (0 + minusPower)) := by
  unfold cosineCubeMinusInnerTerm
  exact (integrable_cosineCubeRawIntegrand 0 minusPower index.val).const_mul _

theorem cosineCubeRawIntegrand_minus_eq_inner_sum
    (minusPower power : ℕ) (angle : ℝ)
    (tail : Fin (0 + minusPower) → ℝ) :
    cosineCubeRawIntegrand 0 (minusPower + 1) power
        (cosineMinusCons minusPower angle tail) =
      ∑ index : Fin (power + 1),
        cosineCubeMinusInnerTerm minusPower power angle index tail := by
  rw [cosineCubeRawIntegrand_minus_finCons]
  rw [add_comm (2 * Real.cos angle), add_pow]
  rw [← Fin.sum_univ_eq_sum_range]
  unfold cosineCubeMinusInnerTerm cosineCubeRawIntegrand
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro index _hindex
  ring

theorem cosineCubeRawInner_minus_expand
    (minusPower power : ℕ) (angle : ℝ) :
    (∫ tail : Fin (0 + minusPower) → ℝ,
        cosineCubeRawIntegrand 0 (minusPower + 1) power
          (cosineMinusCons minusPower angle tail)
        ∂cosineCubeProductMeasure (0 + minusPower)) =
      cosineFactorWeight false angle *
        ∑ index : Fin (power + 1),
          (Nat.choose power index.val : ℝ) *
            (2 * Real.cos angle) ^ (power - index.val) *
            (∫ tail : Fin (0 + minusPower) → ℝ,
              cosineCubeRawIntegrand 0 minusPower index.val tail
              ∂cosineCubeProductMeasure (0 + minusPower)) := by
  calc
    _ = ∫ tail : Fin (0 + minusPower) → ℝ,
        ∑ index : Fin (power + 1),
          cosineCubeMinusInnerTerm minusPower power angle index tail
        ∂cosineCubeProductMeasure (0 + minusPower) := by
      apply integral_congr_ae
      filter_upwards with tail
      exact cosineCubeRawIntegrand_minus_eq_inner_sum
        minusPower power angle tail
    _ = ∑ index : Fin (power + 1),
        ∫ tail : Fin (0 + minusPower) → ℝ,
          cosineCubeMinusInnerTerm minusPower power angle index tail
          ∂cosineCubeProductMeasure (0 + minusPower) := by
      rw [integral_finsetSum]
      intro index _hindex
      exact integrable_cosineCubeMinusInnerTerm minusPower power angle index
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro index _hindex
      unfold cosineCubeMinusInnerTerm
      rw [integral_const_mul]
      ring

end FibonacciRibbonKernel
