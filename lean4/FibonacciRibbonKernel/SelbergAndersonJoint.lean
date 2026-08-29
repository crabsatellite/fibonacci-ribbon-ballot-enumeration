import FibonacciRibbonKernel.SelbergAndersonChain

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped Classical BigOperators

noncomputable def selbergAndersonJointIntegrand (rank : ℕ)
    (alpha beta : ℝ)
    (upper : Fin (rank + 2) → ℝ)
    (lower : Fin (rank + 1) → ℝ) : ℝ :=
  standardMehtaVandermonde (rank + 1) lower *
    dixonAndersonGeneralIntegrand
      (selbergExtendedAnchors rank lower)
      (selbergAndersonParameters rank alpha beta) upper

noncomputable def selbergAndersonCoefficient (rank : ℕ)
    (alpha beta : ℝ) : ℝ :=
  Real.Gamma alpha * Real.Gamma beta *
      Real.Gamma (1 / 2) ^ (rank + 1) /
    Real.Gamma (alpha + beta + ((rank + 1 : ℕ) : ℝ) / 2)

theorem selbergHalfCrossProduct_eq_dixonCross
    (rank : ℕ) (upper : Fin (rank + 2) → ℝ)
    (lower : Fin (rank + 1) → ℝ) :
    selbergHalfCrossProduct rank upper lower =
      ∏ lowerIndex : Fin (rank + 1),
        ∏ upperIndex : Fin (rank + 2),
          |lower lowerIndex - upper upperIndex| ^ (-1 / 2 : ℝ) := by
  unfold selbergHalfCrossProduct
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro lowerIndex hlower
  apply Finset.prod_congr rfl
  intro upperIndex hupper
  rw [abs_sub_comm]

theorem selbergAndersonJointIntegrand_eq_upper_first
    (rank : ℕ) (alpha beta : ℝ)
    (upper : Fin (rank + 2) → ℝ)
    (lower : Fin (rank + 1) → ℝ)
    (hupper : upper ∈ strictOrderedSelbergDomain (rank + 2))
    (hinterlace : DixonAndersonInterlacing upper lower) :
    selbergAndersonJointIntegrand rank alpha beta upper lower =
      selbergHalfIntegrand (rank + 2) alpha beta upper *
        dixonAndersonHalfIntegrand (rank + 1) upper lower := by
  unfold selbergAndersonJointIntegrand
  rw [dixonAndersonGeneralIntegrand_extended_eq
    rank upper lower alpha beta hupper]
  unfold dixonAndersonHalfIntegrand
  rw [← standardMehtaVandermonde_eq_ordered_of_strictAnti
    lower (roots_strictAnti_of_interlacing hupper.2 hinterlace)]
  rw [selbergHalfCrossProduct_eq_dixonCross]
  ring

theorem expectedDirichletGeneralIntegral_selbergParameters
    (rank : ℕ) (alpha beta : ℝ) :
    expectedDirichletGeneralIntegral (rank + 2)
        (selbergAndersonParameters rank alpha beta) =
      selbergAndersonCoefficient rank alpha beta := by
  unfold expectedDirichletGeneralIntegral
  unfold selbergAndersonCoefficient
  rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
  rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [selbergAndersonParameters_zero,
    selbergAndersonParameters_root,
    selbergAndersonParameters_last_succ]
  simp only [Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.sum_const, nsmul_eq_mul]
  congr 1
  · ring
  · congr 1
    push_cast
    ring

theorem selbergAndersonJointIntegral_upper_section
    (rank : ℕ) {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (lower : Fin (rank + 1) → ℝ)
    (hlower : lower ∈ strictOrderedSelbergDomain (rank + 1)) :
    (∫ upper in dixonAndersonDomain (rank + 2)
        (selbergExtendedAnchors rank lower),
      selbergAndersonJointIntegrand rank alpha beta upper lower) =
      selbergAndersonCoefficient rank alpha beta *
        selbergHalfIntegrand (rank + 1)
          (alpha + 1 / 2) (beta + 1 / 2) lower := by
  have hevaluation := dixonAndersonGeneralEvaluation
    (selbergExtendedAnchors rank lower)
    (selbergAndersonParameters rank alpha beta)
    (selbergExtendedAnchors_strictAnti rank lower hlower)
    (selbergAndersonParameters_pos rank halpha hbeta)
  unfold DixonAndersonGeneralEvaluation at hevaluation
  unfold dixonAndersonGeneralIntegral at hevaluation
  unfold selbergAndersonJointIntegrand
  rw [integral_const_mul]
  rw [hevaluation]
  unfold expectedDixonAndersonGeneralIntegral
  rw [expectedDirichletGeneralIntegral_selbergParameters]
  rw [selbergExtendedAnchorFactor_eq_weights]
  unfold selbergHalfIntegrand
  ring

end FibonacciRibbonKernel
