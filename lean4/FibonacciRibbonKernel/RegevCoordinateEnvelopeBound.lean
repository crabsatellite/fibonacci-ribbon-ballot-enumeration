import FibonacciRibbonKernel.RegevCoordinateEnvelope
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

namespace FibonacciRibbonKernel

open scoped Classical

noncomputable def regevCoordinateAbsSum
    {rank : ℕ} (coordinates : Fin rank → ℝ) : ℝ :=
  ∑ row, |coordinates row|

noncomputable def regevCoordinateBase
    {rank : ℕ} (coordinates : Fin rank → ℝ) : ℝ :=
  1 + regevCoordinateAbsSum coordinates

theorem abs_tracelessExtend_le_absSum
    {rank : ℕ} (coordinates : Fin rank → ℝ)
    (row : Fin (rank + 1)) :
    |tracelessExtend coordinates row| ≤ regevCoordinateAbsSum coordinates := by
  cases row using Fin.lastCases with
  | last =>
      rw [tracelessExtend_last, abs_neg]
      exact Finset.abs_sum_le_sum_abs _ _
  | cast row =>
      rw [tracelessExtend_castSucc]
      unfold regevCoordinateAbsSum
      exact Finset.single_le_sum
        (fun index _ => abs_nonneg (coordinates index))
        (Finset.mem_univ row)

theorem regevCoordinateBase_one_le
    {rank : ℕ} (coordinates : Fin rank → ℝ) :
    1 ≤ regevCoordinateBase coordinates := by
  unfold regevCoordinateBase regevCoordinateAbsSum
  have hsum : 0 ≤ ∑ row, |coordinates row| := by positivity
  linarith

theorem regevCoordinate_row_factor_le
    (rank : ℕ) (coordinates : Fin rank → ℝ)
    (row : Fin (rank + 1)) :
    2 * (1 + |tracelessExtend coordinates row| + (row.rev.val : ℝ)) ≤
      (2 * (rank + 2 : ℕ)) * regevCoordinateBase coordinates := by
  have htrace := abs_tracelessExtend_le_absSum coordinates row
  have hsumNonneg : 0 ≤ regevCoordinateAbsSum coordinates := by
    unfold regevCoordinateAbsSum
    positivity
  have hrevNat : row.rev.val ≤ rank := Nat.le_of_lt_succ row.rev.isLt
  have hrev : (row.rev.val : ℝ) ≤ rank := by exact_mod_cast hrevNat
  unfold regevCoordinateBase
  push_cast
  nlinarith

theorem regevCoordinate_pair_factor_le
    (rank : ℕ) (coordinates : Fin rank → ℝ)
    (row next : Fin (rank + 1)) :
    |tracelessExtend coordinates row| +
        |tracelessExtend coordinates next| +
        (rank : ℝ) * (rank + 1 : ℕ) ≤
      ((rank : ℝ) * (rank + 1 : ℕ) + 2) *
        regevCoordinateBase coordinates := by
  have hrow := abs_tracelessExtend_le_absSum coordinates row
  have hnext := abs_tracelessExtend_le_absSum coordinates next
  have hsumNonneg : 0 ≤ regevCoordinateAbsSum coordinates := by
    unfold regevCoordinateAbsSum
    positivity
  have hrankNonneg : (0 : ℝ) ≤ rank := Nat.cast_nonneg rank
  have hdimensionNonneg : (0 : ℝ) ≤ (rank + 1 : ℕ) :=
    Nat.cast_nonneg (rank + 1)
  have hrankProductNonneg : (0 : ℝ) ≤
      (rank : ℝ) * (rank + 1 : ℕ) :=
    mul_nonneg hrankNonneg hdimensionNonneg
  unfold regevCoordinateBase
  nlinarith

theorem regevCoordinateRowEnvelope_le
    (rank : ℕ) (coordinates : Fin rank → ℝ) :
    regevCoordinateRowEnvelope rank coordinates ≤
      ((2 * (rank + 2 : ℕ) : ℝ) *
        regevCoordinateBase coordinates) ^ (rank + 1) := by
  unfold regevCoordinateRowEnvelope
  calc
    (∏ row : Fin (rank + 1),
      2 * (1 + |tracelessExtend coordinates row| + (row.rev.val : ℝ))) ≤
        ∏ _row : Fin (rank + 1),
          ((2 * (rank + 2 : ℕ) : ℝ) *
            regevCoordinateBase coordinates) := by
      apply Finset.prod_le_prod
      · intro row hrow
        positivity
      · intro row hrow
        exact regevCoordinate_row_factor_le rank coordinates row
    _ = _ := by simp

theorem regevCoordinatePairEnvelope_le
    (rank : ℕ) (coordinates : Fin rank → ℝ) :
    regevCoordinatePairEnvelope rank coordinates ≤
      ((((rank : ℝ) * (rank + 1 : ℕ) + 2) *
        regevCoordinateBase coordinates) ^ (rank + 1)) ^ (rank + 1) := by
  let common := ((rank : ℝ) * (rank + 1 : ℕ) + 2) *
    regevCoordinateBase coordinates
  have hcommonOne : 1 ≤ common := by
    dsimp only [common]
    have hbase := regevCoordinateBase_one_le coordinates
    have hrankNonneg : (0 : ℝ) ≤ rank := Nat.cast_nonneg rank
    have hdimensionNonneg : (0 : ℝ) ≤ (rank + 1 : ℕ) :=
      Nat.cast_nonneg (rank + 1)
    have hrankProductNonneg : (0 : ℝ) ≤
        (rank : ℝ) * (rank + 1 : ℕ) :=
      mul_nonneg hrankNonneg hdimensionNonneg
    have hcoefficient : (1 : ℝ) ≤
        (rank : ℝ) * (rank + 1 : ℕ) + 2 := by linarith
    nlinarith
  unfold regevCoordinatePairEnvelope
  calc
    (∏ row : Fin (rank + 1), ∏ next ∈ Finset.Ioi row,
      (|tracelessExtend coordinates row| +
        |tracelessExtend coordinates next| +
        (rank : ℝ) * (rank + 1 : ℕ))) ≤
      ∏ _row : Fin (rank + 1), common ^ (rank + 1) := by
      apply Finset.prod_le_prod
      · intro row hrow
        apply Finset.prod_nonneg
        intro next hnext
        positivity
      · intro row hrow
        calc
          (∏ next ∈ Finset.Ioi row,
            (|tracelessExtend coordinates row| +
              |tracelessExtend coordinates next| +
              (rank : ℝ) * (rank + 1 : ℕ))) ≤
            ∏ _next ∈ Finset.Ioi row, common := by
              apply Finset.prod_le_prod
              · intro next hnext
                positivity
              · intro next hnext
                exact regevCoordinate_pair_factor_le
                  rank coordinates row next
          _ = common ^ (Finset.Ioi row).card := by simp
          _ ≤ common ^ (rank + 1) := by
            apply pow_le_pow_right₀ hcommonOne
            simpa using Finset.card_le_card (Finset.subset_univ (Finset.Ioi row))
    _ = _ := by
      dsimp only [common]
      simp

noncomputable def regevCoordinateEnvelopeConstant (rank : ℕ) : ℝ :=
  (2 * (rank + 2 : ℕ) : ℝ) ^ (rank + 1) *
    ((rank : ℝ) * (rank + 1 : ℕ) + 2) ^ ((rank + 1) * (rank + 1))

def regevCoordinateEnvelopeDegree (rank : ℕ) : ℕ :=
  (rank + 1) + (rank + 1) * (rank + 1)

theorem regevCoordinateEnvelopeProduct_le
    (rank : ℕ) (coordinates : Fin rank → ℝ) :
    regevCoordinateRowEnvelope rank coordinates *
        regevCoordinatePairEnvelope rank coordinates ≤
      regevCoordinateEnvelopeConstant rank *
        regevCoordinateBase coordinates ^
          regevCoordinateEnvelopeDegree rank := by
  have hrow := regevCoordinateRowEnvelope_le rank coordinates
  have hpair := regevCoordinatePairEnvelope_le rank coordinates
  have hpairNonneg : 0 ≤ regevCoordinatePairEnvelope rank coordinates := by
    unfold regevCoordinatePairEnvelope
    positivity
  have hrowUpperNonneg : 0 ≤
      ((2 * (rank + 2 : ℕ) : ℝ) *
        regevCoordinateBase coordinates) ^ (rank + 1) := by
    have hbaseNonneg : 0 ≤ regevCoordinateBase coordinates :=
      zero_le_one.trans (regevCoordinateBase_one_le coordinates)
    positivity
  refine (mul_le_mul hrow hpair hpairNonneg hrowUpperNonneg).trans_eq ?_
  unfold regevCoordinateEnvelopeConstant regevCoordinateEnvelopeDegree
  rw [pow_mul]
  simp only [mul_pow, pow_add]
  ring

end FibonacciRibbonKernel
