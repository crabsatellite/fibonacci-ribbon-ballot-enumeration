import FibonacciRibbonKernel.RibbonModelProductAsymptotic
import FibonacciRibbonKernel.BesselGenerated

namespace FibonacciRibbonKernel

open PowerSeries
open scoped Classical

/-!
# Homogeneous Bessel representations

Unlike `BesselGenerated`, this carrier retains the total number of Bessel
factors.  That degree is the literal source of the spectral scales
`2d-4j` (and `2d+1-4j` in the exponential branch), so it must not be erased
before the regular-singular analysis.
-/

inductive HomogeneousBesselGenerated : ℕ → ℚ⟦X⟧ → Prop
  | zero (degree : ℕ) : HomogeneousBesselGenerated degree 0
  | term (degree index : ℕ) (hindex : index ≤ degree)
      (coefficient : Polynomial ℚ) :
      HomogeneousBesselGenerated degree
        ((coefficient : ℚ⟦X⟧) * besselMonomial degree index)
  | add {degree : ℕ} {left right : ℚ⟦X⟧} :
      HomogeneousBesselGenerated degree left →
      HomogeneousBesselGenerated degree right →
      HomogeneousBesselGenerated degree (left + right)
  | neg {degree : ℕ} {value : ℚ⟦X⟧} :
      HomogeneousBesselGenerated degree value →
      HomogeneousBesselGenerated degree (-value)
  | mul {leftDegree rightDegree : ℕ} {left right : ℚ⟦X⟧} :
      HomogeneousBesselGenerated leftDegree left →
      HomogeneousBesselGenerated rightDegree right →
      HomogeneousBesselGenerated (leftDegree + rightDegree) (left * right)

theorem HomogeneousBesselGenerated.sub
    {degree : ℕ} {left right : ℚ⟦X⟧}
    (hleft : HomogeneousBesselGenerated degree left)
    (hright : HomogeneousBesselGenerated degree right) :
    HomogeneousBesselGenerated degree (left - right) := by
  rw [sub_eq_add_neg]
  exact hleft.add hright.neg

theorem HomogeneousBesselGenerated.finsetSum
    {degree : ℕ} {indexType : Type*} [DecidableEq indexType]
    (indices : Finset indexType) (values : indexType → ℚ⟦X⟧)
    (hvalues : ∀ index ∈ indices,
      HomogeneousBesselGenerated degree (values index)) :
    HomogeneousBesselGenerated degree (∑ index ∈ indices, values index) := by
  induction indices using Finset.induction_on with
  | empty => exact HomogeneousBesselGenerated.zero degree
  | @insert index indices hindex ih =>
      rw [Finset.sum_insert hindex]
      exact (hvalues index (Finset.mem_insert_self index indices)).add
        (ih fun current hcurrent =>
          hvalues current (Finset.mem_insert_of_mem hcurrent))

theorem HomogeneousBesselGenerated.pow
    {degree : ℕ} {value : ℚ⟦X⟧}
    (hvalue : HomogeneousBesselGenerated degree value) (power : ℕ) :
    HomogeneousBesselGenerated (degree * power) (value ^ power) := by
  induction power with
  | zero =>
      simpa [besselMonomial] using HomogeneousBesselGenerated.term 0 0 (by omega)
        (1 : Polynomial ℚ)
  | succ power ih =>
      rw [pow_succ]
      have hmul := ih.mul hvalue
      simpa [Nat.mul_add, Nat.add_comm] using hmul

theorem homogeneousBessel_polynomial (value : Polynomial ℚ) :
    HomogeneousBesselGenerated 0 (value : ℚ⟦X⟧) := by
  have hterm := HomogeneousBesselGenerated.term 0 0 (by omega) value
  simpa [besselMonomial] using hterm

theorem homogeneousBessel_J0 :
    HomogeneousBesselGenerated 1 (literalBesselJ 0) := by
  have hterm := HomogeneousBesselGenerated.term 1 1 (by omega)
    (1 : Polynomial ℚ)
  simpa [besselMonomial, besselJ0, literalBesselJ_zero] using hterm

theorem homogeneousBessel_J1 :
    HomogeneousBesselGenerated 1 (literalBesselJ 1) := by
  have hterm := HomogeneousBesselGenerated.term 1 0 (by omega)
    (1 : Polynomial ℚ)
  simpa [besselMonomial, besselJ1, literalBesselJ_one] using hterm

theorem homogeneousBessel_polynomial_X_pow_mul
    (degree : ℕ) (value : Polynomial ℚ) :
    HomogeneousBesselGenerated 0
      (PowerSeries.X ^ degree * (value : ℚ⟦X⟧)) := by
  rw [← polynomial_X_pow_mul_coe]
  exact homogeneousBessel_polynomial _

theorem generalClosedPair_homogeneousBessel
    {rank gap : ℕ} (left right : Fin (rank + 1))
    (hgap : left.rev.val = right.rev.val + gap) (hgapPos : 1 ≤ gap) :
    HomogeneousBesselGenerated 1 (generalClosedPair left right) := by
  rw [generalClosedPair_polynomial_bessel_reduction left right hgap hgapPos]
  have hp := homogeneousBessel_polynomial_X_pow_mul
    (2 * right.rev.val) (pairReductionP gap)
  have hq := homogeneousBessel_polynomial_X_pow_mul
    (2 * right.rev.val) (pairReductionQ gap)
  have hpJ := hp.mul homogeneousBessel_J0
  have hqJ := hq.mul homogeneousBessel_J1
  simpa using hpJ.add hqJ

theorem generalClosedPair_homogeneousBessel_all
    {dimension : ℕ} (left right : Fin dimension) :
    HomogeneousBesselGenerated 1 (generalClosedPair left right) := by
  cases dimension with
  | zero => exact Fin.elim0 left
  | succ rank =>
      by_cases heq : left = right
      · subst right
        rw [generalClosedPair_self]
        exact HomogeneousBesselGenerated.zero 1
      by_cases horder : right.rev.val < left.rev.val
      · let gap := left.rev.val - right.rev.val
        exact generalClosedPair_homogeneousBessel (gap := gap) left right
          (by dsimp only [gap]; omega) (by dsimp only [gap]; omega)
      · have hreverse : left.rev.val < right.rev.val := by
          have hne : left.rev.val ≠ right.rev.val := by
            intro h
            apply heq
            exact Fin.rev_injective (Fin.ext h)
          omega
        have hskew : generalClosedPair left right =
            -generalClosedPair right left := by
          ext degree
          rw [map_neg, generalClosedPair_coeff_formula,
            generalClosedPair_coeff_formula]
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro high hhigh
          split_ifs <;> ring
        rw [hskew]
        let gap := right.rev.val - left.rev.val
        exact (generalClosedPair_homogeneousBessel (gap := gap) right left
          (by dsimp only [gap]; omega) (by dsimp only [gap]; omega)).neg

def ExponentialHomogeneousBesselGenerated
    (degree : ℕ) (value : ℚ⟦X⟧) : Prop :=
  ∃ base : ℚ⟦X⟧,
    HomogeneousBesselGenerated degree base ∧
      value = PowerSeries.exp ℚ * base

theorem generalClosedSingle_exponentialHomogeneous
    {dimension : ℕ} (index : Fin dimension) :
    ExponentialHomogeneousBesselGenerated 0 (generalClosedSingle index) := by
  have hpoly : HomogeneousBesselGenerated 0
      (PowerSeries.X ^ index.rev.val : ℚ⟦X⟧) := by
    simpa using homogeneousBessel_polynomial
      (Polynomial.X ^ index.rev.val : Polynomial ℚ)
  refine ⟨PowerSeries.X ^ index.rev.val, hpoly, ?_⟩
  unfold generalClosedSingle
  simp
  ring

theorem HomogeneousBesselGenerated.mul_exponential
    {leftDegree rightDegree : ℕ} {left right : ℚ⟦X⟧}
    (hleft : HomogeneousBesselGenerated leftDegree left)
    (hright : ExponentialHomogeneousBesselGenerated rightDegree right) :
    ExponentialHomogeneousBesselGenerated (leftDegree + rightDegree)
      (left * right) := by
  obtain ⟨base, hbase, rfl⟩ := hright
  refine ⟨left * base, hleft.mul hbase, ?_⟩
  ring

theorem ExponentialHomogeneousBesselGenerated.add
    {degree : ℕ} {left right : ℚ⟦X⟧}
    (hleft : ExponentialHomogeneousBesselGenerated degree left)
    (hright : ExponentialHomogeneousBesselGenerated degree right) :
    ExponentialHomogeneousBesselGenerated degree (left + right) := by
  obtain ⟨leftBase, hleftBase, rfl⟩ := hleft
  obtain ⟨rightBase, hrightBase, rfl⟩ := hright
  refine ⟨leftBase + rightBase, hleftBase.add hrightBase, ?_⟩
  ring

theorem ExponentialHomogeneousBesselGenerated.neg
    {degree : ℕ} {value : ℚ⟦X⟧}
    (hvalue : ExponentialHomogeneousBesselGenerated degree value) :
    ExponentialHomogeneousBesselGenerated degree (-value) := by
  obtain ⟨base, hbase, rfl⟩ := hvalue
  refine ⟨-base, hbase.neg, ?_⟩
  ring

theorem ExponentialHomogeneousBesselGenerated.finsetSum
    {degree : ℕ} {indexType : Type*} [DecidableEq indexType]
    (indices : Finset indexType) (values : indexType → ℚ⟦X⟧)
    (hvalues : ∀ index ∈ indices,
      ExponentialHomogeneousBesselGenerated degree (values index)) :
    ExponentialHomogeneousBesselGenerated degree
      (∑ index ∈ indices, values index) := by
  induction indices using Finset.induction_on with
  | empty =>
      refine ⟨0, HomogeneousBesselGenerated.zero degree, ?_⟩
      simp
  | @insert index indices hindex ih =>
      rw [Finset.sum_insert hindex]
      exact (hvalues index (Finset.mem_insert_self index indices)).add
        (ih fun current hcurrent =>
          hvalues current (Finset.mem_insert_of_mem hcurrent))

theorem ExponentialHomogeneousBesselGenerated.mul_homogeneous
    {leftDegree rightDegree : ℕ} {left right : ℚ⟦X⟧}
    (hleft : ExponentialHomogeneousBesselGenerated leftDegree left)
    (hright : HomogeneousBesselGenerated rightDegree right) :
    ExponentialHomogeneousBesselGenerated (leftDegree + rightDegree)
      (left * right) := by
  obtain ⟨base, hbase, rfl⟩ := hleft
  refine ⟨base * right, hbase.mul hright, ?_⟩
  ring

end FibonacciRibbonKernel
