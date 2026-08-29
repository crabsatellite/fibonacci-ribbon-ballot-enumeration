import FibonacciRibbonKernel.GeneralBesselPairFamily

namespace FibonacciRibbonKernel

open PowerSeries
open scoped Classical

noncomputable def besselReductionP : ℕ → Polynomial ℚ
  | 0 => 1
  | 1 => 0
  | order + 2 =>
      Polynomial.X ^ 2 * besselReductionP order -
        Polynomial.C (order + 1 : ℚ) * besselReductionP (order + 1)

noncomputable def besselReductionQ : ℕ → Polynomial ℚ
  | 0 => 0
  | 1 => Polynomial.X
  | order + 2 =>
      Polynomial.X ^ 2 * besselReductionQ order -
        Polynomial.C (order + 1 : ℚ) * besselReductionQ (order + 1)

/-- Cleared recurrence reducing every literal `J_s` to the `J₀,J₁` basis. -/
theorem X_pow_mul_literalBesselJ_reduction (order : ℕ) :
    X ^ order * literalBesselJ order =
      (besselReductionP order : ℚ⟦X⟧) * literalBesselJ 0 +
        (besselReductionQ order : ℚ⟦X⟧) * literalBesselJ 1 := by
  induction order using Nat.twoStepInduction with
  | zero =>
      simp [besselReductionP, besselReductionQ]
  | one =>
      simp [besselReductionP, besselReductionQ]
  | more order hzero hone =>
      have hrec := literalBesselJ_recurrence order
      calc
        X ^ (order + 2) * literalBesselJ (order + 2) =
            X ^ (order + 1) * (X * literalBesselJ (order + 2)) := by
              ring
        _ = X ^ (order + 1) *
            (X * literalBesselJ order -
              (order + 1 : ℚ⟦X⟧) * literalBesselJ (order + 1)) := by
                rw [hrec]
        _ = X ^ 2 * (X ^ order * literalBesselJ order) -
            (order + 1 : ℚ⟦X⟧) *
              (X ^ (order + 1) * literalBesselJ (order + 1)) := by
                ring
        _ = X ^ 2 *
              ((besselReductionP order : ℚ⟦X⟧) * literalBesselJ 0 +
                (besselReductionQ order : ℚ⟦X⟧) * literalBesselJ 1) -
            (order + 1 : ℚ⟦X⟧) *
              ((besselReductionP (order + 1) : ℚ⟦X⟧) * literalBesselJ 0 +
                (besselReductionQ (order + 1) : ℚ⟦X⟧) * literalBesselJ 1) := by
                  rw [hzero, hone]
        _ = (besselReductionP (order + 2) : ℚ⟦X⟧) * literalBesselJ 0 +
            (besselReductionQ (order + 2) : ℚ⟦X⟧) * literalBesselJ 1 := by
              simp only [besselReductionP, besselReductionQ,
                Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_pow,
                Polynomial.coe_X, Polynomial.coe_C]
              norm_num
              ring

noncomputable def pairReductionWeight (gap order : ℕ) : ℚ :=
  if order = 0 ∨ order = gap then 1 else 2

noncomputable def pairReductionP (gap : ℕ) : Polynomial ℚ :=
  ∑ order ∈ Finset.range (gap + 1),
    Polynomial.C (pairReductionWeight gap order) *
      Polynomial.X ^ (gap - order) * besselReductionP order

noncomputable def pairReductionQ (gap : ℕ) : Polynomial ℚ :=
  ∑ order ∈ Finset.range (gap + 1),
    Polynomial.C (pairReductionWeight gap order) *
      Polynomial.X ^ (gap - order) * besselReductionQ order

theorem generalBesselPairQ_eq_weighted_sum
    (gap : ℕ) (hgap : 1 ≤ gap) :
    generalBesselPairQ gap =
      ∑ order ∈ Finset.range (gap + 1),
        pairReductionWeight gap order • literalBesselJ order := by
  rw [generalBesselPairQ, if_neg (by omega : gap ≠ 0)]
  rw [show Finset.range (gap + 1) =
      insert 0 (insert gap (Finset.Ico 1 gap)) by
    ext order
    simp
    omega]
  have hzeroNot : 0 ∉ insert gap (Finset.Ico 1 gap) := by
    simp only [Finset.mem_insert, Finset.mem_Ico, not_or]
    constructor <;> omega
  rw [Finset.sum_insert hzeroNot,
    Finset.sum_insert (by simp : gap ∉ Finset.Ico 1 gap)]
  have hzero : pairReductionWeight gap 0 = 1 := by
    simp [pairReductionWeight]
  have hlast : pairReductionWeight gap gap = 1 := by
    simp [pairReductionWeight]
  have hmiddle :
      (∑ order ∈ Finset.Ico 1 gap,
        pairReductionWeight gap order • literalBesselJ order) =
        2 * ∑ order ∈ Finset.Ico 1 gap, literalBesselJ order := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro order horder
    have hneZero : order ≠ 0 := by
      have := (Finset.mem_Ico.mp horder).1
      omega
    have hneGap : order ≠ gap := by
      have := (Finset.mem_Ico.mp horder).2
      omega
    rw [show pairReductionWeight gap order = 2 by
      simp [pairReductionWeight, hneZero, hneGap]]
    simp only [two_smul]
    ring
  rw [hzero, hlast, one_smul, one_smul, hmiddle]
  ring

theorem polynomial_coe_triple_mul (left middle right : Polynomial ℚ) :
    ((left * middle * right : Polynomial ℚ) : ℚ⟦X⟧) =
      (left : ℚ⟦X⟧) * (middle : ℚ⟦X⟧) * (right : ℚ⟦X⟧) := by
  change Polynomial.coeToPowerSeries.ringHom (left * middle * right) = _
  rw [map_mul, map_mul]
  rfl

theorem pairReductionP_coe (gap : ℕ) :
    (pairReductionP gap : ℚ⟦X⟧) =
      ∑ order ∈ Finset.range (gap + 1),
        ((Polynomial.C (pairReductionWeight gap order) *
          Polynomial.X ^ (gap - order) * besselReductionP order :
          Polynomial ℚ) : ℚ⟦X⟧) := by
  unfold pairReductionP
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
  apply Finset.sum_congr rfl
  intro order horder
  rfl

theorem pairReductionQ_coe (gap : ℕ) :
    (pairReductionQ gap : ℚ⟦X⟧) =
      ∑ order ∈ Finset.range (gap + 1),
        ((Polynomial.C (pairReductionWeight gap order) *
          Polynomial.X ^ (gap - order) * besselReductionQ order :
          Polynomial ℚ) : ℚ⟦X⟧) := by
  unfold pairReductionQ
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
  apply Finset.sum_congr rfl
  intro order horder
  rfl

theorem X_pow_mul_generalBesselPairQ_reduction
    (gap : ℕ) (hgap : 1 ≤ gap) :
    X ^ gap * generalBesselPairQ gap =
      (pairReductionP gap : ℚ⟦X⟧) * literalBesselJ 0 +
        (pairReductionQ gap : ℚ⟦X⟧) * literalBesselJ 1 := by
  rw [generalBesselPairQ_eq_weighted_sum gap hgap, Finset.mul_sum]
  rw [pairReductionP_coe, pairReductionQ_coe,
    Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro order horder
  have horderLe : order ≤ gap := by
    have := Finset.mem_range.mp horder
    omega
  have hreduction := X_pow_mul_literalBesselJ_reduction order
  have hpower : (X : ℚ⟦X⟧) ^ gap = X ^ (gap - order) * X ^ order := by
    rw [← pow_add, Nat.sub_add_cancel horderLe]
  calc
    X ^ gap * (pairReductionWeight gap order • literalBesselJ order) =
        pairReductionWeight gap order •
          (X ^ (gap - order) * (X ^ order * literalBesselJ order)) := by
            rw [PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul,
              hpower]
            ring
    _ = pairReductionWeight gap order •
          (X ^ (gap - order) *
            ((besselReductionP order : ℚ⟦X⟧) * literalBesselJ 0 +
              (besselReductionQ order : ℚ⟦X⟧) * literalBesselJ 1)) := by
                rw [hreduction]
    _ = ((Polynomial.C (pairReductionWeight gap order) *
              Polynomial.X ^ (gap - order) * besselReductionP order : Polynomial ℚ) :
            ℚ⟦X⟧) * literalBesselJ 0 +
          ((Polynomial.C (pairReductionWeight gap order) *
              Polynomial.X ^ (gap - order) * besselReductionQ order : Polynomial ℚ) :
            ℚ⟦X⟧) * literalBesselJ 1 := by
              rw [PowerSeries.smul_eq_C_mul]
              simp only [Polynomial.coe_mul, Polynomial.coe_pow,
                Polynomial.coe_C, Polynomial.coe_X]
              ring

theorem X_pow_mul_universalPairQ_reduction
    (gap : ℕ) (hgap : 1 ≤ gap) :
    X ^ gap * universalPairQ gap =
      (pairReductionP gap : ℚ⟦X⟧) * literalBesselJ 0 +
        (pairReductionQ gap : ℚ⟦X⟧) * literalBesselJ 1 := by
  rw [universalPairQ_eq_generalBesselPairQ gap hgap]
  exact X_pow_mul_generalBesselPairQ_reduction gap hgap

/-- Every arbitrary-rank closed pair coordinate lies in the explicit
`J₀,J₁` module with polynomial coefficients. -/
theorem generalClosedPair_polynomial_bessel_reduction
    {rank gap : ℕ} (left right : Fin (rank + 1))
    (hgap : left.rev.val = right.rev.val + gap) (hgapPos : 1 ≤ gap) :
    generalClosedPair left right =
      (X ^ (2 * right.rev.val) * (pairReductionP gap : ℚ⟦X⟧)) *
          literalBesselJ 0 +
        (X ^ (2 * right.rev.val) * (pairReductionQ gap : ℚ⟦X⟧)) *
          literalBesselJ 1 := by
  rw [generalClosedPair_eq_X_rev_sum_mul_pairQ left right hgap]
  have hexponent : left.rev.val + right.rev.val =
      2 * right.rev.val + gap := by omega
  rw [hexponent, pow_add, mul_assoc,
    X_pow_mul_universalPairQ_reduction gap hgapPos]
  ring

end FibonacciRibbonKernel
