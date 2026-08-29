import FibonacciRibbonKernel.UniversalPairParity

namespace FibonacciRibbonKernel

open PowerSeries

/-- The uniform Bergeron--Gascon pair family
`Q_s=J₀+2J₁+⋯+2J_{s-1}+J_s` for `s>0`. -/
noncomputable def generalBesselPairQ (gap : ℕ) : ℚ⟦X⟧ :=
  if gap = 0 then 0 else
    literalBesselJ 0 + literalBesselJ gap +
      2 * ∑ order ∈ Finset.Ico 1 gap, literalBesselJ order

theorem generalBesselPairQ_one :
    generalBesselPairQ 1 = literalBesselJ 0 + literalBesselJ 1 := by
  simp [generalBesselPairQ]

theorem generalBesselPairQ_succ
    (gap : ℕ) (hgap : 1 ≤ gap) :
    generalBesselPairQ (gap + 1) =
      generalBesselPairQ gap + literalBesselJ gap +
        literalBesselJ (gap + 1) := by
  rw [generalBesselPairQ, generalBesselPairQ,
    if_neg (by omega : gap + 1 ≠ 0), if_neg (by omega : gap ≠ 0)]
  rw [Finset.sum_Ico_succ_top hgap]
  ring

theorem universalPairQ_one_eq_generalBesselPairQ :
    universalPairQ 1 = generalBesselPairQ 1 := by
  rw [universalPairQ_one_eq_bessel, generalBesselPairQ_one]
  rfl

/-- Complete all-gap Bergeron--Gascon coordinate identity. -/
theorem universalPairQ_eq_generalBesselPairQ
    (gap : ℕ) (hgap : 1 ≤ gap) :
    universalPairQ gap = generalBesselPairQ gap := by
  induction gap using Nat.strong_induction_on with
  | h gap ih =>
      by_cases hone : gap = 1
      · subst gap
        exact universalPairQ_one_eq_generalBesselPairQ
      have hgapTwo : 2 ≤ gap := by omega
      let previous := gap - 1
      have hprevious : 1 ≤ previous := by
        dsimp only [previous]
        omega
      have hpreviousLt : previous < gap := by
        dsimp only [previous]
        omega
      have hinduction := ih previous hpreviousLt hprevious
      have hsuccessor : previous + 1 = gap := by
        dsimp only [previous]
        omega
      have huniversal :
          universalPairQ gap =
            universalPairQ previous + literalBesselJ previous +
              literalBesselJ gap := by
        obtain ⟨halfGap, heven | hodd⟩ := Nat.even_or_odd' previous
        · have hhalf : 1 ≤ halfGap := by omega
          have hrec := universalPairQ_even_to_odd_recurrence halfGap hhalf
          rw [heven] at hsuccessor hinduction ⊢
          simpa [hsuccessor] using hrec
        · have hrec := universalPairQ_odd_to_even_recurrence halfGap
          rw [hodd] at hsuccessor hinduction ⊢
          simpa [hsuccessor] using hrec
      have hbessel := generalBesselPairQ_succ previous hprevious
      rw [hsuccessor] at hbessel
      calc
        universalPairQ gap =
            universalPairQ previous + literalBesselJ previous +
              literalBesselJ gap := huniversal
        _ = generalBesselPairQ previous + literalBesselJ previous +
              literalBesselJ gap := by rw [hinduction]
        _ = generalBesselPairQ gap := hbessel.symm

end FibonacciRibbonKernel
