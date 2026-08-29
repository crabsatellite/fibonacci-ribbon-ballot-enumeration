import FibonacciRibbonKernel.MainEnumeration
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Catalan

namespace FibonacciRibbonKernel

open PowerSeries

/-- `(1 + X²)^{-d}` as a literal formal power series over `ℤ`. -/
noncomputable def evenNegativeBinomial (d : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.subst (X ^ 2)
    (PowerSeries.rescale (-1 : ℤ) (PowerSeries.invOneSubPow ℤ d).val)

theorem evenNegativeBinomial_coeff_succ (d n : ℕ) :
    PowerSeries.coeff n (evenNegativeBinomial (d + 1)) =
      if 2 ∣ n then
        (-1 : ℤ) ^ (n / 2) * (Nat.choose (d + n / 2) d : ℤ)
      else 0 := by
  rw [evenNegativeBinomial, PowerSeries.coeff_subst_X_pow (by omega)]
  split_ifs with heven
  · rw [PowerSeries.coeff_rescale,
      PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
      PowerSeries.coeff_mk]
    simp
  · rfl

theorem evenNegativeBinomial_zero : evenNegativeBinomial 0 = 1 := by
  unfold evenNegativeBinomial
  rw [PowerSeries.invOneSubPow_zero]
  change PowerSeries.subst (X ^ 2)
    (PowerSeries.rescale (-1 : ℤ) (1 : ℤ⟦X⟧)) = 1
  rw [show PowerSeries.rescale (-1 : ℤ) (1 : ℤ⟦X⟧) = 1 by
    ext n
    simp]
  change PowerSeries.subst (X ^ 2) (PowerSeries.C (R := ℤ) 1) = 1
  simpa using PowerSeries.subst_C (a := (X ^ 2 : ℤ⟦X⟧)) (1 : ℤ)

theorem evenNegativeBinomial_add (left right : ℕ) :
    evenNegativeBinomial (left + right) =
      evenNegativeBinomial left * evenNegativeBinomial right := by
  unfold evenNegativeBinomial
  rw [← PowerSeries.subst_mul (PowerSeries.HasSubst.X_pow (by omega))]
  congr 1
  rw [← map_mul]
  congr 1
  rw [← Units.val_mul, ← PowerSeries.invOneSubPow_add]

/-- The unit factor `(1+X²)⁻¹`. -/
noncomputable def substitutionDenominator : ℤ⟦X⟧ :=
  evenNegativeBinomial 1

/-- The inner substitution `X/(1+X²)`. -/
noncomputable def ribbonSubstitution : ℤ⟦X⟧ :=
  X * substitutionDenominator

theorem evenNegativeBinomial_eq_denominator_pow (d : ℕ) :
    evenNegativeBinomial d = substitutionDenominator ^ d := by
  induction d with
  | zero => simp [evenNegativeBinomial_zero]
  | succ d ih =>
      rw [show d + 1 = 1 + d by omega, evenNegativeBinomial_add,
        ih]
      change substitutionDenominator * substitutionDenominator ^ d =
        substitutionDenominator ^ (1 + d)
      rw [Nat.add_comm, pow_succ']

theorem substitutionDenominator_coeff (n : ℕ) :
    PowerSeries.coeff n substitutionDenominator =
      if 2 ∣ n then (-1 : ℤ) ^ (n / 2) else 0 := by
  simpa [substitutionDenominator] using evenNegativeBinomial_coeff_succ 0 n

theorem substitutionDenominator_mul_one_add_X_sq :
    substitutionDenominator * (1 + X ^ 2) = 1 := by
  have hunit := Units.val_inv (PowerSeries.invOneSubPow ℤ 1)
  rw [PowerSeries.invOneSubPow_inv_eq_one_sub_pow] at hunit
  simp only [pow_one] at hunit
  have hscaled := congrArg (PowerSeries.rescale (-1 : ℤ)) hunit
  have hbase :
      PowerSeries.rescale (-1 : ℤ) (PowerSeries.invOneSubPow ℤ 1).val *
        (1 + X) = 1 := by
    simpa [map_mul, map_sub, PowerSeries.rescale_neg_one_X] using hscaled
  let hX2 : PowerSeries.HasSubst (X ^ 2 : ℤ⟦X⟧) :=
    PowerSeries.HasSubst.X_pow (by omega)
  have hsubst := congrArg (PowerSeries.substAlgHom hX2) hbase
  rw [PowerSeries.coe_substAlgHom] at hsubst
  rw [PowerSeries.subst_mul hX2] at hsubst
  have hOne : PowerSeries.subst (X ^ 2 : ℤ⟦X⟧) (1 : ℤ⟦X⟧) =
      (1 : ℤ⟦X⟧) := by
    change PowerSeries.subst (X ^ 2 : ℤ⟦X⟧) (PowerSeries.C (R := ℤ) 1) = 1
    simpa using PowerSeries.subst_C (a := (X ^ 2 : ℤ⟦X⟧)) (1 : ℤ)
  have hOneAddX :
      PowerSeries.subst (X ^ 2 : ℤ⟦X⟧) ((1 : ℤ⟦X⟧) + X) =
        (1 : ℤ⟦X⟧) + X ^ 2 := by
    rw [PowerSeries.subst_add hX2, hOne, PowerSeries.subst_X hX2]
  rw [hOne, hOneAddX] at hsubst
  simpa [substitutionDenominator, evenNegativeBinomial] using hsubst

theorem ribbonSubstitution_constantCoeff :
    PowerSeries.constantCoeff ribbonSubstitution = 0 := by
  simp [ribbonSubstitution]

theorem ribbonSubstitution_hasSubst :
    PowerSeries.HasSubst ribbonSubstitution :=
  PowerSeries.HasSubst.of_constantCoeff_zero' ribbonSubstitution_constantCoeff

theorem denominator_mul_substitution_pow (degree : ℕ) :
    substitutionDenominator * ribbonSubstitution ^ degree =
      X ^ degree * evenNegativeBinomial (degree + 1) := by
  rw [ribbonSubstitution, mul_pow, ← evenNegativeBinomial_eq_denominator_pow]
  rw [evenNegativeBinomial_add]
  unfold substitutionDenominator
  ring

theorem coeff_denominator_mul_substitution_pow
    (degree coefficient : ℕ) :
    PowerSeries.coeff coefficient
        (substitutionDenominator * ribbonSubstitution ^ degree) =
      if degree ≤ coefficient ∧ 2 ∣ coefficient - degree then
        (-1 : ℤ) ^ ((coefficient - degree) / 2) *
          (Nat.choose
            (degree + (coefficient - degree) / 2)
            degree : ℤ)
      else 0 := by
  rw [denominator_mul_substitution_pow,
    PowerSeries.coeff_X_pow_mul']
  by_cases hdegree : degree ≤ coefficient
  · rw [if_pos hdegree, evenNegativeBinomial_coeff_succ]
    by_cases heven : 2 ∣ coefficient - degree
    · simp [hdegree, heven]
    · simp [hdegree, heven]
  · rw [if_neg hdegree]
    simp [hdegree]

theorem coeff_ribbonSubstitution_pow_eq_zero_of_lt
    {degree coefficient : ℕ} (hlt : coefficient < degree) :
    PowerSeries.coeff coefficient (ribbonSubstitution ^ degree) = 0 := by
  rw [ribbonSubstitution, mul_pow, PowerSeries.coeff_X_pow_mul']
  simp [hlt.not_ge]

theorem coeff_subst_ribbonSubstitution_eq_sum_range
    (series : ℤ⟦X⟧) {coefficient bound : ℕ} (hbound : coefficient ≤ bound) :
    PowerSeries.coeff coefficient
        (PowerSeries.subst ribbonSubstitution series) =
      ∑ degree ∈ Finset.range (bound + 1),
        PowerSeries.coeff degree series *
          PowerSeries.coeff coefficient (ribbonSubstitution ^ degree) := by
  rw [PowerSeries.coeff_subst' ribbonSubstitution_hasSubst]
  have hsupport : Function.support (fun degree : ℕ =>
      PowerSeries.coeff degree series •
        PowerSeries.coeff coefficient (ribbonSubstitution ^ degree)) ⊆
      (Finset.range (bound + 1) : Set ℕ) := by
    intro degree hdegree
    simp only [Function.mem_support, smul_eq_mul] at hdegree
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra hnot
    have hlt : coefficient < degree := by omega
    rw [coeff_ribbonSubstitution_pow_eq_zero_of_lt hlt, mul_zero] at hdegree
    exact hdegree rfl
  rw [finsum_eq_sum_of_support_subset _ hsupport]
  rfl

theorem coeff_denominator_mul_subst
    (series : ℤ⟦X⟧) (coefficient : ℕ) :
    PowerSeries.coeff coefficient
        (substitutionDenominator *
          PowerSeries.subst ribbonSubstitution series) =
      ∑ degree ∈ Finset.range (coefficient + 1),
        PowerSeries.coeff degree series *
          PowerSeries.coeff coefficient
            (substitutionDenominator * ribbonSubstitution ^ degree) := by
  rw [PowerSeries.coeff_mul]
  have hrewrite : ∀ pair ∈ Finset.antidiagonal coefficient,
      PowerSeries.coeff pair.2
          (PowerSeries.subst ribbonSubstitution series) =
        ∑ degree ∈ Finset.range (coefficient + 1),
          PowerSeries.coeff degree series *
            PowerSeries.coeff pair.2 (ribbonSubstitution ^ degree) := by
    intro pair hpair
    apply coeff_subst_ribbonSubstitution_eq_sum_range
    have hsum := Finset.mem_antidiagonal.mp hpair
    omega
  rw [Finset.sum_congr rfl (fun pair hpair => by
    rw [hrewrite pair hpair])]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro degree hdegree
  rw [PowerSeries.coeff_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair hpair
  ring

/-- Ordinary series of unrestricted counts. -/
noncomputable def unrestrictedGeneratingSeries (rank : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun columns => (unrestrictedCount rank columns : ℤ)

/-- Ordinary series of admissible ribbon counts. -/
noncomputable def ribbonGeneratingSeries (rank : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun columns => (ribbonCount rank columns : ℤ)

@[simp] theorem unrestrictedGeneratingSeries_coeff (rank columns : ℕ) :
    PowerSeries.coeff columns (unrestrictedGeneratingSeries rank) =
      (unrestrictedCount rank columns : ℤ) := by
  simp [unrestrictedGeneratingSeries]

@[simp] theorem ribbonGeneratingSeries_coeff (rank columns : ℕ) :
    PowerSeries.coeff columns (ribbonGeneratingSeries rank) =
      (ribbonCount rank columns : ℤ) := by
  simp [ribbonGeneratingSeries]

theorem coeff_exact_substitution_rhs (rank columns : ℕ) :
    PowerSeries.coeff columns
        (substitutionDenominator *
          PowerSeries.subst ribbonSubstitution
            (unrestrictedGeneratingSeries rank)) =
      ∑ edges ∈ Finset.range (columns / 2 + 1),
        (-1 : ℤ) ^ edges *
          (Nat.choose (columns - edges) edges : ℤ) *
          (unrestrictedCount rank (columns - 2 * edges) : ℤ) := by
  rw [coeff_denominator_mul_subst]
  simp only [unrestrictedGeneratingSeries_coeff]
  calc
    (∑ degree ∈ Finset.range (columns + 1),
        (unrestrictedCount rank degree : ℤ) *
          PowerSeries.coeff columns
            (substitutionDenominator * ribbonSubstitution ^ degree)) =
      ∑ degree ∈ Finset.range (columns + 1),
        if 2 ∣ columns - degree then
          (unrestrictedCount rank degree : ℤ) *
            ((-1 : ℤ) ^ ((columns - degree) / 2) *
              (Nat.choose (degree + (columns - degree) / 2) degree : ℤ))
        else 0 := by
          apply Finset.sum_congr rfl
          intro degree hdegree
          have hle : degree ≤ columns := by
            simp only [Finset.mem_range] at hdegree
            omega
          rw [coeff_denominator_mul_substitution_pow]
          by_cases heven : 2 ∣ columns - degree <;> simp [hle, heven]
    _ = ∑ degree ∈
        (Finset.range (columns + 1)).filter
          (fun degree => 2 ∣ columns - degree),
        (unrestrictedCount rank degree : ℤ) *
          ((-1 : ℤ) ^ ((columns - degree) / 2) *
            (Nat.choose (degree + (columns - degree) / 2) degree : ℤ)) := by
          rw [Finset.sum_filter]
    _ = ∑ edges ∈ Finset.range (columns / 2 + 1),
        (-1 : ℤ) ^ edges *
          (Nat.choose (columns - edges) edges : ℤ) *
          (unrestrictedCount rank (columns - 2 * edges) : ℤ) := by
          apply Finset.sum_bij
            (fun degree _ => (columns - degree) / 2)
          · intro degree hdegree
            simp only [Finset.mem_filter, Finset.mem_range] at hdegree
            simp only [Finset.mem_range]
            omega
          · intro left hleft right hright heq
            simp only [Finset.mem_filter, Finset.mem_range] at hleft hright
            obtain ⟨leftHalf, hleftHalf⟩ := hleft.2
            obtain ⟨rightHalf, hrightHalf⟩ := hright.2
            omega
          · intro edges hedges
            simp only [Finset.mem_range] at hedges
            let degree := columns - 2 * edges
            have hdegree : degree ∈
                (Finset.range (columns + 1)).filter
                  (fun degree => 2 ∣ columns - degree) := by
              simp only [Finset.mem_filter, Finset.mem_range, degree]
              constructor
              · omega
              · use edges
                omega
            refine ⟨degree, hdegree, ?_⟩
            dsimp [degree]
            omega
          · intro degree hdegree
            simp only [Finset.mem_filter, Finset.mem_range] at hdegree
            obtain ⟨half, hhalf⟩ := hdegree.2
            rw [show columns - 2 * ((columns - degree) / 2) = degree by omega]
            rw [show columns - (columns - degree) / 2 =
              degree + (columns - degree) / 2 by omega]
            rw [Nat.choose_symm_add]
            ring

/-- Complete formal-series endpoint for `thm:substitution` / `eq:substitution`. -/
theorem exact_generating_substitution
    {rank : ℕ} (hrank : 1 ≤ rank) :
    ribbonGeneratingSeries rank =
      substitutionDenominator *
        PowerSeries.subst ribbonSubstitution
          (unrestrictedGeneratingSeries rank) := by
  ext columns
  rw [ribbonGeneratingSeries_coeff,
    coeff_exact_substitution_rhs]
  exact ribbonCount_eq_alternating_unrestricted hrank columns

/-- Catalan series transported coefficientwise from `ℕ` to `ℤ`. -/
noncomputable def integerCatalanSeries : ℤ⟦X⟧ :=
  PowerSeries.map (Nat.castRingHom ℤ) PowerSeries.catalanSeries

theorem integerCatalanSeries_equation :
    integerCatalanSeries ^ 2 * X + 1 = integerCatalanSeries := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℤ))
    PowerSeries.catalanSeries_sq_mul_X_add_one
  simpa [integerCatalanSeries, map_add, map_mul, map_pow] using h

/-- `C(X²)`, the even Catalan series. -/
noncomputable def evenCatalanSeries : ℤ⟦X⟧ :=
  PowerSeries.subst (X ^ 2) integerCatalanSeries

theorem integerCatalanSeries_coeff (n : ℕ) :
    PowerSeries.coeff n integerCatalanSeries =
      (catalan n : ℤ) := by
  simp [integerCatalanSeries, PowerSeries.coeff_map]

theorem evenCatalanSeries_coeff_two_mul (n : ℕ) :
    PowerSeries.coeff (2 * n) evenCatalanSeries =
      (catalan n : ℤ) := by
  rw [evenCatalanSeries, PowerSeries.coeff_subst_X_pow (by omega)]
  simp [integerCatalanSeries_coeff]

theorem evenCatalanSeries_coeff_two_mul_add_one (n : ℕ) :
    PowerSeries.coeff (2 * n + 1) evenCatalanSeries = 0 := by
  rw [evenCatalanSeries, PowerSeries.coeff_subst_X_pow (by omega)]
  simp

theorem evenCatalanSeries_equation :
    evenCatalanSeries ^ 2 * X ^ 2 + 1 = evenCatalanSeries := by
  let hX2 : PowerSeries.HasSubst (X ^ 2 : ℤ⟦X⟧) :=
    PowerSeries.HasSubst.X_pow (by omega)
  have h := congrArg (PowerSeries.substAlgHom hX2)
    integerCatalanSeries_equation
  rw [PowerSeries.coe_substAlgHom] at h
  have hOne : PowerSeries.subst (X ^ 2 : ℤ⟦X⟧) (1 : ℤ⟦X⟧) = 1 := by
    change PowerSeries.subst (X ^ 2 : ℤ⟦X⟧)
      (PowerSeries.C (R := ℤ) 1) = 1
    simpa using PowerSeries.subst_C (a := (X ^ 2 : ℤ⟦X⟧)) (1 : ℤ)
  rw [PowerSeries.subst_add hX2, PowerSeries.subst_mul hX2,
    PowerSeries.subst_pow hX2, PowerSeries.subst_X hX2, hOne] at h
  exact h

/--
The manuscript inverse series
`ψ(w) = w + w³ + 2w⁵ + ⋯ = w C(w²)`.
-/
noncomputable def inverseRibbonSubstitution : ℤ⟦X⟧ :=
  X * evenCatalanSeries

theorem inverseRibbonSubstitution_coeff_two_mul_add_one (n : ℕ) :
    PowerSeries.coeff (2 * n + 1) inverseRibbonSubstitution =
      (catalan n : ℤ) := by
  rw [inverseRibbonSubstitution]
  have h := PowerSeries.coeff_X_pow_mul evenCatalanSeries 1 (2 * n)
  simpa only [pow_one, Nat.add_comm 1 (2 * n)] using
    h.trans (evenCatalanSeries_coeff_two_mul n)

theorem inverseRibbonSubstitution_coeff_two_mul (n : ℕ) :
    PowerSeries.coeff (2 * n) inverseRibbonSubstitution = 0 := by
  cases n with
  | zero => simp [inverseRibbonSubstitution]
  | succ n =>
      rw [inverseRibbonSubstitution]
      rw [show (X : ℤ⟦X⟧) = X ^ 1 by simp]
      rw [PowerSeries.coeff_X_pow_mul']
      simp only [if_pos (by omega : 1 ≤ 2 * (n + 1))]
      rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
      exact evenCatalanSeries_coeff_two_mul_add_one n

theorem inverseRibbonSubstitution_equation :
    inverseRibbonSubstitution =
      X * (1 + inverseRibbonSubstitution ^ 2) := by
  unfold inverseRibbonSubstitution
  calc
    X * evenCatalanSeries =
        X * (evenCatalanSeries ^ 2 * X ^ 2 + 1) := by
          rw [evenCatalanSeries_equation]
    _ = X * (1 + (X * evenCatalanSeries) ^ 2) := by ring

theorem inverseRibbonSubstitution_constantCoeff :
    PowerSeries.constantCoeff inverseRibbonSubstitution = 0 := by
  simp [inverseRibbonSubstitution]

theorem inverseRibbonSubstitution_hasSubst :
    PowerSeries.HasSubst inverseRibbonSubstitution :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    inverseRibbonSubstitution_constantCoeff

theorem substitutionDenominator_subst_inverse_mul :
    PowerSeries.subst inverseRibbonSubstitution substitutionDenominator *
      (1 + inverseRibbonSubstitution ^ 2) = 1 := by
  let hpsi := inverseRibbonSubstitution_hasSubst
  have h := congrArg (PowerSeries.substAlgHom hpsi)
    substitutionDenominator_mul_one_add_X_sq
  rw [PowerSeries.coe_substAlgHom] at h
  rw [PowerSeries.subst_mul hpsi] at h
  have hOne : PowerSeries.subst inverseRibbonSubstitution (1 : ℤ⟦X⟧) = 1 := by
    change PowerSeries.subst inverseRibbonSubstitution
      (PowerSeries.C (R := ℤ) 1) = 1
    simpa using PowerSeries.subst_C
      (a := inverseRibbonSubstitution) (1 : ℤ)
  have hOneAdd :
      PowerSeries.subst inverseRibbonSubstitution (1 + X ^ 2 : ℤ⟦X⟧) =
        1 + inverseRibbonSubstitution ^ 2 := by
    rw [PowerSeries.subst_add hpsi, hOne,
      PowerSeries.subst_pow hpsi, PowerSeries.subst_X hpsi]
  rw [hOne, hOneAdd] at h
  exact h

/-- The displayed inner substitution sends the explicit `ψ` back to `X`. -/
theorem ribbonSubstitution_subst_inverse :
    PowerSeries.subst inverseRibbonSubstitution ribbonSubstitution = X := by
  let hpsi := inverseRibbonSubstitution_hasSubst
  rw [ribbonSubstitution, PowerSeries.subst_mul hpsi,
    PowerSeries.subst_X hpsi]
  calc
    inverseRibbonSubstitution *
        PowerSeries.subst inverseRibbonSubstitution substitutionDenominator =
      X * (1 + inverseRibbonSubstitution ^ 2) *
        PowerSeries.subst inverseRibbonSubstitution substitutionDenominator := by
          conv_lhs => lhs; rw [inverseRibbonSubstitution_equation]
    _ = X := by
      rw [mul_assoc]
      rw [mul_comm (1 + inverseRibbonSubstitution ^ 2)]
      rw [substitutionDenominator_subst_inverse_mul]
      simp

theorem ribbonSubstitution_coeff_one :
    PowerSeries.coeff 1 ribbonSubstitution = 1 := by
  have h := PowerSeries.coeff_X_pow_mul substitutionDenominator 1 0
  calc
    PowerSeries.coeff 1 ribbonSubstitution =
        PowerSeries.coeff 0 substitutionDenominator := by
          simpa only [ribbonSubstitution, Nat.zero_add, pow_one] using h
    _ = 1 := by simp [substitutionDenominator_coeff]

theorem ribbonSubstitution_coeff_one_isUnit :
    IsUnit (PowerSeries.coeff 1 ribbonSubstitution) := by
  rw [ribbonSubstitution_coeff_one]
  exact isUnit_one

/-- The explicit Catalan series is the canonical compositional inverse. -/
theorem inverseRibbonSubstitution_eq_substInv :
    inverseRibbonSubstitution =
      ribbonSubstitution.substInvOfIsUnit
        ribbonSubstitution_coeff_one_isUnit := by
  let canonical := ribbonSubstitution.substInvOfIsUnit
    ribbonSubstitution_coeff_one_isUnit
  have hcanonicalLeft : PowerSeries.subst ribbonSubstitution canonical = X :=
    PowerSeries.subst_substInvOfIsUnit_left ribbonSubstitution
      ribbonSubstitution_constantCoeff ribbonSubstitution_coeff_one_isUnit
  calc
    inverseRibbonSubstitution =
        PowerSeries.subst inverseRibbonSubstitution X := by
          exact (PowerSeries.subst_X (R := ℤ) (S := ℤ)
            inverseRibbonSubstitution_hasSubst).symm
    _ = PowerSeries.subst inverseRibbonSubstitution
          (PowerSeries.subst ribbonSubstitution canonical) := by
            rw [hcanonicalLeft]
    _ = PowerSeries.subst
          (PowerSeries.subst inverseRibbonSubstitution ribbonSubstitution)
          canonical :=
            PowerSeries.subst_comp_subst_apply
              ribbonSubstitution_hasSubst inverseRibbonSubstitution_hasSubst canonical
    _ = canonical := by
          rw [ribbonSubstitution_subst_inverse, PowerSeries.X_subst]

/-- The explicit `ψ` also sends the inner substitution to `X`. -/
theorem inverseRibbonSubstitution_subst_ribbon :
    PowerSeries.subst ribbonSubstitution inverseRibbonSubstitution = X := by
  rw [inverseRibbonSubstitution_eq_substInv]
  exact PowerSeries.subst_substInvOfIsUnit_left ribbonSubstitution
    ribbonSubstitution_constantCoeff ribbonSubstitution_coeff_one_isUnit

/-- Complete endpoint for `eq:inverse-substitution`. -/
theorem inverse_generating_substitution
    {rank : ℕ} (hrank : 1 ≤ rank) :
    unrestrictedGeneratingSeries rank =
      (1 + inverseRibbonSubstitution ^ 2) *
        PowerSeries.subst inverseRibbonSubstitution
          (ribbonGeneratingSeries rank) := by
  have hforward := exact_generating_substitution hrank
  have hsubst := congrArg
    (PowerSeries.substAlgHom inverseRibbonSubstitution_hasSubst) hforward
  rw [PowerSeries.coe_substAlgHom] at hsubst
  rw [PowerSeries.subst_mul inverseRibbonSubstitution_hasSubst] at hsubst
  rw [PowerSeries.subst_comp_subst_apply ribbonSubstitution_hasSubst
    inverseRibbonSubstitution_hasSubst] at hsubst
  rw [ribbonSubstitution_subst_inverse, PowerSeries.X_subst] at hsubst
  calc
    unrestrictedGeneratingSeries rank =
        1 * unrestrictedGeneratingSeries rank := by simp
    _ = (1 + inverseRibbonSubstitution ^ 2) *
          PowerSeries.subst inverseRibbonSubstitution substitutionDenominator *
          unrestrictedGeneratingSeries rank := by
            rw [mul_comm (1 + inverseRibbonSubstitution ^ 2),
              substitutionDenominator_subst_inverse_mul]
    _ = (1 + inverseRibbonSubstitution ^ 2) *
          PowerSeries.subst inverseRibbonSubstitution
            (ribbonGeneratingSeries rank) := by
            rw [hsubst, mul_assoc]

end FibonacciRibbonKernel
