import FibonacciRibbonKernel.BesselGenerated
import Mathlib.LinearAlgebra.Dimension.Finite

namespace FibonacciRibbonKernel

open PowerSeries
open scoped Classical

noncomputable def eulerDerivative (series : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  X * PowerSeries.derivative ℚ series

theorem eulerDerivative_add (left right : ℚ⟦X⟧) :
    eulerDerivative (left + right) =
      eulerDerivative left + eulerDerivative right := by
  simp [eulerDerivative, map_add, mul_add]

theorem eulerDerivative_neg (value : ℚ⟦X⟧) :
    eulerDerivative (-value) = -eulerDerivative value := by
  simp [eulerDerivative]

theorem eulerDerivative_mul (left right : ℚ⟦X⟧) :
    eulerDerivative (left * right) =
      eulerDerivative left * right + left * eulerDerivative right := by
  unfold eulerDerivative
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

theorem eulerDerivative_finsetSum
    {indexType : Type*} [DecidableEq indexType]
    (indices : Finset indexType) (values : indexType → ℚ⟦X⟧) :
    eulerDerivative (∑ index ∈ indices, values index) =
      ∑ index ∈ indices, eulerDerivative (values index) := by
  induction indices using Finset.induction_on with
  | empty => simp [eulerDerivative]
  | @insert index indices hindex ih =>
      simp only [Finset.sum_insert hindex]
      rw [eulerDerivative_add, ih]

theorem eulerDerivative_polynomial (value : Polynomial ℚ) :
    eulerDerivative (value : ℚ⟦X⟧) =
      (Polynomial.X * value.derivative : Polynomial ℚ) := by
  unfold eulerDerivative
  rw [PowerSeries.derivative_coe]
  simpa only [Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X] using
      (Polynomial.coeToPowerSeries.ringHom.map_mul
        Polynomial.X value.derivative).symm

theorem polynomial_coe_add (left right : Polynomial ℚ) :
    ((left + right : Polynomial ℚ) : ℚ⟦X⟧) =
      (left : ℚ⟦X⟧) + (right : ℚ⟦X⟧) := by
  change Polynomial.coeToPowerSeries.ringHom (left + right) = _
  rw [map_add]
  rfl

theorem polynomial_coe_mul (left right : Polynomial ℚ) :
    ((left * right : Polynomial ℚ) : ℚ⟦X⟧) =
      (left : ℚ⟦X⟧) * (right : ℚ⟦X⟧) := by
  change Polynomial.coeToPowerSeries.ringHom (left * right) = _
  rw [map_mul]
  rfl

theorem polynomial_coe_neg (value : Polynomial ℚ) :
    ((-value : Polynomial ℚ) : ℚ⟦X⟧) = -(value : ℚ⟦X⟧) := by
  change Polynomial.coeToPowerSeries.ringHom (-value) = _
  rw [map_neg]
  rfl

theorem polynomial_coe_natCast (value : ℕ) :
    (((value : ℕ) : Polynomial ℚ) : ℚ⟦X⟧) = (value : ℚ⟦X⟧) := by
  change Polynomial.coeToPowerSeries.ringHom (value : Polynomial ℚ) = _
  rw [map_natCast]

structure PolynomialDifferentialRepresentation (value : ℚ⟦X⟧) where
  Index : Type
  indexFintype : Fintype Index
  indexDecidableEq : DecidableEq Index
  basis : Index → ℚ⟦X⟧
  coordinates : Index → Polynomial ℚ
  value_eq : value = ∑ index, (coordinates index : ℚ⟦X⟧) * basis index
  action : Index → Index → Polynomial ℚ
  euler_basis : ∀ index,
    eulerDerivative (basis index) =
      ∑ target, (action index target : ℚ⟦X⟧) * basis target

namespace PolynomialDifferentialRepresentation

attribute [local instance] indexFintype indexDecidableEq

noncomputable def realize {value : ℚ⟦X⟧}
    (representation : PolynomialDifferentialRepresentation value)
    (coordinates : representation.Index → Polynomial ℚ) : ℚ⟦X⟧ :=
  ∑ index, (coordinates index : ℚ⟦X⟧) * representation.basis index

noncomputable def eulerAction {value : ℚ⟦X⟧}
    (representation : PolynomialDifferentialRepresentation value)
    (coordinates : representation.Index → Polynomial ℚ) :
    representation.Index → Polynomial ℚ :=
  fun target =>
    Polynomial.X * (coordinates target).derivative +
      ∑ index, coordinates index * representation.action index target

theorem realize_coordinates {value : ℚ⟦X⟧}
    (representation : PolynomialDifferentialRepresentation value) :
    representation.realize representation.coordinates = value := by
  exact representation.value_eq.symm

theorem eulerDerivative_realize {value : ℚ⟦X⟧}
    (representation : PolynomialDifferentialRepresentation value)
    (coordinates : representation.Index → Polynomial ℚ) :
    eulerDerivative (representation.realize coordinates) =
      representation.realize (representation.eulerAction coordinates) := by
  unfold realize eulerAction
  rw [show (∑ index, (coordinates index : ℚ⟦X⟧) *
      representation.basis index) =
      ∑ index ∈ Finset.univ, (coordinates index : ℚ⟦X⟧) *
        representation.basis index by simp]
  rw [eulerDerivative_finsetSum]
  simp only [eulerDerivative_mul, eulerDerivative_polynomial,
    representation.euler_basis]
  have hsplit :
      (∑ target,
        ((Polynomial.X * (coordinates target).derivative +
          ∑ index, coordinates index * representation.action index target :
            Polynomial ℚ) : ℚ⟦X⟧) * representation.basis target) =
        (∑ target,
          ((Polynomial.X * (coordinates target).derivative :
            Polynomial ℚ) : ℚ⟦X⟧) * representation.basis target) +
        ∑ target,
          ((∑ index, coordinates index * representation.action index target :
            Polynomial ℚ) : ℚ⟦X⟧) * representation.basis target := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro target htarget
    change Polynomial.coeToPowerSeries.ringHom
          (Polynomial.X * (coordinates target).derivative +
            ∑ index, coordinates index * representation.action index target) *
          representation.basis target =
        Polynomial.coeToPowerSeries.ringHom
            (Polynomial.X * (coordinates target).derivative) *
          representation.basis target +
        Polynomial.coeToPowerSeries.ringHom
            (∑ index, coordinates index * representation.action index target) *
          representation.basis target
    rw [map_add, add_mul]
  rw [hsplit]
  rw [Finset.sum_add_distrib]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro target htarget
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  change (∑ index,
      Polynomial.coeToPowerSeries.ringHom (coordinates index) *
        Polynomial.coeToPowerSeries.ringHom
          (representation.action index target)) =
    Polynomial.coeToPowerSeries.ringHom
      (∑ index, coordinates index * representation.action index target)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro index hindex
  rw [map_mul]

noncomputable def polynomial (value : Polynomial ℚ) :
    PolynomialDifferentialRepresentation (value : ℚ⟦X⟧) where
  Index := PUnit
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  basis := fun _ => 1
  coordinates := fun _ => value
  value_eq := by simp
  action := fun _ _ => 0
  euler_basis := by simp [eulerDerivative]

noncomputable def exponential :
    PolynomialDifferentialRepresentation (PowerSeries.exp ℚ) where
  Index := PUnit
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  basis := fun _ => PowerSeries.exp ℚ
  coordinates := fun _ => 1
  value_eq := by simp
  action := fun _ _ => Polynomial.X
  euler_basis := by
    intro index
    simp [eulerDerivative, PowerSeries.derivative_exp]

noncomputable def neg {value : ℚ⟦X⟧}
    (representation : PolynomialDifferentialRepresentation value) :
    PolynomialDifferentialRepresentation (-value) := by
  letI := representation.indexFintype
  letI := representation.indexDecidableEq
  exact
    { Index := representation.Index
      indexFintype := representation.indexFintype
      indexDecidableEq := representation.indexDecidableEq
      basis := representation.basis
      coordinates := fun index => -representation.coordinates index
      value_eq := by
        calc
          -value = -(∑ index,
              (representation.coordinates index : ℚ⟦X⟧) *
                representation.basis index) :=
            congrArg Neg.neg representation.value_eq
          _ = ∑ index,
              ((-representation.coordinates index : Polynomial ℚ) : ℚ⟦X⟧) *
                representation.basis index := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro index hindex
            rw [polynomial_coe_neg]
            ring
      action := representation.action
      euler_basis := representation.euler_basis }

noncomputable def add {left right : ℚ⟦X⟧}
    (leftRepresentation : PolynomialDifferentialRepresentation left)
    (rightRepresentation : PolynomialDifferentialRepresentation right) :
    PolynomialDifferentialRepresentation (left + right) := by
  letI := leftRepresentation.indexFintype
  letI := leftRepresentation.indexDecidableEq
  letI := rightRepresentation.indexFintype
  letI := rightRepresentation.indexDecidableEq
  exact
    { Index := leftRepresentation.Index ⊕ rightRepresentation.Index
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      basis := Sum.elim leftRepresentation.basis rightRepresentation.basis
      coordinates := Sum.elim leftRepresentation.coordinates
        rightRepresentation.coordinates
      value_eq := by
        rw [Fintype.sum_sum_type]
        simpa only [Sum.elim_inl, Sum.elim_inr] using
          congrArg₂ (· + ·) leftRepresentation.value_eq
            rightRepresentation.value_eq
      action := fun source target =>
        match source, target with
        | Sum.inl leftSource, Sum.inl leftTarget =>
            leftRepresentation.action leftSource leftTarget
        | Sum.inr rightSource, Sum.inr rightTarget =>
            rightRepresentation.action rightSource rightTarget
        | _, _ => 0
      euler_basis := by
        intro source
        cases source with
        | inl leftSource =>
            rw [Fintype.sum_sum_type]
            simp only [Sum.elim_inl, Sum.elim_inr]
            rw [leftRepresentation.euler_basis]
            simp
        | inr rightSource =>
            rw [Fintype.sum_sum_type]
            simp only [Sum.elim_inl, Sum.elim_inr]
            rw [rightRepresentation.euler_basis]
            simp }

noncomputable def mul {left right : ℚ⟦X⟧}
    (leftRepresentation : PolynomialDifferentialRepresentation left)
    (rightRepresentation : PolynomialDifferentialRepresentation right) :
    PolynomialDifferentialRepresentation (left * right) := by
  letI := leftRepresentation.indexFintype
  letI := leftRepresentation.indexDecidableEq
  letI := rightRepresentation.indexFintype
  letI := rightRepresentation.indexDecidableEq
  exact
    { Index := leftRepresentation.Index × rightRepresentation.Index
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      basis := fun index =>
        leftRepresentation.basis index.1 * rightRepresentation.basis index.2
      coordinates := fun index =>
        leftRepresentation.coordinates index.1 *
          rightRepresentation.coordinates index.2
      value_eq := by
        calc
          left * right =
              (∑ leftIndex,
                (leftRepresentation.coordinates leftIndex : ℚ⟦X⟧) *
                  leftRepresentation.basis leftIndex) *
              (∑ rightIndex,
                (rightRepresentation.coordinates rightIndex : ℚ⟦X⟧) *
                  rightRepresentation.basis rightIndex) :=
            congrArg₂ (· * ·) leftRepresentation.value_eq
              rightRepresentation.value_eq
          _ = ∑ index : leftRepresentation.Index ×
                rightRepresentation.Index,
              ((leftRepresentation.coordinates index.1 *
                rightRepresentation.coordinates index.2 : Polynomial ℚ) :
                  ℚ⟦X⟧) *
                (leftRepresentation.basis index.1 *
                  rightRepresentation.basis index.2) := by
            rw [Fintype.sum_mul_sum, Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro leftIndex hleftIndex
            apply Finset.sum_congr rfl
            intro rightIndex hrightIndex
            rw [polynomial_coe_mul]
            ring
      action := fun source target =>
        leftRepresentation.action source.1 target.1 *
              (if target.2 = source.2 then 1 else 0) +
          rightRepresentation.action source.2 target.2 *
              (if target.1 = source.1 then 1 else 0)
      euler_basis := by
        intro source
        rw [eulerDerivative_mul, leftRepresentation.euler_basis,
          rightRepresentation.euler_basis]
        rw [Finset.sum_mul, Finset.mul_sum, Fintype.sum_prod_type]
        have hsplit :
            (∑ leftTarget, ∑ rightTarget,
              ((leftRepresentation.action source.1 leftTarget *
                    (if rightTarget = source.2 then 1 else 0) +
                  rightRepresentation.action source.2 rightTarget *
                    (if leftTarget = source.1 then 1 else 0) :
                  Polynomial ℚ) : ℚ⟦X⟧) *
                (leftRepresentation.basis leftTarget *
                  rightRepresentation.basis rightTarget)) =
              (∑ leftTarget, ∑ rightTarget,
                ((leftRepresentation.action source.1 leftTarget *
                    (if rightTarget = source.2 then 1 else 0) :
                      Polynomial ℚ) : ℚ⟦X⟧) *
                  (leftRepresentation.basis leftTarget *
                    rightRepresentation.basis rightTarget)) +
              ∑ leftTarget, ∑ rightTarget,
                ((rightRepresentation.action source.2 rightTarget *
                    (if leftTarget = source.1 then 1 else 0) :
                      Polynomial ℚ) : ℚ⟦X⟧) *
                  (leftRepresentation.basis leftTarget *
                    rightRepresentation.basis rightTarget) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro leftTarget hleftTarget
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro rightTarget hrightTarget
          rw [polynomial_coe_add, add_mul]
        rw [hsplit]
        congr 1
        · apply Finset.sum_congr rfl
          intro leftTarget hleftTarget
          rw [Finset.sum_eq_single source.2]
          · simp
            ring
          · intro rightTarget hrightTarget hne
            simp [hne]
          · intro hnotMem
            exact (hnotMem (Finset.mem_univ source.2)).elim
        · rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro rightTarget hrightTarget
          rw [Finset.sum_eq_single source.1]
          · simp
            ring
          · intro leftTarget hleftTarget hne
            simp [hne]
          · intro hnotMem
            exact (hnotMem (Finset.mem_univ source.1)).elim }

noncomputable def besselPair (selectOne : Bool) :
    PolynomialDifferentialRepresentation
      (if selectOne then literalBesselJ 1 else literalBesselJ 0) := by
  let basis : Bool → ℚ⟦X⟧ := fun index =>
    if index then literalBesselJ 1 else literalBesselJ 0
  exact
    { Index := Bool
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      basis := basis
      coordinates := fun index => if index = selectOne then 1 else 0
      value_eq := by
        cases selectOne <;> simp [basis]
      action := fun source target =>
        match source, target with
        | false, false => 0
        | false, true => 2 * Polynomial.X
        | true, false => 2 * Polynomial.X
        | true, true => -1
      euler_basis := by
        intro source
        cases source with
        | false =>
            simp [basis, eulerDerivative, literalBesselJ_zero,
              literalBesselJ_one, derivative_besselJ0]
            change X * (2 * besselJ1) =
              (((2 : ℕ) : Polynomial ℚ) : ℚ⟦X⟧) * X * besselJ1
            rw [polynomial_coe_natCast]
            ring
        | true =>
            simp [basis, eulerDerivative, literalBesselJ_zero,
              literalBesselJ_one, X_mul_derivative_besselJ1]
            change 2 * X * besselJ0 - besselJ1 =
              -besselJ1 + (((2 : ℕ) : Polynomial ℚ) : ℚ⟦X⟧) *
                X * besselJ0
            rw [polynomial_coe_natCast]
            ring }

theorem nonempty_ofBesselGenerated {value : ℚ⟦X⟧}
    (generated : BesselGenerated value) :
    Nonempty (PolynomialDifferentialRepresentation value) := by
  induction generated with
  | polynomial value => exact ⟨polynomial value⟩
  | besselZero => exact ⟨by simpa using besselPair false⟩
  | besselOne => exact ⟨by simpa using besselPair true⟩
  | exponential => exact ⟨exponential⟩
  | @add left right hleft hright leftIH rightIH =>
      obtain ⟨leftRepresentation⟩ := leftIH
      obtain ⟨rightRepresentation⟩ := rightIH
      exact ⟨add leftRepresentation rightRepresentation⟩
  | @neg value hvalue valueIH =>
      obtain ⟨representation⟩ := valueIH
      exact ⟨neg representation⟩
  | @mul left right hleft hright leftIH rightIH =>
      obtain ⟨leftRepresentation⟩ := leftIH
      obtain ⟨rightRepresentation⟩ := rightIH
      exact ⟨mul leftRepresentation rightRepresentation⟩

noncomputable def iteratedCoordinates {value : ℚ⟦X⟧}
    (representation : PolynomialDifferentialRepresentation value) :
    ℕ → representation.Index → Polynomial ℚ
  | 0 => representation.coordinates
  | order + 1 => representation.eulerAction
      (representation.iteratedCoordinates order)

theorem realize_iteratedCoordinates {value : ℚ⟦X⟧}
    (representation : PolynomialDifferentialRepresentation value)
    (order : ℕ) :
    representation.realize (representation.iteratedCoordinates order) =
      eulerDerivative^[order] value := by
  induction order with
  | zero =>
      simpa [iteratedCoordinates] using representation.realize_coordinates
  | succ order ih =>
      rw [iteratedCoordinates]
      rw [← representation.eulerDerivative_realize]
      rw [ih, Function.iterate_succ_apply']

theorem realize_linearCombination {value : ℚ⟦X⟧}
    (representation : PolynomialDifferentialRepresentation value)
    {combinationIndex : Type*} [Fintype combinationIndex]
    [DecidableEq combinationIndex]
    (scalars : combinationIndex → Polynomial ℚ)
    (vectors : combinationIndex →
      representation.Index → Polynomial ℚ) :
    representation.realize
        (fun target => ∑ index, scalars index * vectors index target) =
      ∑ index, (scalars index : ℚ⟦X⟧) *
        representation.realize (vectors index) := by
  unfold realize
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro target htarget
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  change Polynomial.coeToPowerSeries.ringHom
      (∑ index, scalars index * vectors index target) =
    ∑ index, Polynomial.coeToPowerSeries.ringHom (scalars index) *
      Polynomial.coeToPowerSeries.ringHom (vectors index target)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro index hindex
  rw [map_mul]

end PolynomialDifferentialRepresentation

def EulerDifferentialRelation (value : ℚ⟦X⟧) (order : ℕ)
    (coefficients : Fin (order + 1) → Polynomial ℚ) : Prop :=
  (∃ index, coefficients index ≠ 0) ∧
    ∑ index, (coefficients index : ℚ⟦X⟧) *
      eulerDerivative^[index.val] value = 0

def EulerDFinite (value : ℚ⟦X⟧) : Prop :=
  ∃ order coefficients, EulerDifferentialRelation value order coefficients

namespace PolynomialDifferentialRepresentation

attribute [local instance] indexFintype indexDecidableEq

theorem eulerDFinite {value : ℚ⟦X⟧}
    (representation : PolynomialDifferentialRepresentation value) :
    EulerDFinite value := by
  let dimension := Fintype.card representation.Index
  let vectors : Fin (dimension + 1) →
      (representation.Index → Polynomial ℚ) :=
    fun order => representation.iteratedCoordinates order.val
  have hnotIndependent :
      ¬ LinearIndependent (Polynomial ℚ) vectors := by
    intro hindependent
    have hcard := hindependent.fintype_card_le_finrank
    have hfinrank : Module.finrank (Polynomial ℚ)
        (representation.Index → Polynomial ℚ) = dimension := by
      simp [dimension]
    rw [hfinrank] at hcard
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨coefficients, hrelation, index, hindex⟩ :=
    Fintype.not_linearIndependent_iff.mp hnotIndependent
  refine ⟨dimension, coefficients, ⟨⟨index, hindex⟩, ?_⟩⟩
  simp_rw [← representation.realize_iteratedCoordinates]
  rw [← representation.realize_linearCombination coefficients vectors]
  have hrelationFunction :
      (fun target => ∑ order, coefficients order * vectors order target) = 0 := by
    funext target
    have htarget := congrFun hrelation target
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] using htarget
  rw [hrelationFunction]
  simp [PolynomialDifferentialRepresentation.realize]

end PolynomialDifferentialRepresentation

theorem BesselGenerated.eulerDFinite {value : ℚ⟦X⟧}
    (generated : BesselGenerated value) : EulerDFinite value := by
  obtain ⟨representation⟩ :=
    PolynomialDifferentialRepresentation.nonempty_ofBesselGenerated generated
  exact representation.eulerDFinite

end FibonacciRibbonKernel
