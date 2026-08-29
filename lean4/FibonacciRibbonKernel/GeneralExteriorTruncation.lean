import FibonacciRibbonKernel.GeneralClosedAssembly
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

namespace FibonacciRibbonKernel

open ExteriorAlgebra PowerSeries
open scoped Classical

def ScalarTruncationEquivalent
    (cutoff : ℕ) (left right : ℚ⟦X⟧) : Prop :=
  PowerSeries.trunc cutoff left = PowerSeries.trunc cutoff right

theorem scalarTruncationEquivalent_refl (cutoff : ℕ) (series : ℚ⟦X⟧) :
    ScalarTruncationEquivalent cutoff series series := rfl

theorem scalarTruncationEquivalent_add
    {cutoff : ℕ} {a b c d : ℚ⟦X⟧}
    (hab : ScalarTruncationEquivalent cutoff a b)
    (hcd : ScalarTruncationEquivalent cutoff c d) :
    ScalarTruncationEquivalent cutoff (a + c) (b + d) := by
  unfold ScalarTruncationEquivalent at *
  simpa using congrArg₂ (fun left right => left + right) hab hcd

theorem scalarTruncationEquivalent_neg
    {cutoff : ℕ} {a b : ℚ⟦X⟧}
    (hab : ScalarTruncationEquivalent cutoff a b) :
    ScalarTruncationEquivalent cutoff (-a) (-b) := by
  unfold ScalarTruncationEquivalent at *
  simpa using congrArg Neg.neg hab

theorem scalarTruncationEquivalent_mul
    {cutoff : ℕ} {a b c d : ℚ⟦X⟧}
    (hab : ScalarTruncationEquivalent cutoff a b)
    (hcd : ScalarTruncationEquivalent cutoff c d) :
    ScalarTruncationEquivalent cutoff (a * c) (b * d) := by
  unfold ScalarTruncationEquivalent at *
  calc
    PowerSeries.trunc cutoff (a * c) =
        PowerSeries.trunc cutoff
          ((PowerSeries.trunc cutoff a : ℚ⟦X⟧) *
            (PowerSeries.trunc cutoff c : ℚ⟦X⟧)) :=
      (PowerSeries.trunc_trunc_mul_trunc a c).symm
    _ = PowerSeries.trunc cutoff
          ((PowerSeries.trunc cutoff b : ℚ⟦X⟧) *
            (PowerSeries.trunc cutoff d : ℚ⟦X⟧)) := by rw [hab, hcd]
    _ = PowerSeries.trunc cutoff (b * d) :=
      PowerSeries.trunc_trunc_mul_trunc b d

theorem scalarTruncationEquivalent_finset_sum
    {cutoff : ℕ} {indexType : Type*} [DecidableEq indexType]
    (indices : Finset indexType) (left right : indexType → ℚ⟦X⟧)
    (h : ∀ index ∈ indices,
      ScalarTruncationEquivalent cutoff (left index) (right index)) :
    ScalarTruncationEquivalent cutoff
      (∑ index ∈ indices, left index) (∑ index ∈ indices, right index) := by
  induction indices using Finset.induction_on with
  | empty => exact scalarTruncationEquivalent_refl cutoff 0
  | @insert index indices hindex ih =>
      rw [Finset.sum_insert hindex, Finset.sum_insert hindex]
      exact scalarTruncationEquivalent_add
        (h index (Finset.mem_insert_self index indices))
        (ih fun current hcurrent => h current (Finset.mem_insert_of_mem hcurrent))

theorem scalarTruncationEquivalent_of_coeff_eq
    {cutoff : ℕ} {left right : ℚ⟦X⟧}
    (h : ∀ degree, degree < cutoff →
      PowerSeries.coeff degree left = PowerSeries.coeff degree right) :
    ScalarTruncationEquivalent cutoff left right := by
  unfold ScalarTruncationEquivalent
  apply Polynomial.ext
  intro degree
  rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
  by_cases hdegree : degree < cutoff
  · rw [if_pos hdegree, if_pos hdegree, h degree hdegree]
  · rw [if_neg hdegree, if_neg hdegree]

noncomputable def generalExteriorBasis (dimension : ℕ) :=
  (Pi.basisFun ℚ⟦X⟧ (Fin dimension)).ExteriorAlgebra

def ExteriorTruncationEquivalent
    (dimension cutoff : ℕ)
    (left right : ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension)) : Prop :=
  ∀ subset : Finset (Fin dimension),
    ScalarTruncationEquivalent cutoff
      ((generalExteriorBasis dimension).repr left subset)
      ((generalExteriorBasis dimension).repr right subset)

theorem exteriorTruncationEquivalent_refl
    (dimension cutoff : ℕ)
    (element : ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension)) :
    ExteriorTruncationEquivalent dimension cutoff element element := by
  intro subset
  rfl

theorem exteriorTruncationEquivalent_add
    {dimension cutoff : ℕ} {a b c d :
      ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension)}
    (hab : ExteriorTruncationEquivalent dimension cutoff a b)
    (hcd : ExteriorTruncationEquivalent dimension cutoff c d) :
    ExteriorTruncationEquivalent dimension cutoff (a + c) (b + d) := by
  intro subset
  simp only [map_add]
  exact scalarTruncationEquivalent_add (hab subset) (hcd subset)

theorem exteriorTruncationEquivalent_finset_sum
    {dimension cutoff : ℕ} {indexType : Type*} [DecidableEq indexType]
    (indices : Finset indexType)
    (left right : indexType →
      ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension))
    (h : ∀ index ∈ indices,
      ExteriorTruncationEquivalent dimension cutoff (left index) (right index)) :
    ExteriorTruncationEquivalent dimension cutoff
      (∑ index ∈ indices, left index) (∑ index ∈ indices, right index) := by
  intro subset
  simp only [map_sum, Finset.sum_apply']
  exact scalarTruncationEquivalent_finset_sum indices
    (fun index => (generalExteriorBasis dimension).repr (left index) subset)
    (fun index => (generalExteriorBasis dimension).repr (right index) subset)
    (fun index hindex => h index hindex subset)

theorem exteriorTruncationEquivalent_smul
    {dimension cutoff : ℕ} {leftScalar rightScalar : ℚ⟦X⟧}
    {left right : ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension)}
    (hscalar : ScalarTruncationEquivalent cutoff leftScalar rightScalar)
    (helement : ExteriorTruncationEquivalent dimension cutoff left right) :
    ExteriorTruncationEquivalent dimension cutoff
      (leftScalar • left) (rightScalar • right) := by
  intro subset
  simp only [map_smul]
  exact scalarTruncationEquivalent_mul hscalar (helement subset)

theorem exteriorBasis_mul_repr
    (dimension : ℕ) (left right target : Finset (Fin dimension)) :
    ScalarTruncationEquivalent 0
      ((generalExteriorBasis dimension).repr
        (generalExteriorBasis dimension left * generalExteriorBasis dimension right) target)
      ((generalExteriorBasis dimension).repr
        (generalExteriorBasis dimension left * generalExteriorBasis dimension right) target) := rfl

theorem exteriorTruncationEquivalent_mul
    {dimension cutoff : ℕ} {a b c d :
      ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension)}
    (hab : ExteriorTruncationEquivalent dimension cutoff a b)
    (hcd : ExteriorTruncationEquivalent dimension cutoff c d) :
    ExteriorTruncationEquivalent dimension cutoff (a * c) (b * d) := by
  intro target
  let basis := generalExteriorBasis dimension
  have ha := basis.sum_repr a
  have hb := basis.sum_repr b
  have hc := basis.sum_repr c
  have hd := basis.sum_repr d
  rw [← ha, ← hb, ← hc, ← hd]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, map_sum, map_smul, Finset.sum_apply',
    Finsupp.smul_apply, smul_eq_mul]
  apply scalarTruncationEquivalent_finset_sum Finset.univ
  intro right hright
  apply scalarTruncationEquivalent_finset_sum Finset.univ
  intro left hleft
  exact scalarTruncationEquivalent_mul (hcd right)
    (scalarTruncationEquivalent_mul (hab left)
      (scalarTruncationEquivalent_refl cutoff
        (basis.repr (basis left * basis right) target)))

theorem exteriorTruncationEquivalent_pow
    {dimension cutoff : ℕ}
    {left right : ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension)}
    (h : ExteriorTruncationEquivalent dimension cutoff left right)
    (degree : ℕ) :
    ExteriorTruncationEquivalent dimension cutoff (left ^ degree) (right ^ degree) := by
  induction degree with
  | zero => simpa using exteriorTruncationEquivalent_refl dimension cutoff 1
  | succ degree ih =>
      rw [pow_succ, pow_succ]
      exact exteriorTruncationEquivalent_mul ih h

theorem exteriorTruncationEquivalent_topDeterminant
    {dimension cutoff : ℕ}
    {left right : ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension)}
    (h : ExteriorTruncationEquivalent dimension cutoff left right) :
    ScalarTruncationEquivalent cutoff
      (generalTopDeterminant dimension left)
      (generalTopDeterminant dimension right) := by
  let basis := generalExteriorBasis dimension
  have hleft := basis.sum_repr left
  have hright := basis.sum_repr right
  rw [← hleft, ← hright]
  simp only [map_sum, map_smul]
  apply scalarTruncationEquivalent_finset_sum Finset.univ
  intro subset hsubset
  exact scalarTruncationEquivalent_mul (h subset)
    (scalarTruncationEquivalent_refl cutoff
      (generalTopDeterminant dimension (basis subset)))

theorem generalRowSum_truncationEquivalent_closed
    {dimension cutoff bound : ℕ} (hbound : cutoff ≤ bound)
    (column : Fin dimension) :
    ScalarTruncationEquivalent cutoff
      (generalRowSum (generalFactorialRows dimension bound) column)
      (generalClosedSingle column) := by
  apply scalarTruncationEquivalent_of_coeff_eq
  intro degree hdegree
  exact generalRowSum_coeff_eq_closed dimension bound degree
    (hdegree.trans_le hbound) column

theorem generalPairSum_truncationEquivalent_closed
    {dimension cutoff bound : ℕ} (hbound : cutoff ≤ bound)
    (left right : Fin dimension) :
    ScalarTruncationEquivalent cutoff
      (generalPairSum (generalFactorialRows dimension bound) left right)
      (generalClosedPair left right) := by
  apply scalarTruncationEquivalent_of_coeff_eq
  intro degree hdegree
  exact generalPairSum_coeff_stable bound degree
    (hdegree.trans_le hbound) left right

theorem generalOneForm_truncationEquivalent
    {dimension cutoff : ℕ}
    {left right : GeneralSeriesRow dimension}
    (hcoordinates : ∀ index,
      ScalarTruncationEquivalent cutoff (left index) (right index)) :
    ExteriorTruncationEquivalent dimension cutoff
      (generalOneForm left) (generalOneForm right) := by
  unfold generalOneForm
  apply exteriorTruncationEquivalent_finset_sum Finset.univ
  intro index hindex
  exact exteriorTruncationEquivalent_smul (hcoordinates index)
    (exteriorTruncationEquivalent_refl dimension cutoff
      (ExteriorAlgebra.ι ℚ⟦X⟧ (generalBasisVector dimension index)))

theorem generalTwoForm_truncationEquivalent
    {dimension cutoff : ℕ}
    {left right : Fin dimension → Fin dimension → ℚ⟦X⟧}
    (hcoordinates : ∀ i j,
      ScalarTruncationEquivalent cutoff (left i j) (right i j)) :
    ExteriorTruncationEquivalent dimension cutoff
      (generalTwoForm left) (generalTwoForm right) := by
  unfold generalTwoForm generalFullTwoForm
  apply exteriorTruncationEquivalent_smul
    (scalarTruncationEquivalent_refl cutoff (PowerSeries.C (1 / 2 : ℚ)))
  apply exteriorTruncationEquivalent_finset_sum Finset.univ
  intro i hi
  apply exteriorTruncationEquivalent_finset_sum Finset.univ
  intro j hj
  exact exteriorTruncationEquivalent_smul (hcoordinates i j)
    (exteriorTruncationEquivalent_refl dimension cutoff
      (ExteriorAlgebra.ι ℚ⟦X⟧ (generalBasisVector dimension i) *
        ExteriorAlgebra.ι ℚ⟦X⟧ (generalBasisVector dimension j)))

theorem generalEvenAssembly_truncationEquivalent_closed
    (halfDimension cutoff bound : ℕ) (hbound : cutoff ≤ bound) :
    ScalarTruncationEquivalent cutoff
      (generalTopDeterminant (2 * halfDimension)
        (generalTwoForm (fun i j : Fin (2 * halfDimension) =>
          generalPairSum (generalFactorialRows (2 * halfDimension) bound) i j) ^
            halfDimension))
      (generalClosedEvenAssembly halfDimension) := by
  unfold generalClosedEvenAssembly
  apply exteriorTruncationEquivalent_topDeterminant
  apply exteriorTruncationEquivalent_pow
  apply generalTwoForm_truncationEquivalent
  intro i j
  exact generalPairSum_truncationEquivalent_closed hbound i j

theorem generalOddAssembly_truncationEquivalent_closed
    (halfDimension cutoff bound : ℕ) (hbound : cutoff ≤ bound) :
    ScalarTruncationEquivalent cutoff
      (generalTopDeterminant (2 * halfDimension + 1)
        (generalTwoForm (fun i j : Fin (2 * halfDimension + 1) =>
            generalPairSum
              (generalFactorialRows (2 * halfDimension + 1) bound) i j) ^
            halfDimension *
          generalOneForm (generalRowSum
            (generalFactorialRows (2 * halfDimension + 1) bound))))
      (generalClosedOddAssembly halfDimension) := by
  unfold generalClosedOddAssembly
  apply exteriorTruncationEquivalent_topDeterminant
  apply exteriorTruncationEquivalent_mul
  · apply exteriorTruncationEquivalent_pow
    apply generalTwoForm_truncationEquivalent
    intro i j
    exact generalPairSum_truncationEquivalent_closed hbound i j
  · apply generalOneForm_truncationEquivalent
    intro i
    exact generalRowSum_truncationEquivalent_closed hbound i

end FibonacciRibbonKernel
