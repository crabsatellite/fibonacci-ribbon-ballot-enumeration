import FibonacciRibbonKernel.GeneralClosedBridge
import FibonacciRibbonKernel.GeneralBesselReduction

namespace FibonacciRibbonKernel

open ExteriorAlgebra PowerSeries
open scoped Classical

inductive BesselGenerated : ℚ⟦X⟧ → Prop
  | polynomial (value : Polynomial ℚ) : BesselGenerated (value : ℚ⟦X⟧)
  | besselZero : BesselGenerated (literalBesselJ 0)
  | besselOne : BesselGenerated (literalBesselJ 1)
  | exponential : BesselGenerated (PowerSeries.exp ℚ)
  | add {left right} : BesselGenerated left → BesselGenerated right →
      BesselGenerated (left + right)
  | neg {value} : BesselGenerated value → BesselGenerated (-value)
  | mul {left right} : BesselGenerated left → BesselGenerated right →
      BesselGenerated (left * right)

theorem BesselGenerated.zero : BesselGenerated 0 := by
  simpa using BesselGenerated.polynomial (0 : Polynomial ℚ)

theorem BesselGenerated.one : BesselGenerated 1 := by
  simpa using BesselGenerated.polynomial (1 : Polynomial ℚ)

theorem BesselGenerated.constant (value : ℚ) :
    BesselGenerated (PowerSeries.C value) := by
  simpa using BesselGenerated.polynomial (Polynomial.C value)

theorem BesselGenerated.sub {left right : ℚ⟦X⟧}
    (hleft : BesselGenerated left) (hright : BesselGenerated right) :
    BesselGenerated (left - right) := by
  rw [sub_eq_add_neg]
  exact hleft.add hright.neg

theorem BesselGenerated.finsetSum
    {indexType : Type*} [DecidableEq indexType]
    (indices : Finset indexType) (values : indexType → ℚ⟦X⟧)
    (h : ∀ index ∈ indices, BesselGenerated (values index)) :
    BesselGenerated (∑ index ∈ indices, values index) := by
  induction indices using Finset.induction_on with
  | empty => exact BesselGenerated.zero
  | @insert index indices hindex ih =>
      rw [Finset.sum_insert hindex]
      exact (h index (Finset.mem_insert_self index indices)).add
        (ih fun current hcurrent => h current (Finset.mem_insert_of_mem hcurrent))

theorem polynomial_X_pow_mul_coe (degree : ℕ) (value : Polynomial ℚ) :
    ((Polynomial.X ^ degree * value : Polynomial ℚ) : ℚ⟦X⟧) =
      X ^ degree * (value : ℚ⟦X⟧) := by
  calc
    ((Polynomial.X ^ degree * value : Polynomial ℚ) : ℚ⟦X⟧) =
        ((1 * Polynomial.X ^ degree * value : Polynomial ℚ) : ℚ⟦X⟧) := by
          rw [one_mul]
    _ = ((1 : Polynomial ℚ) : ℚ⟦X⟧) *
          ((Polynomial.X ^ degree : Polynomial ℚ) : ℚ⟦X⟧) *
          (value : ℚ⟦X⟧) :=
      polynomial_coe_triple_mul (1 : Polynomial ℚ)
        (Polynomial.X ^ degree) value
    _ = X ^ degree * (value : ℚ⟦X⟧) := by simp

theorem generalClosedPair_besselGenerated
    {rank gap : ℕ} (left right : Fin (rank + 1))
    (hgap : left.rev.val = right.rev.val + gap) (hgapPos : 1 ≤ gap) :
    BesselGenerated (generalClosedPair left right) := by
  rw [generalClosedPair_polynomial_bessel_reduction left right hgap hgapPos]
  have hp : BesselGenerated
      (X ^ (2 * right.rev.val) * (pairReductionP gap : ℚ⟦X⟧)) := by
    rw [← polynomial_X_pow_mul_coe]
    exact BesselGenerated.polynomial _
  have hq : BesselGenerated
      (X ^ (2 * right.rev.val) * (pairReductionQ gap : ℚ⟦X⟧)) := by
    rw [← polynomial_X_pow_mul_coe]
    exact BesselGenerated.polynomial _
  exact (hp.mul BesselGenerated.besselZero).add
    (hq.mul BesselGenerated.besselOne)

theorem generalClosedPair_besselGenerated_all
    {dimension : ℕ} (left right : Fin dimension) :
    BesselGenerated (generalClosedPair left right) := by
  cases dimension with
  | zero => exact Fin.elim0 left
  | succ rank =>
      by_cases heq : left = right
      · subst right
        rw [generalClosedPair_self]
        exact BesselGenerated.zero
      by_cases horder : right.rev.val < left.rev.val
      · let gap := left.rev.val - right.rev.val
        exact generalClosedPair_besselGenerated (gap := gap) left right
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
        apply BesselGenerated.neg
        let gap := right.rev.val - left.rev.val
        exact generalClosedPair_besselGenerated (gap := gap) right left
          (by dsimp only [gap]; omega) (by dsimp only [gap]; omega)

theorem generalClosedSingle_besselGenerated
    {dimension : ℕ} (index : Fin dimension) :
    BesselGenerated (generalClosedSingle index) := by
  unfold generalClosedSingle
  have hpoly : BesselGenerated (X ^ index.rev.val : ℚ⟦X⟧) := by
    simpa using BesselGenerated.polynomial
      (Polynomial.X ^ index.rev.val)
  exact hpoly.mul BesselGenerated.exponential

def ExteriorBesselGenerated (dimension : ℕ)
    (element : ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension)) : Prop :=
  ∀ subset : Finset (Fin dimension),
    BesselGenerated ((generalExteriorBasis dimension).repr element subset)

theorem exteriorBesselGenerated_add
    {dimension : ℕ} {left right :
      ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension)}
    (hleft : ExteriorBesselGenerated dimension left)
    (hright : ExteriorBesselGenerated dimension right) :
    ExteriorBesselGenerated dimension (left + right) := by
  intro subset
  simp only [map_add]
  exact (hleft subset).add (hright subset)

theorem exteriorBesselGenerated_smul
    {dimension : ℕ} {scalar : ℚ⟦X⟧}
    {element : ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension)}
    (hscalar : BesselGenerated scalar)
    (helement : ExteriorBesselGenerated dimension element) :
    ExteriorBesselGenerated dimension (scalar • element) := by
  intro subset
  simp only [map_smul]
  exact hscalar.mul (helement subset)

theorem exteriorBesselGenerated_finsetSum
    {dimension : ℕ} {indexType : Type*} [DecidableEq indexType]
    (indices : Finset indexType)
    (values : indexType →
      ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension))
    (h : ∀ index ∈ indices, ExteriorBesselGenerated dimension (values index)) :
    ExteriorBesselGenerated dimension (∑ index ∈ indices, values index) := by
  intro subset
  simp only [map_sum, Finset.sum_apply']
  exact BesselGenerated.finsetSum indices
    (fun index => (generalExteriorBasis dimension).repr (values index) subset)
    (fun index hindex => h index hindex subset)

theorem exteriorBasis_mul_repr_besselGenerated
    (dimension : ℕ) (left right target : Finset (Fin dimension)) :
    BesselGenerated
      ((generalExteriorBasis dimension).repr
        (generalExteriorBasis dimension left *
          generalExteriorBasis dimension right) target) := by
  let vectorBasis := Pi.basisFun ℚ⟦X⟧ (Fin dimension)
  let basis := generalExteriorBasis dimension
  let leftCard : Set.powersetCard (Fin dimension) left.card :=
    ⟨left, by simp⟩
  let rightCard : Set.powersetCard (Fin dimension) right.card :=
    ⟨right, by simp⟩
  by_cases hdisjoint : Disjoint left right
  · have hdisjointCard : Disjoint leftCard.val rightCard.val := by
      simpa [leftCard, rightCard] using hdisjoint
    have hmul := ExteriorAlgebra.basis_mul_of_disjoint
      (R := ℚ⟦X⟧) vectorBasis leftCard rightCard hdisjointCard
    have hmul' : basis left * basis right =
        (Set.powersetCard.permOfDisjoint hdisjointCard).sign •
          basis (Set.powersetCard.disjUnion hdisjointCard).val := by
      simpa [basis, generalExteriorBasis, vectorBasis, leftCard, rightCard]
        using hmul
    change BesselGenerated (basis.repr (basis left * basis right) target)
    rcases Int.units_eq_one_or
        (Set.powersetCard.permOfDisjoint hdisjointCard).sign with hsign | hsign
    · have hmulOne : basis left * basis right =
          basis (Set.powersetCard.disjUnion hdisjointCard).val := by
        simpa [hsign] using hmul'
      rw [hmulOne, Module.Basis.repr_self]
      by_cases htarget : target =
          (Set.powersetCard.disjUnion hdisjointCard).val
      · subst target
        simp only [Finsupp.single_eq_same]
        exact BesselGenerated.one
      · rw [Finsupp.single_apply]
        simp only [Ne.symm htarget, ↓reduceIte]
        exact BesselGenerated.zero
    · have hmulNeg : basis left * basis right =
          -basis (Set.powersetCard.disjUnion hdisjointCard).val := by
        simpa [hsign] using hmul'
      rw [hmulNeg, map_neg, Module.Basis.repr_self]
      by_cases htarget : target =
          (Set.powersetCard.disjUnion hdisjointCard).val
      · subst target
        simp only [Finsupp.neg_apply, Finsupp.single_eq_same]
        exact BesselGenerated.one.neg
      · rw [Finsupp.neg_apply, Finsupp.single_apply]
        simp only [Ne.symm htarget, ↓reduceIte, neg_zero]
        exact BesselGenerated.zero
  · have hnotCard : ¬ Disjoint leftCard.val rightCard.val := by
      simpa [leftCard, rightCard] using hdisjoint
    have hmul := ExteriorAlgebra.basis_mul_of_not_disjoint
      (R := ℚ⟦X⟧) vectorBasis leftCard rightCard hnotCard
    have hmul' : basis left * basis right = 0 := by
      simpa [basis, generalExteriorBasis, vectorBasis, leftCard, rightCard]
        using hmul
    change BesselGenerated (basis.repr (basis left * basis right) target)
    rw [hmul']
    simp only [map_zero, Finsupp.zero_apply]
    exact BesselGenerated.zero

theorem exteriorBesselGenerated_mul
    {dimension : ℕ} {left right :
      ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension)}
    (hleft : ExteriorBesselGenerated dimension left)
    (hright : ExteriorBesselGenerated dimension right) :
    ExteriorBesselGenerated dimension (left * right) := by
  intro target
  let basis := generalExteriorBasis dimension
  have hleftExpansion := basis.sum_repr left
  have hrightExpansion := basis.sum_repr right
  rw [← hleftExpansion, ← hrightExpansion]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, map_sum, map_smul, Finset.sum_apply',
    Finsupp.smul_apply, smul_eq_mul]
  apply BesselGenerated.finsetSum Finset.univ
  intro rightIndex hrightIndex
  apply BesselGenerated.finsetSum Finset.univ
  intro leftIndex hleftIndex
  exact (hright rightIndex).mul
    ((hleft leftIndex).mul
      (exteriorBasis_mul_repr_besselGenerated
        dimension leftIndex rightIndex target))

theorem exteriorBasis_besselGenerated
    (dimension : ℕ) (subset : Finset (Fin dimension)) :
    ExteriorBesselGenerated dimension
      (generalExteriorBasis dimension subset) := by
  intro target
  rw [Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs
  · exact BesselGenerated.one
  · exact BesselGenerated.zero

theorem iota_generalBasisVector_besselGenerated
    (dimension : ℕ) (index : Fin dimension) :
    ExteriorBesselGenerated dimension
      (ExteriorAlgebra.ι ℚ⟦X⟧ (generalBasisVector dimension index)) := by
  have hι : ExteriorAlgebra.ι ℚ⟦X⟧
        (generalBasisVector dimension index) =
      generalExteriorBasis dimension {index} := by
    have hcard : ({index} : Finset (Fin dimension)).card = 1 := by simp
    rw [generalExteriorBasis]
    rw [ExteriorAlgebra.basis_apply_ofCard
      (Pi.basisFun ℚ⟦X⟧ (Fin dimension)) (n := 1) hcard]
    dsimp only [ExteriorAlgebra.ιMulti_family]
    rw [ExteriorAlgebra.ιMulti_succ_apply,
      ExteriorAlgebra.ιMulti_zero_apply, mul_one]
    congr 2
    symm
    apply Finset.mem_singleton.mp
    exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
      (I := Fin dimension) (n := 1)
      (Set.powersetCard.ofCard hcard) _).mp ⟨(0 : Fin 1), rfl⟩
  rw [hι]
  exact exteriorBasis_besselGenerated dimension {index}

theorem generalOneForm_besselGenerated
    {dimension : ℕ} (coordinates : GeneralSeriesRow dimension)
    (hcoordinates : ∀ index, BesselGenerated (coordinates index)) :
    ExteriorBesselGenerated dimension (generalOneForm coordinates) := by
  unfold generalOneForm
  simpa using exteriorBesselGenerated_finsetSum Finset.univ
    (fun index => coordinates index •
      ExteriorAlgebra.ι ℚ⟦X⟧ (generalBasisVector dimension index))
    (fun index _ => exteriorBesselGenerated_smul
      (hcoordinates index)
      (iota_generalBasisVector_besselGenerated dimension index))

theorem generalFullTwoForm_besselGenerated
    {dimension : ℕ}
    (coordinates : Fin dimension → Fin dimension → ℚ⟦X⟧)
    (hcoordinates : ∀ left right,
      BesselGenerated (coordinates left right)) :
    ExteriorBesselGenerated dimension (generalFullTwoForm coordinates) := by
  unfold generalFullTwoForm
  simpa using exteriorBesselGenerated_finsetSum Finset.univ
    (fun left => ∑ right,
      coordinates left right •
        (ExteriorAlgebra.ι ℚ⟦X⟧ (generalBasisVector dimension left) *
          ExteriorAlgebra.ι ℚ⟦X⟧ (generalBasisVector dimension right)))
    (fun left _ => by
      simpa using exteriorBesselGenerated_finsetSum Finset.univ
        (fun right => coordinates left right •
          (ExteriorAlgebra.ι ℚ⟦X⟧ (generalBasisVector dimension left) *
            ExteriorAlgebra.ι ℚ⟦X⟧ (generalBasisVector dimension right)))
        (fun right _ => exteriorBesselGenerated_smul
          (hcoordinates left right)
          (exteriorBesselGenerated_mul
            (iota_generalBasisVector_besselGenerated dimension left)
            (iota_generalBasisVector_besselGenerated dimension right))))

theorem generalTwoForm_besselGenerated
    {dimension : ℕ}
    (coordinates : Fin dimension → Fin dimension → ℚ⟦X⟧)
    (hcoordinates : ∀ left right,
      BesselGenerated (coordinates left right)) :
    ExteriorBesselGenerated dimension (generalTwoForm coordinates) := by
  unfold generalTwoForm
  exact exteriorBesselGenerated_smul (BesselGenerated.constant (1 / 2))
    (generalFullTwoForm_besselGenerated coordinates hcoordinates)

theorem exteriorBesselGenerated_pow
    {dimension : ℕ}
    {element : ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension)}
    (helement : ExteriorBesselGenerated dimension element) (degree : ℕ) :
    ExteriorBesselGenerated dimension (element ^ degree) := by
  induction degree with
  | zero =>
      have hone : (1 : ExteriorAlgebra ℚ⟦X⟧
          (GeneralSeriesRow dimension)) =
          generalExteriorBasis dimension ∅ := by
        rw [generalExteriorBasis]
        rw [ExteriorAlgebra.basis_apply_ofCard
          (Pi.basisFun ℚ⟦X⟧ (Fin dimension)) (n := 0) (by simp)]
        simp [ExteriorAlgebra.ιMulti_family]
      rw [pow_zero, hone]
      exact exteriorBasis_besselGenerated dimension ∅
  | succ degree ih =>
      rw [pow_succ]
      exact exteriorBesselGenerated_mul ih helement

theorem generalTopDeterminant_basis_besselGenerated
    (dimension : ℕ) (subset : Finset (Fin dimension)) :
    BesselGenerated
      (generalTopDeterminant (R := ℚ⟦X⟧) dimension
        (generalExteriorBasis dimension subset)) := by
  by_cases hsubset : subset = Finset.univ
  · subst subset
    have hvalue : generalTopDeterminant (R := ℚ⟦X⟧) dimension
          (generalExteriorBasis dimension
            (Finset.univ : Finset (Fin dimension))) = 1 := by
      have hcard : (Finset.univ : Finset (Fin dimension)).card = dimension := by
        rw [Finset.card_univ]
        exact Fintype.card_fin dimension
      rw [generalExteriorBasis]
      rw [ExteriorAlgebra.basis_apply_ofCard
        (Pi.basisFun ℚ⟦X⟧ (Fin dimension)) (n := dimension) hcard]
      dsimp only [ExteriorAlgebra.ιMulti_family]
      have henumeration :
          Set.powersetCard.ofFinEmbEquiv.symm
              (Set.powersetCard.ofCard hcard) =
            OrderEmbedding.id (Fin dimension) := by
        rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
        symm
        exact Finset.orderEmbOfFin_unique' hcard
          (fun index => Finset.mem_univ index)
      rw [henumeration]
      rw [generalTopDeterminant_iMulti]
      have hbasisMatrix :
          (fun index => (Pi.basisFun ℚ⟦X⟧ (Fin dimension)) index) =
            (1 : Matrix (Fin dimension) (Fin dimension) ℚ⟦X⟧) := by
        apply Matrix.ext
        intro row column
        by_cases heq : row = column
        · subst column
          simp
        · simp [heq]
      change Matrix.det
        (fun index => (Pi.basisFun ℚ⟦X⟧ (Fin dimension)) index) = 1
      rw [hbasisMatrix, Matrix.det_one]
    rw [hvalue]
    exact BesselGenerated.one
  · have hcard : subset.card ≠ dimension := by
      intro heq
      apply hsubset
      exact Finset.eq_univ_of_card subset (by simpa using heq)
    have hvalue : generalTopDeterminant (R := ℚ⟦X⟧) dimension
          (generalExteriorBasis dimension subset) = 0 := by
      rw [generalExteriorBasis, ExteriorAlgebra.basis_apply]
      dsimp only [ExteriorAlgebra.ιMulti_family]
      rw [generalTopDeterminant,
        ExteriorAlgebra.liftAlternating_apply_ιMulti]
      simp [generalTopAlternating, hcard]
    rw [hvalue]
    exact BesselGenerated.zero

theorem generalTopDeterminant_besselGenerated
    {dimension : ℕ}
    {element : ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension)}
    (helement : ExteriorBesselGenerated dimension element) :
    BesselGenerated
      (generalTopDeterminant (R := ℚ⟦X⟧) dimension element) := by
  let basis := generalExteriorBasis dimension
  have hexpansion := basis.sum_repr element
  rw [← hexpansion]
  simp only [map_sum, map_smul]
  simpa only [Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul] using
    BesselGenerated.finsetSum Finset.univ
      (fun subset => basis.repr element subset *
        generalTopDeterminant (R := ℚ⟦X⟧) dimension (basis subset))
      (fun subset _ => (helement subset).mul
        (generalTopDeterminant_basis_besselGenerated dimension subset))

theorem generalClosedEvenAssembly_besselGenerated (halfDimension : ℕ) :
    BesselGenerated (generalClosedEvenAssembly halfDimension) := by
  unfold generalClosedEvenAssembly
  apply generalTopDeterminant_besselGenerated
  apply exteriorBesselGenerated_pow
  apply generalTwoForm_besselGenerated
  intro left right
  exact generalClosedPair_besselGenerated_all left right

theorem generalClosedOddAssembly_besselGenerated (halfDimension : ℕ) :
    BesselGenerated (generalClosedOddAssembly halfDimension) := by
  unfold generalClosedOddAssembly
  apply generalTopDeterminant_besselGenerated
  apply exteriorBesselGenerated_mul
  · apply exteriorBesselGenerated_pow
    apply generalTwoForm_besselGenerated
    intro left right
    exact generalClosedPair_besselGenerated_all left right
  · apply generalOneForm_besselGenerated
    intro index
    exact generalClosedSingle_besselGenerated index

end FibonacciRibbonKernel
