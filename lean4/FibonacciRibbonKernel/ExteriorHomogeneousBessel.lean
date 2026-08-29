import FibonacciRibbonKernel.HomogeneousBesselRepresentation

namespace FibonacciRibbonKernel

open ExteriorAlgebra PowerSeries
open scoped Classical

def ExteriorHomogeneousBesselGenerated (dimension degree : ℕ)
    (element : ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension)) : Prop :=
  ∀ subset : Finset (Fin dimension),
    HomogeneousBesselGenerated degree
      ((generalExteriorBasis dimension).repr element subset)

theorem exteriorHomogeneous_add
    {dimension degree : ℕ}
    {left right : ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension)}
    (hleft : ExteriorHomogeneousBesselGenerated dimension degree left)
    (hright : ExteriorHomogeneousBesselGenerated dimension degree right) :
    ExteriorHomogeneousBesselGenerated dimension degree (left + right) := by
  intro subset
  simp only [map_add]
  exact (hleft subset).add (hright subset)

theorem exteriorHomogeneous_smul
    {dimension scalarDegree elementDegree : ℕ} {scalar : ℚ⟦X⟧}
    {element : ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension)}
    (hscalar : HomogeneousBesselGenerated scalarDegree scalar)
    (helement : ExteriorHomogeneousBesselGenerated dimension elementDegree element) :
    ExteriorHomogeneousBesselGenerated dimension
      (scalarDegree + elementDegree) (scalar • element) := by
  intro subset
  simp only [map_smul]
  exact hscalar.mul (helement subset)

theorem exteriorHomogeneous_finsetSum
    {dimension degree : ℕ} {indexType : Type*} [DecidableEq indexType]
    (indices : Finset indexType)
    (values : indexType → ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension))
    (hvalues : ∀ index ∈ indices,
      ExteriorHomogeneousBesselGenerated dimension degree (values index)) :
    ExteriorHomogeneousBesselGenerated dimension degree
      (∑ index ∈ indices, values index) := by
  intro subset
  simp only [map_sum, Finset.sum_apply']
  exact HomogeneousBesselGenerated.finsetSum indices
    (fun index => (generalExteriorBasis dimension).repr (values index) subset)
    (fun index hindex => hvalues index hindex subset)

theorem exteriorBasis_homogeneous_zero
    (dimension : ℕ) (subset : Finset (Fin dimension)) :
    ExteriorHomogeneousBesselGenerated dimension 0
      (generalExteriorBasis dimension subset) := by
  intro target
  rw [Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs
  · simpa using homogeneousBessel_polynomial (1 : Polynomial ℚ)
  · exact HomogeneousBesselGenerated.zero 0

theorem iota_generalBasisVector_homogeneous_zero
    (dimension : ℕ) (index : Fin dimension) :
    ExteriorHomogeneousBesselGenerated dimension 0
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
  exact exteriorBasis_homogeneous_zero dimension {index}

theorem exteriorBasis_mul_repr_homogeneous_zero
    (dimension : ℕ) (left right target : Finset (Fin dimension)) :
    HomogeneousBesselGenerated 0
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
    change HomogeneousBesselGenerated 0
      (basis.repr (basis left * basis right) target)
    rcases Int.units_eq_one_or
        (Set.powersetCard.permOfDisjoint hdisjointCard).sign with hsign | hsign
    · have hmulOne : basis left * basis right =
          basis (Set.powersetCard.disjUnion hdisjointCard).val := by
        simpa [hsign] using hmul'
      rw [hmulOne]
      exact exteriorBasis_homogeneous_zero dimension
        (Set.powersetCard.disjUnion hdisjointCard).val target
    · have hmulNeg : basis left * basis right =
          -basis (Set.powersetCard.disjUnion hdisjointCard).val := by
        simpa [hsign] using hmul'
      rw [hmulNeg, map_neg]
      exact (exteriorBasis_homogeneous_zero dimension
        (Set.powersetCard.disjUnion hdisjointCard).val target).neg
  · have hnotCard : ¬Disjoint leftCard.val rightCard.val := by
      simpa [leftCard, rightCard] using hdisjoint
    have hmul := ExteriorAlgebra.basis_mul_of_not_disjoint
      (R := ℚ⟦X⟧) vectorBasis leftCard rightCard hnotCard
    have hmul' : basis left * basis right = 0 := by
      simpa [basis, generalExteriorBasis, vectorBasis, leftCard, rightCard]
        using hmul
    have hmulGeneral : generalExteriorBasis dimension left *
        generalExteriorBasis dimension right = 0 := by
      simpa [basis] using hmul'
    rw [hmulGeneral]
    simp only [map_zero, Finsupp.zero_apply]
    exact HomogeneousBesselGenerated.zero 0

theorem exteriorHomogeneous_mul
    {dimension leftDegree rightDegree : ℕ}
    {left right : ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension)}
    (hleft : ExteriorHomogeneousBesselGenerated dimension leftDegree left)
    (hright : ExteriorHomogeneousBesselGenerated dimension rightDegree right) :
    ExteriorHomogeneousBesselGenerated dimension (leftDegree + rightDegree)
      (left * right) := by
  intro target
  let basis := generalExteriorBasis dimension
  have hleftExpansion := basis.sum_repr left
  have hrightExpansion := basis.sum_repr right
  rw [← hleftExpansion, ← hrightExpansion]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, map_sum, map_smul, Finset.sum_apply',
    Finsupp.smul_apply, smul_eq_mul]
  apply HomogeneousBesselGenerated.finsetSum Finset.univ
  intro rightIndex hrightIndex
  apply HomogeneousBesselGenerated.finsetSum Finset.univ
  intro leftIndex hleftIndex
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (hright rightIndex).mul
      ((hleft leftIndex).mul
        (exteriorBasis_mul_repr_homogeneous_zero
          dimension leftIndex rightIndex target))

theorem exteriorHomogeneous_pow
    {dimension degree : ℕ}
    {element : ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension)}
    (helement : ExteriorHomogeneousBesselGenerated dimension degree element)
    (power : ℕ) :
    ExteriorHomogeneousBesselGenerated dimension (degree * power)
      (element ^ power) := by
  induction power with
  | zero =>
      have hone : (1 : ExteriorAlgebra ℚ⟦X⟧
          (GeneralSeriesRow dimension)) =
          generalExteriorBasis dimension ∅ := by
        rw [generalExteriorBasis]
        rw [ExteriorAlgebra.basis_apply_ofCard
          (Pi.basisFun ℚ⟦X⟧ (Fin dimension)) (n := 0) (by simp)]
        simp [ExteriorAlgebra.ιMulti_family]
      rw [pow_zero, hone]
      simpa using exteriorBasis_homogeneous_zero dimension ∅
  | succ power ih =>
      rw [pow_succ]
      have hmul := exteriorHomogeneous_mul ih helement
      simpa [Nat.mul_add, Nat.add_comm] using hmul

end FibonacciRibbonKernel
