import FibonacciRibbonKernel.GeneralAssemblyHomogeneousBessel

namespace FibonacciRibbonKernel

open ExteriorAlgebra PowerSeries
open scoped Classical

def ExteriorExponentialHomogeneousBesselGenerated (dimension degree : ℕ)
    (element : ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension)) : Prop :=
  ∀ subset : Finset (Fin dimension),
    ExponentialHomogeneousBesselGenerated degree
      ((generalExteriorBasis dimension).repr element subset)

theorem exteriorExponential_add
    {dimension degree : ℕ}
    {left right : ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension)}
    (hleft : ExteriorExponentialHomogeneousBesselGenerated dimension degree left)
    (hright : ExteriorExponentialHomogeneousBesselGenerated dimension degree right) :
    ExteriorExponentialHomogeneousBesselGenerated dimension degree (left + right) := by
  intro subset
  simp only [map_add]
  exact (hleft subset).add (hright subset)

theorem exteriorExponential_finsetSum
    {dimension degree : ℕ} {indexType : Type*} [DecidableEq indexType]
    (indices : Finset indexType)
    (values : indexType → ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension))
    (hvalues : ∀ index ∈ indices,
      ExteriorExponentialHomogeneousBesselGenerated dimension degree
        (values index)) :
    ExteriorExponentialHomogeneousBesselGenerated dimension degree
      (∑ index ∈ indices, values index) := by
  intro subset
  simp only [map_sum, Finset.sum_apply']
  exact ExponentialHomogeneousBesselGenerated.finsetSum indices
    (fun index => (generalExteriorBasis dimension).repr (values index) subset)
    (fun index hindex => hvalues index hindex subset)

theorem exteriorExponential_smul_homogeneous
    {dimension scalarDegree elementDegree : ℕ} {scalar : ℚ⟦X⟧}
    {element : ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension)}
    (hscalar : ExponentialHomogeneousBesselGenerated scalarDegree scalar)
    (helement : ExteriorHomogeneousBesselGenerated dimension elementDegree element) :
    ExteriorExponentialHomogeneousBesselGenerated dimension
      (scalarDegree + elementDegree) (scalar • element) := by
  intro subset
  simp only [map_smul]
  exact hscalar.mul_homogeneous (helement subset)

theorem exteriorHomogeneous_mul_exponential
    {dimension leftDegree rightDegree : ℕ}
    {left right : ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension)}
    (hleft : ExteriorHomogeneousBesselGenerated dimension leftDegree left)
    (hright : ExteriorExponentialHomogeneousBesselGenerated dimension rightDegree right) :
    ExteriorExponentialHomogeneousBesselGenerated dimension
      (leftDegree + rightDegree) (left * right) := by
  intro target
  let basis := generalExteriorBasis dimension
  have hleftExpansion := basis.sum_repr left
  have hrightExpansion := basis.sum_repr right
  rw [← hleftExpansion, ← hrightExpansion]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, map_sum, map_smul, Finset.sum_apply',
    Finsupp.smul_apply, smul_eq_mul]
  apply ExponentialHomogeneousBesselGenerated.finsetSum Finset.univ
  intro rightIndex hrightIndex
  apply ExponentialHomogeneousBesselGenerated.finsetSum Finset.univ
  intro leftIndex hleftIndex
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (hright rightIndex).mul_homogeneous
      ((hleft leftIndex).mul
        (exteriorBasis_mul_repr_homogeneous_zero
          dimension leftIndex rightIndex target))

theorem generalOneForm_exponentialHomogeneous
    {dimension degree : ℕ} (coordinates : GeneralSeriesRow dimension)
    (hcoordinates : ∀ index,
      ExponentialHomogeneousBesselGenerated degree (coordinates index)) :
    ExteriorExponentialHomogeneousBesselGenerated dimension degree
      (generalOneForm coordinates) := by
  unfold generalOneForm
  simpa using exteriorExponential_finsetSum Finset.univ
    (fun index => coordinates index •
      ExteriorAlgebra.ι ℚ⟦X⟧ (generalBasisVector dimension index))
    (fun index _ => by
      have hsmul := exteriorExponential_smul_homogeneous
        (hcoordinates index)
        (iota_generalBasisVector_homogeneous_zero dimension index)
      simpa using hsmul)

theorem generalTopDeterminant_exponentialHomogeneous
    {dimension degree : ℕ}
    {element : ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension)}
    (helement : ExteriorExponentialHomogeneousBesselGenerated
      dimension degree element) :
    ExponentialHomogeneousBesselGenerated degree
      (generalTopDeterminant (R := ℚ⟦X⟧) dimension element) := by
  let basis := generalExteriorBasis dimension
  have hexpansion := basis.sum_repr element
  rw [← hexpansion]
  simp only [map_sum, map_smul]
  simpa only [Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul] using
    ExponentialHomogeneousBesselGenerated.finsetSum Finset.univ
      (fun subset => basis.repr element subset *
        generalTopDeterminant (R := ℚ⟦X⟧) dimension (basis subset))
      (fun subset _ => by
        have hmul := (helement subset).mul_homogeneous
          (generalTopDeterminant_basis_homogeneous_zero dimension subset)
        simpa using hmul)

theorem generalClosedOddAssembly_exponentialHomogeneous
    (halfDimension : ℕ) :
    ExponentialHomogeneousBesselGenerated halfDimension
      (generalClosedOddAssembly halfDimension) := by
  unfold generalClosedOddAssembly
  apply generalTopDeterminant_exponentialHomogeneous
  have htwo : ExteriorHomogeneousBesselGenerated (2 * halfDimension + 1) 1
      (generalTwoForm (fun i j : Fin (2 * halfDimension + 1) =>
        generalClosedPair i j)) := by
    apply generalTwoForm_homogeneous
    intro left right
    exact generalClosedPair_homogeneousBessel_all left right
  have hpow := exteriorHomogeneous_pow htwo halfDimension
  have hone : ExteriorExponentialHomogeneousBesselGenerated
      (2 * halfDimension + 1) 0
      (generalOneForm (fun i : Fin (2 * halfDimension + 1) =>
        generalClosedSingle i)) := by
    apply generalOneForm_exponentialHomogeneous
    intro index
    exact generalClosedSingle_exponentialHomogeneous index
  simpa using exteriorHomogeneous_mul_exponential hpow hone

end FibonacciRibbonKernel
