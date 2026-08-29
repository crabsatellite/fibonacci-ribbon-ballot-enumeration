import FibonacciRibbonKernel.ExteriorHomogeneousBessel

namespace FibonacciRibbonKernel

open ExteriorAlgebra PowerSeries
open scoped Classical

theorem generalOneForm_homogeneous
    {dimension degree : ℕ} (coordinates : GeneralSeriesRow dimension)
    (hcoordinates : ∀ index,
      HomogeneousBesselGenerated degree (coordinates index)) :
    ExteriorHomogeneousBesselGenerated dimension degree
      (generalOneForm coordinates) := by
  unfold generalOneForm
  simpa using exteriorHomogeneous_finsetSum Finset.univ
    (fun index => coordinates index •
      ExteriorAlgebra.ι ℚ⟦X⟧ (generalBasisVector dimension index))
    (fun index _ => by
      have hsmul := exteriorHomogeneous_smul (hcoordinates index)
        (iota_generalBasisVector_homogeneous_zero dimension index)
      simpa using hsmul)

theorem generalFullTwoForm_homogeneous
    {dimension degree : ℕ}
    (coordinates : Fin dimension → Fin dimension → ℚ⟦X⟧)
    (hcoordinates : ∀ left right,
      HomogeneousBesselGenerated degree (coordinates left right)) :
    ExteriorHomogeneousBesselGenerated dimension degree
      (generalFullTwoForm coordinates) := by
  unfold generalFullTwoForm
  simpa using exteriorHomogeneous_finsetSum Finset.univ
    (fun left => ∑ right,
      coordinates left right •
        (ExteriorAlgebra.ι ℚ⟦X⟧ (generalBasisVector dimension left) *
          ExteriorAlgebra.ι ℚ⟦X⟧ (generalBasisVector dimension right)))
    (fun left _ => by
      simpa using exteriorHomogeneous_finsetSum Finset.univ
        (fun right => coordinates left right •
          (ExteriorAlgebra.ι ℚ⟦X⟧ (generalBasisVector dimension left) *
            ExteriorAlgebra.ι ℚ⟦X⟧ (generalBasisVector dimension right)))
        (fun right _ => by
          have hbasis := exteriorHomogeneous_mul
            (iota_generalBasisVector_homogeneous_zero dimension left)
            (iota_generalBasisVector_homogeneous_zero dimension right)
          have hsmul := exteriorHomogeneous_smul
            (hcoordinates left right) hbasis
          simpa using hsmul))

theorem generalTwoForm_homogeneous
    {dimension degree : ℕ}
    (coordinates : Fin dimension → Fin dimension → ℚ⟦X⟧)
    (hcoordinates : ∀ left right,
      HomogeneousBesselGenerated degree (coordinates left right)) :
    ExteriorHomogeneousBesselGenerated dimension degree
      (generalTwoForm coordinates) := by
  unfold generalTwoForm
  have hscalar : HomogeneousBesselGenerated 0
      (PowerSeries.C (1 / 2 : ℚ)) := by
    simpa using homogeneousBessel_polynomial (Polynomial.C (1 / 2 : ℚ))
  have hsmul := exteriorHomogeneous_smul hscalar
    (generalFullTwoForm_homogeneous coordinates hcoordinates)
  simpa using hsmul

theorem generalTopDeterminant_basis_homogeneous_zero
    (dimension : ℕ) (subset : Finset (Fin dimension)) :
    HomogeneousBesselGenerated 0
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
    simpa using homogeneousBessel_polynomial (1 : Polynomial ℚ)
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
    exact HomogeneousBesselGenerated.zero 0

theorem generalTopDeterminant_homogeneous
    {dimension degree : ℕ}
    {element : ExteriorAlgebra ℚ⟦X⟧ (GeneralSeriesRow dimension)}
    (helement : ExteriorHomogeneousBesselGenerated dimension degree element) :
    HomogeneousBesselGenerated degree
      (generalTopDeterminant (R := ℚ⟦X⟧) dimension element) := by
  let basis := generalExteriorBasis dimension
  have hexpansion := basis.sum_repr element
  rw [← hexpansion]
  simp only [map_sum, map_smul]
  simpa only [Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul] using
    HomogeneousBesselGenerated.finsetSum Finset.univ
      (fun subset => basis.repr element subset *
        generalTopDeterminant (R := ℚ⟦X⟧) dimension (basis subset))
      (fun subset _ => by
        have hmul := (helement subset).mul
          (generalTopDeterminant_basis_homogeneous_zero dimension subset)
        simpa using hmul)

theorem generalClosedEvenAssembly_homogeneous
    (halfDimension : ℕ) :
    HomogeneousBesselGenerated halfDimension
      (generalClosedEvenAssembly halfDimension) := by
  unfold generalClosedEvenAssembly
  apply generalTopDeterminant_homogeneous
  have htwo : ExteriorHomogeneousBesselGenerated (2 * halfDimension) 1
      (generalTwoForm (fun i j : Fin (2 * halfDimension) =>
        generalClosedPair i j)) := by
    apply generalTwoForm_homogeneous
    intro left right
    exact generalClosedPair_homogeneousBessel_all left right
  simpa using exteriorHomogeneous_pow htwo halfDimension

end FibonacciRibbonKernel
