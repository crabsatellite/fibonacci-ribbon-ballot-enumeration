import FibonacciRibbonKernel.GeneralExteriorCoordinates

namespace FibonacciRibbonKernel

open ExteriorAlgebra PowerSeries

noncomputable def generalClosedEvenAssembly (halfDimension : ℕ) : ℚ⟦X⟧ :=
  generalTopDeterminant (R := ℚ⟦X⟧) (2 * halfDimension)
    (generalTwoForm (fun i j : Fin (2 * halfDimension) =>
      generalClosedPair i j) ^ halfDimension)

noncomputable def generalClosedOddAssembly (halfDimension : ℕ) : ℚ⟦X⟧ :=
  generalTopDeterminant (R := ℚ⟦X⟧) (2 * halfDimension + 1)
    (generalTwoForm (fun i j : Fin (2 * halfDimension + 1) =>
        generalClosedPair i j) ^ halfDimension *
      generalOneForm (fun i : Fin (2 * halfDimension + 1) =>
        generalClosedSingle i))

theorem generalExteriorTruncation_even_coordinate_assembly
    (halfDimension bound : ℕ) :
    (halfDimension.factorial : ℚ⟦X⟧) *
        generalExteriorTruncation (2 * halfDimension) bound =
      generalTopDeterminant (R := ℚ⟦X⟧) (2 * halfDimension)
        (generalTwoForm (fun i j : Fin (2 * halfDimension) =>
          generalPairSum (generalFactorialRows (2 * halfDimension) bound) i j) ^
            halfDimension) := by
  rw [generalExteriorTruncation_even_assembly]
  rw [exteriorElementary_two_eq_generalTwoForm]
  rfl

theorem generalExteriorTruncation_odd_coordinate_assembly
    (halfDimension bound : ℕ) :
    (halfDimension.factorial : ℚ⟦X⟧) *
        generalExteriorTruncation (2 * halfDimension + 1) bound =
      generalTopDeterminant (R := ℚ⟦X⟧) (2 * halfDimension + 1)
        (generalTwoForm (fun i j : Fin (2 * halfDimension + 1) =>
            generalPairSum
              (generalFactorialRows (2 * halfDimension + 1) bound) i j) ^
            halfDimension *
          generalOneForm (generalRowSum
            (generalFactorialRows (2 * halfDimension + 1) bound))) := by
  rw [generalExteriorTruncation_odd_assembly]
  rw [exteriorElementary_two_eq_generalTwoForm,
    exteriorElementary_one_eq_generalOneForm]
  rfl

end FibonacciRibbonKernel
