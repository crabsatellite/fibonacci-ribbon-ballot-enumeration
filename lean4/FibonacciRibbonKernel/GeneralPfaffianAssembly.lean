import FibonacciRibbonKernel.GeneralExteriorMinor
import FibonacciRibbonKernel.ExteriorDividedPowers

namespace FibonacciRibbonKernel

open ExteriorAlgebra PowerSeries

variable {R : Type*} [CommRing R]

/-- Uniform even-dimensional minor-summation/Pfaffian assembly. -/
theorem generalTopDeterminant_even_pair_assembly
    (halfDimension : ℕ)
    (rows : List (GeneralRow (2 * halfDimension) R)) :
    generalTopDeterminant (R := R) (2 * halfDimension)
        (exteriorElementary 2 rows ^ halfDimension) =
      (halfDimension.factorial : R) *
        generalTopDeterminant (R := R) (2 * halfDimension)
          (exteriorElementary (2 * halfDimension) rows) := by
  rw [(exteriorElementary_divided_powers (R := R) rows halfDimension).1]
  exact map_smul (generalTopDeterminant (R := R) (2 * halfDimension))
    (halfDimension.factorial : R) _

/-- Uniform odd-dimensional bordered-Pfaffian assembly. -/
theorem generalTopDeterminant_odd_pair_assembly
    (halfDimension : ℕ)
    (rows : List (GeneralRow (2 * halfDimension + 1) R)) :
    generalTopDeterminant (R := R) (2 * halfDimension + 1)
        (exteriorElementary 2 rows ^ halfDimension *
          exteriorElementary 1 rows) =
      (halfDimension.factorial : R) *
        generalTopDeterminant (R := R) (2 * halfDimension + 1)
          (exteriorElementary (2 * halfDimension + 1) rows) := by
  rw [(exteriorElementary_divided_powers (R := R) rows halfDimension).2]
  exact map_smul (generalTopDeterminant (R := R) (2 * halfDimension + 1))
    (halfDimension.factorial : R) _

theorem generalExteriorTruncation_even_assembly
    (halfDimension bound : ℕ) :
    (halfDimension.factorial : ℚ⟦X⟧) *
        generalExteriorTruncation (2 * halfDimension) bound =
      generalTopDeterminant (R := ℚ⟦X⟧) (2 * halfDimension)
        (exteriorElementary 2
          ((List.range bound).reverse.map
            (generalFactorialPowerSeriesRow (2 * halfDimension))) ^
              halfDimension) := by
  symm
  exact generalTopDeterminant_even_pair_assembly halfDimension _

theorem generalExteriorTruncation_odd_assembly
    (halfDimension bound : ℕ) :
    (halfDimension.factorial : ℚ⟦X⟧) *
        generalExteriorTruncation (2 * halfDimension + 1) bound =
      generalTopDeterminant (R := ℚ⟦X⟧) (2 * halfDimension + 1)
        (exteriorElementary 2
            ((List.range bound).reverse.map
              (generalFactorialPowerSeriesRow (2 * halfDimension + 1))) ^
            halfDimension *
          exteriorElementary 1
            ((List.range bound).reverse.map
              (generalFactorialPowerSeriesRow (2 * halfDimension + 1)))) := by
  symm
  exact generalTopDeterminant_odd_pair_assembly halfDimension _

end FibonacciRibbonKernel
