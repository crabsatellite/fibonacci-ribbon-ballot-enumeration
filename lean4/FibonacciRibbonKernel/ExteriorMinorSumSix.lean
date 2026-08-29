import FibonacciRibbonKernel.ExteriorElementary
import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace FibonacciRibbonKernel

open ExteriorAlgebra

variable {R : Type*} [CommRing R]

abbrev SixRow (R : Type*) [CommRing R] := Fin 6 → R

noncomputable def topSixAlternating (degree : ℕ) :
    SixRow R [⋀^Fin degree]→ₗ[R] R := by
  classical
  by_cases hdegree : degree = 6
  · subst degree
    exact Matrix.detRowAlternating
  · exact 0

noncomputable def topSixDeterminant :
    ExteriorAlgebra R (SixRow R) →ₗ[R] R :=
  ExteriorAlgebra.liftAlternating (topSixAlternating (R := R))

theorem topSixDeterminant_iMulti (rows : Fin 6 → SixRow R) :
    topSixDeterminant (R := R) (ExteriorAlgebra.ιMulti R 6 rows) =
      Matrix.det rows := by
  rw [topSixDeterminant,
    ExteriorAlgebra.liftAlternating_apply_ιMulti]
  change Matrix.detRowAlternating rows = Matrix.det rows
  rfl

@[simp] theorem topSixDeterminant_iota_product
    (first second third fourth fifth sixth : SixRow R) :
    topSixDeterminant (R := R)
        (ExteriorAlgebra.ι R first *
          (ExteriorAlgebra.ι R second *
            (ExteriorAlgebra.ι R third *
              (ExteriorAlgebra.ι R fourth *
                (ExteriorAlgebra.ι R fifth *
                  ExteriorAlgebra.ι R sixth))))) =
      Matrix.det ![first, second, third, fourth, fifth, sixth] := by
  have h := topSixDeterminant_iMulti (R := R)
    ![first, second, third, fourth, fifth, sixth]
  simpa [ExteriorAlgebra.ιMulti_apply] using h

theorem topSixDeterminant_exterior_minor_sum
    (rows : List (SixRow R)) :
    topSixDeterminant (R := R)
        (exteriorElementary 2 rows ^ 3) =
      6 * topSixDeterminant (R := R) (exteriorElementary 6 rows) := by
  rw [exteriorElementary_two_cube]
  exact map_smul (topSixDeterminant (R := R)) 6 _

end FibonacciRibbonKernel
