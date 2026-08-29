import FibonacciRibbonKernel.ExteriorElementary
import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace FibonacciRibbonKernel

open ExteriorAlgebra

variable {R : Type*} [CommRing R]

abbrev FiveRow (R : Type*) [CommRing R] := Fin 5 → R

/-- Alternating family which keeps degree five and evaluates it by the row
determinant, while killing every other exterior degree. -/
noncomputable def topFiveAlternating (degree : ℕ) :
    FiveRow R [⋀^Fin degree]→ₗ[R] R := by
  classical
  by_cases hdegree : degree = 5
  · subst degree
    exact Matrix.detRowAlternating
  · exact 0

/-- Linear top-degree determinant coefficient on the full exterior algebra. -/
noncomputable def topFiveDeterminant :
    ExteriorAlgebra R (FiveRow R) →ₗ[R] R :=
  ExteriorAlgebra.liftAlternating (topFiveAlternating (R := R))

theorem topFiveDeterminant_iMulti (rows : Fin 5 → FiveRow R) :
    topFiveDeterminant (R := R) (ExteriorAlgebra.ιMulti R 5 rows) =
      Matrix.det rows := by
  rw [topFiveDeterminant,
    ExteriorAlgebra.liftAlternating_apply_ιMulti]
  change Matrix.detRowAlternating rows = Matrix.det rows
  rfl

theorem topFiveDeterminant_exterior_minor_sum
    (rows : List (FiveRow R)) :
    topFiveDeterminant (R := R)
        (exteriorElementary 2 rows ^ 2 * exteriorElementary 1 rows) =
      2 * topFiveDeterminant (R := R) (exteriorElementary 5 rows) := by
  rw [exterior_minor_sum_five]
  exact map_smul (topFiveDeterminant (R := R)) 2 _

end FibonacciRibbonKernel
