import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fin.Basic

namespace FibonacciRibbonKernel

/-- Difference-coordinate carrier for an alphabet of size `rank + 1`. -/
abbrev Weight (rank : ℕ) := Fin rank → ℤ

/--
The literal type-A difference increment of reading one alphabet letter.
Coordinate `i` records `#i - #(i+1)` in zero-based notation.
-/
def letterWeight (rank : ℕ) (x : Fin (rank + 1)) : Weight rank :=
  fun i =>
    (if x = i.castSucc then 1 else 0) -
      (if x = i.succ then 1 else 0)

/-- The net weight of the increasing full-alphabet block. -/
def fullBlockWeight (rank : ℕ) : Weight rank :=
  ∑ x : Fin (rank + 1), letterWeight rank x

/-- The net weight of the increasing tall column omitting `omitted`. -/
def tallWeight (rank : ℕ) (omitted : Fin (rank + 1)) : Weight rank :=
  ∑ x ∈ Finset.univ.erase omitted, letterWeight rank x

end FibonacciRibbonKernel
