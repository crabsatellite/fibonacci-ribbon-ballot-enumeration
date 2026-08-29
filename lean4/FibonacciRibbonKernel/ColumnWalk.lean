import FibonacciRibbonKernel.PrefixBallot

namespace FibonacciRibbonKernel

/-- A literal Fibonacci-ribbon column over an alphabet of size `rank + 1`. -/
inductive Column (rank : ℕ) where
  | singleton (letter : Fin (rank + 1))
  | tall (omitted : Fin (rank + 1))
  deriving DecidableEq

/-- The net difference increment contributed by a literal column. -/
def Column.weight {rank : ℕ} : Column rank → Weight rank
  | .singleton letter => letterWeight rank letter
  | .tall omitted => tallWeight rank omitted

/--
Every nonempty prefix inside a column leaves the walk in the dominant cone.
For a singleton the only nonempty prefix is the complete column.  For a tall
column, `cutoff` selects precisely the increasing letters below `cutoff`, with
the omitted letter removed.
-/
def Column.prefixesDominant {rank : ℕ}
    (state : Weight rank) : Column rank → Prop
  | .singleton letter => Dominant (state + letterWeight rank letter)
  | .tall omitted =>
      ∀ cutoff, Dominant (state + tallPrefixWeight rank omitted cutoff)

theorem singleton_prefixesDominant_iff_endpoint
    {rank : ℕ} {state : Weight rank} (letter : Fin (rank + 1)) :
    (Column.singleton letter).prefixesDominant state ↔
      Dominant (state + (Column.singleton letter).weight) :=
  Iff.rfl

theorem tall_prefixesDominant_iff_endpoint
    {rank : ℕ} {state : Weight rank} (omitted : Fin (rank + 1))
    (hstart : Dominant state) :
    (Column.tall omitted).prefixesDominant state ↔
      Dominant (state + (Column.tall omitted).weight) := by
  constructor
  · intro hall
    have hend := hall (rank + 1)
    simpa [Column.prefixesDominant, Column.weight,
      tallPrefixWeight_at_end] using hend
  · intro hend cutoff
    exact dominant_add_tallPrefixWeight_of_endpoint omitted hstart hend cutoff

/--
Literal column-walk criterion: from a ballot state, a singleton or tall column
can be read prefix by prefix exactly when its endpoint remains dominant.
-/
theorem column_prefixesDominant_iff_endpoint
    {rank : ℕ} {state : Weight rank} (column : Column rank)
    (hstart : Dominant state) :
    column.prefixesDominant state ↔ Dominant (state + column.weight) := by
  cases column with
  | singleton letter => exact singleton_prefixesDominant_iff_endpoint letter
  | tall omitted => exact tall_prefixesDominant_iff_endpoint omitted hstart

end FibonacciRibbonKernel
