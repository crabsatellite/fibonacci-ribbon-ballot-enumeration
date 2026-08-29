import FibonacciRibbonKernel.ExteriorMinorSum
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.FinCases

namespace FibonacciRibbonKernel

open ExteriorAlgebra

variable {R : Type*} [CommRing R]

noncomputable def fiveBasisVector (index : Fin 5) : FiveRow R :=
  (Pi.basisFun R (Fin 5)) index

noncomputable def fiveOneForm (coordinates : FiveRow R) :
    ExteriorAlgebra R (FiveRow R) :=
  coordinates 0 • ExteriorAlgebra.ι R (fiveBasisVector 0) +
    coordinates 1 • ExteriorAlgebra.ι R (fiveBasisVector 1) +
    coordinates 2 • ExteriorAlgebra.ι R (fiveBasisVector 2) +
    coordinates 3 • ExteriorAlgebra.ι R (fiveBasisVector 3) +
    coordinates 4 • ExteriorAlgebra.ι R (fiveBasisVector 4)

noncomputable def fiveTwoForm
    (coordinates : Fin 5 → Fin 5 → R) :
    ExteriorAlgebra R (FiveRow R) :=
  coordinates 0 1 •
      (ExteriorAlgebra.ι R (fiveBasisVector 0) *
        ExteriorAlgebra.ι R (fiveBasisVector 1)) +
    coordinates 0 2 •
      (ExteriorAlgebra.ι R (fiveBasisVector 0) *
        ExteriorAlgebra.ι R (fiveBasisVector 2)) +
    coordinates 0 3 •
      (ExteriorAlgebra.ι R (fiveBasisVector 0) *
        ExteriorAlgebra.ι R (fiveBasisVector 3)) +
    coordinates 0 4 •
      (ExteriorAlgebra.ι R (fiveBasisVector 0) *
        ExteriorAlgebra.ι R (fiveBasisVector 4)) +
    coordinates 1 2 •
      (ExteriorAlgebra.ι R (fiveBasisVector 1) *
        ExteriorAlgebra.ι R (fiveBasisVector 2)) +
    coordinates 1 3 •
      (ExteriorAlgebra.ι R (fiveBasisVector 1) *
        ExteriorAlgebra.ι R (fiveBasisVector 3)) +
    coordinates 1 4 •
      (ExteriorAlgebra.ι R (fiveBasisVector 1) *
        ExteriorAlgebra.ι R (fiveBasisVector 4)) +
    coordinates 2 3 •
      (ExteriorAlgebra.ι R (fiveBasisVector 2) *
        ExteriorAlgebra.ι R (fiveBasisVector 3)) +
    coordinates 2 4 •
      (ExteriorAlgebra.ι R (fiveBasisVector 2) *
        ExteriorAlgebra.ι R (fiveBasisVector 4)) +
    coordinates 3 4 •
      (ExteriorAlgebra.ι R (fiveBasisVector 3) *
        ExteriorAlgebra.ι R (fiveBasisVector 4))

def fiveRowSum : List (FiveRow R) → FiveRow R
  | [] => 0
  | head :: tail => head + fiveRowSum tail

def fivePairSum : List (FiveRow R) → Fin 5 → Fin 5 → R
  | [], _, _ => 0
  | head :: tail, left, right =>
      head left * fiveRowSum tail right -
        head right * fiveRowSum tail left +
        fivePairSum tail left right

@[simp] theorem fiveRowSum_nil : fiveRowSum ([] : List (FiveRow R)) = 0 := rfl

@[simp] theorem fiveRowSum_cons (head : FiveRow R) (tail : List (FiveRow R)) :
    fiveRowSum (head :: tail) = head + fiveRowSum tail := rfl

@[simp] theorem fivePairSum_nil (left right : Fin 5) :
    fivePairSum ([] : List (FiveRow R)) left right = 0 := rfl

@[simp] theorem fivePairSum_cons (head : FiveRow R)
    (tail : List (FiveRow R)) (left right : Fin 5) :
    fivePairSum (head :: tail) left right =
      head left * fiveRowSum tail right -
        head right * fiveRowSum tail left +
        fivePairSum tail left right := rfl

theorem iota_fiveRow_eq_oneForm (row : FiveRow R) :
    ExteriorAlgebra.ι R row = fiveOneForm row := by
  have hrow : row =
      row 0 • fiveBasisVector 0 + row 1 • fiveBasisVector 1 +
        row 2 • fiveBasisVector 2 + row 3 • fiveBasisVector 3 +
        row 4 • fiveBasisVector 4 := by
    funext index
    fin_cases index <;> simp [fiveBasisVector]
  calc
    ExteriorAlgebra.ι R row = ExteriorAlgebra.ι R
        (row 0 • fiveBasisVector 0 + row 1 • fiveBasisVector 1 +
          row 2 • fiveBasisVector 2 + row 3 • fiveBasisVector 3 +
          row 4 • fiveBasisVector 4) := congrArg _ hrow
    _ = row 0 • ExteriorAlgebra.ι R (fiveBasisVector 0) +
          row 1 • ExteriorAlgebra.ι R (fiveBasisVector 1) +
          row 2 • ExteriorAlgebra.ι R (fiveBasisVector 2) +
          row 3 • ExteriorAlgebra.ι R (fiveBasisVector 3) +
          row 4 • ExteriorAlgebra.ι R (fiveBasisVector 4) := by simp
    _ = fiveOneForm row := rfl

theorem fiveOneForm_mul (left right : FiveRow R) :
    fiveOneForm left * fiveOneForm right =
      fiveTwoForm (fun i j => left i * right j - left j * right i) := by
  unfold fiveOneForm fiveTwoForm
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  rw [ExteriorAlgebra.ι_sq_zero, ExteriorAlgebra.ι_sq_zero,
    ExteriorAlgebra.ι_sq_zero, ExteriorAlgebra.ι_sq_zero,
    ExteriorAlgebra.ι_sq_zero]
  rw [iota_mul_iota_neg (R := R) (fiveBasisVector 1) (fiveBasisVector 0),
    iota_mul_iota_neg (R := R) (fiveBasisVector 2) (fiveBasisVector 0),
    iota_mul_iota_neg (R := R) (fiveBasisVector 3) (fiveBasisVector 0),
    iota_mul_iota_neg (R := R) (fiveBasisVector 4) (fiveBasisVector 0),
    iota_mul_iota_neg (R := R) (fiveBasisVector 2) (fiveBasisVector 1),
    iota_mul_iota_neg (R := R) (fiveBasisVector 3) (fiveBasisVector 1),
    iota_mul_iota_neg (R := R) (fiveBasisVector 4) (fiveBasisVector 1),
    iota_mul_iota_neg (R := R) (fiveBasisVector 3) (fiveBasisVector 2),
    iota_mul_iota_neg (R := R) (fiveBasisVector 4) (fiveBasisVector 2),
    iota_mul_iota_neg (R := R) (fiveBasisVector 4) (fiveBasisVector 3)]
  module

theorem exteriorElementary_one_eq_fiveOneForm
    (rows : List (FiveRow R)) :
    exteriorElementary (R := R) 1 rows = fiveOneForm (fiveRowSum rows) := by
  induction rows with
  | nil => simp [fiveRowSum, fiveOneForm]
  | cons head tail ih =>
      rw [exteriorElementary_cons_one, iota_fiveRow_eq_oneForm, ih]
      rw [fiveRowSum_cons]
      unfold fiveOneForm
      simp only [Pi.add_apply, add_smul]
      module

theorem exteriorElementary_two_eq_fiveTwoForm
    (rows : List (FiveRow R)) :
    exteriorElementary (R := R) 2 rows = fiveTwoForm (fivePairSum rows) := by
  induction rows with
  | nil => simp [fivePairSum, fiveTwoForm]
  | cons head tail ih =>
      rw [exteriorElementary_cons_two, iota_fiveRow_eq_oneForm,
        exteriorElementary_one_eq_fiveOneForm, fiveOneForm_mul, ih]
      have hpair : fivePairSum (head :: tail) =
          fun i j => head i * fiveRowSum tail j -
            head j * fiveRowSum tail i + fivePairSum tail i j := rfl
      rw [hpair]
      unfold fiveTwoForm
      module

end FibonacciRibbonKernel
