import FibonacciRibbonKernel.ExteriorMinorSumSix
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.FinCases

namespace FibonacciRibbonKernel

open ExteriorAlgebra

variable {R : Type*} [CommRing R]

noncomputable def sixBasisVector (index : Fin 6) : SixRow R :=
  (Pi.basisFun R (Fin 6)) index

noncomputable def sixOneForm (coordinates : SixRow R) :
    ExteriorAlgebra R (SixRow R) :=
  coordinates 0 • ExteriorAlgebra.ι R (sixBasisVector 0) +
    coordinates 1 • ExteriorAlgebra.ι R (sixBasisVector 1) +
    coordinates 2 • ExteriorAlgebra.ι R (sixBasisVector 2) +
    coordinates 3 • ExteriorAlgebra.ι R (sixBasisVector 3) +
    coordinates 4 • ExteriorAlgebra.ι R (sixBasisVector 4) +
    coordinates 5 • ExteriorAlgebra.ι R (sixBasisVector 5)

noncomputable def sixTwoForm
    (coordinates : Fin 6 → Fin 6 → R) :
    ExteriorAlgebra R (SixRow R) :=
  coordinates 0 1 • (ExteriorAlgebra.ι R (sixBasisVector 0) *
      ExteriorAlgebra.ι R (sixBasisVector 1)) +
  coordinates 0 2 • (ExteriorAlgebra.ι R (sixBasisVector 0) *
      ExteriorAlgebra.ι R (sixBasisVector 2)) +
  coordinates 0 3 • (ExteriorAlgebra.ι R (sixBasisVector 0) *
      ExteriorAlgebra.ι R (sixBasisVector 3)) +
  coordinates 0 4 • (ExteriorAlgebra.ι R (sixBasisVector 0) *
      ExteriorAlgebra.ι R (sixBasisVector 4)) +
  coordinates 0 5 • (ExteriorAlgebra.ι R (sixBasisVector 0) *
      ExteriorAlgebra.ι R (sixBasisVector 5)) +
  coordinates 1 2 • (ExteriorAlgebra.ι R (sixBasisVector 1) *
      ExteriorAlgebra.ι R (sixBasisVector 2)) +
  coordinates 1 3 • (ExteriorAlgebra.ι R (sixBasisVector 1) *
      ExteriorAlgebra.ι R (sixBasisVector 3)) +
  coordinates 1 4 • (ExteriorAlgebra.ι R (sixBasisVector 1) *
      ExteriorAlgebra.ι R (sixBasisVector 4)) +
  coordinates 1 5 • (ExteriorAlgebra.ι R (sixBasisVector 1) *
      ExteriorAlgebra.ι R (sixBasisVector 5)) +
  coordinates 2 3 • (ExteriorAlgebra.ι R (sixBasisVector 2) *
      ExteriorAlgebra.ι R (sixBasisVector 3)) +
  coordinates 2 4 • (ExteriorAlgebra.ι R (sixBasisVector 2) *
      ExteriorAlgebra.ι R (sixBasisVector 4)) +
  coordinates 2 5 • (ExteriorAlgebra.ι R (sixBasisVector 2) *
      ExteriorAlgebra.ι R (sixBasisVector 5)) +
  coordinates 3 4 • (ExteriorAlgebra.ι R (sixBasisVector 3) *
      ExteriorAlgebra.ι R (sixBasisVector 4)) +
  coordinates 3 5 • (ExteriorAlgebra.ι R (sixBasisVector 3) *
      ExteriorAlgebra.ι R (sixBasisVector 5)) +
  coordinates 4 5 • (ExteriorAlgebra.ι R (sixBasisVector 4) *
      ExteriorAlgebra.ι R (sixBasisVector 5))

def sixRowSum : List (SixRow R) → SixRow R
  | [] => 0
  | head :: tail => head + sixRowSum tail

def sixPairSum : List (SixRow R) → Fin 6 → Fin 6 → R
  | [], _, _ => 0
  | head :: tail, left, right =>
      head left * sixRowSum tail right -
        head right * sixRowSum tail left +
        sixPairSum tail left right

@[simp] theorem sixRowSum_nil : sixRowSum ([] : List (SixRow R)) = 0 := rfl
@[simp] theorem sixRowSum_cons (head : SixRow R) (tail : List (SixRow R)) :
    sixRowSum (head :: tail) = head + sixRowSum tail := rfl
@[simp] theorem sixPairSum_nil (left right : Fin 6) :
    sixPairSum ([] : List (SixRow R)) left right = 0 := rfl
@[simp] theorem sixPairSum_cons (head : SixRow R)
    (tail : List (SixRow R)) (left right : Fin 6) :
    sixPairSum (head :: tail) left right =
      head left * sixRowSum tail right -
        head right * sixRowSum tail left +
        sixPairSum tail left right := rfl

theorem iota_sixRow_eq_oneForm (row : SixRow R) :
    ExteriorAlgebra.ι R row = sixOneForm row := by
  have hrow : row =
      row 0 • sixBasisVector 0 + row 1 • sixBasisVector 1 +
        row 2 • sixBasisVector 2 + row 3 • sixBasisVector 3 +
        row 4 • sixBasisVector 4 + row 5 • sixBasisVector 5 := by
    funext index
    fin_cases index <;> simp [sixBasisVector]
  calc
    ExteriorAlgebra.ι R row = ExteriorAlgebra.ι R
        (row 0 • sixBasisVector 0 + row 1 • sixBasisVector 1 +
          row 2 • sixBasisVector 2 + row 3 • sixBasisVector 3 +
          row 4 • sixBasisVector 4 + row 5 • sixBasisVector 5) :=
      congrArg _ hrow
    _ = row 0 • ExteriorAlgebra.ι R (sixBasisVector 0) +
          row 1 • ExteriorAlgebra.ι R (sixBasisVector 1) +
          row 2 • ExteriorAlgebra.ι R (sixBasisVector 2) +
          row 3 • ExteriorAlgebra.ι R (sixBasisVector 3) +
          row 4 • ExteriorAlgebra.ι R (sixBasisVector 4) +
          row 5 • ExteriorAlgebra.ι R (sixBasisVector 5) := by simp
    _ = sixOneForm row := rfl

theorem sixOneForm_mul (left right : SixRow R) :
    sixOneForm left * sixOneForm right =
      sixTwoForm (fun i j => left i * right j - left j * right i) := by
  unfold sixOneForm sixTwoForm
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  rw [ExteriorAlgebra.ι_sq_zero, ExteriorAlgebra.ι_sq_zero,
    ExteriorAlgebra.ι_sq_zero, ExteriorAlgebra.ι_sq_zero,
    ExteriorAlgebra.ι_sq_zero, ExteriorAlgebra.ι_sq_zero]
  rw [iota_mul_iota_neg (R := R) (sixBasisVector 1) (sixBasisVector 0),
    iota_mul_iota_neg (R := R) (sixBasisVector 2) (sixBasisVector 0),
    iota_mul_iota_neg (R := R) (sixBasisVector 3) (sixBasisVector 0),
    iota_mul_iota_neg (R := R) (sixBasisVector 4) (sixBasisVector 0),
    iota_mul_iota_neg (R := R) (sixBasisVector 5) (sixBasisVector 0),
    iota_mul_iota_neg (R := R) (sixBasisVector 2) (sixBasisVector 1),
    iota_mul_iota_neg (R := R) (sixBasisVector 3) (sixBasisVector 1),
    iota_mul_iota_neg (R := R) (sixBasisVector 4) (sixBasisVector 1),
    iota_mul_iota_neg (R := R) (sixBasisVector 5) (sixBasisVector 1),
    iota_mul_iota_neg (R := R) (sixBasisVector 3) (sixBasisVector 2),
    iota_mul_iota_neg (R := R) (sixBasisVector 4) (sixBasisVector 2),
    iota_mul_iota_neg (R := R) (sixBasisVector 5) (sixBasisVector 2),
    iota_mul_iota_neg (R := R) (sixBasisVector 4) (sixBasisVector 3),
    iota_mul_iota_neg (R := R) (sixBasisVector 5) (sixBasisVector 3),
    iota_mul_iota_neg (R := R) (sixBasisVector 5) (sixBasisVector 4)]
  module

theorem exteriorElementary_one_eq_sixOneForm
    (rows : List (SixRow R)) :
    exteriorElementary (R := R) 1 rows = sixOneForm (sixRowSum rows) := by
  induction rows with
  | nil => simp [sixRowSum, sixOneForm]
  | cons head tail ih =>
      rw [exteriorElementary_cons_one, iota_sixRow_eq_oneForm, ih]
      rw [sixRowSum_cons]
      unfold sixOneForm
      simp only [Pi.add_apply, add_smul]
      module

theorem exteriorElementary_two_eq_sixTwoForm
    (rows : List (SixRow R)) :
    exteriorElementary (R := R) 2 rows = sixTwoForm (sixPairSum rows) := by
  induction rows with
  | nil => simp [sixPairSum, sixTwoForm]
  | cons head tail ih =>
      rw [exteriorElementary_cons_two, iota_sixRow_eq_oneForm,
        exteriorElementary_one_eq_sixOneForm, sixOneForm_mul, ih]
      have hpair : sixPairSum (head :: tail) =
          fun i j => head i * sixRowSum tail j -
            head j * sixRowSum tail i + sixPairSum tail i j := rfl
      rw [hpair]
      unfold sixTwoForm
      module

end FibonacciRibbonKernel
