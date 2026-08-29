import FibonacciRibbonKernel.SixFactorialRows
import FibonacciRibbonKernel.FiveShiftedPartitions

namespace FibonacciRibbonKernel

open scoped Classical

theorem exists_six_entries_of_length_eq_six {A : Type*}
    (values : List A) (hlength : values.length = 6) :
    ∃ a b c d e f, values = [a, b, c, d, e, f] := by
  cases values with
  | nil => simp at hlength
  | cons a tail =>
      cases tail with
      | nil => simp at hlength
      | cons b tail =>
          cases tail with
          | nil => simp at hlength
          | cons c tail =>
              cases tail with
              | nil => simp at hlength
              | cons d tail =>
                  cases tail with
                  | nil => simp at hlength
                  | cons e tail =>
                      cases tail with
                      | nil => simp at hlength
                      | cons f tail =>
                          have htail : tail = [] := by simpa using hlength
                          subst tail
                          exact ⟨a, b, c, d, e, f, rfl⟩

structure StrictSixAt (size : ℕ) where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  e : ℕ
  f : ℕ
  ab : b < a
  bc : c < b
  cd : d < c
  de : e < d
  ef : f < e
  sum_eq : a + b + c + d + e + f = size + 15

theorem StrictSixAt.ext {size : ℕ} {left right : StrictSixAt size}
    (ha : left.a = right.a) (hb : left.b = right.b)
    (hc : left.c = right.c) (hd : left.d = right.d)
    (he : left.e = right.e) (hf : left.f = right.f) : left = right := by
  cases left
  cases right
  simp_all

def StrictSixAt.values {size : ℕ} (tuple : StrictSixAt size) : Fin 6 → ℕ :=
  sixVector tuple.a tuple.b tuple.c tuple.d tuple.e tuple.f

def StrictSixAt.toList {size : ℕ} (tuple : StrictSixAt size) : List ℕ :=
  [tuple.a, tuple.b, tuple.c, tuple.d, tuple.e, tuple.f]

@[simp] theorem StrictSixAt.toList_length
    {size : ℕ} (tuple : StrictSixAt size) : tuple.toList.length = 6 := rfl

@[simp] theorem StrictSixAt.toList_sum
    {size : ℕ} (tuple : StrictSixAt size) :
    tuple.toList.sum = size + 15 := by
  simpa only [StrictSixAt.toList, List.sum_cons, List.sum_nil, add_zero,
    add_assoc] using tuple.sum_eq

theorem StrictSixAt.toList_pairwise
    {size : ℕ} (tuple : StrictSixAt size) :
    tuple.toList.Pairwise (fun left right => left > right) := by
  have hab := tuple.ab
  have hbc := tuple.bc
  have hcd := tuple.cd
  have hde := tuple.de
  have hef := tuple.ef
  simp [StrictSixAt.toList]
  omega

theorem StrictSixAt.value_lower_bounds
    {size : ℕ} (tuple : StrictSixAt size) :
    5 ≤ tuple.a ∧ 4 ≤ tuple.b ∧ 3 ≤ tuple.c ∧
      2 ≤ tuple.d ∧ 1 ≤ tuple.e := by
  have hab := tuple.ab
  have hbc := tuple.bc
  have hcd := tuple.cd
  have hde := tuple.de
  have hef := tuple.ef
  omega

theorem StrictSixAt.toList_mem_sublistsLen_of_bound
    {size bound : ℕ} (tuple : StrictSixAt size)
    (hbound : size + 6 ≤ bound) :
    tuple.toList ∈ ((List.range bound).reverse.sublistsLen 6) := by
  rw [List.mem_sublistsLen]
  refine ⟨pairwise_gt_sublist_reverse_range tuple.toList bound
    tuple.toList_pairwise ?_, tuple.toList_length⟩
  intro value hvalue
  have hab := tuple.ab
  have hbc := tuple.bc
  have hcd := tuple.cd
  have hde := tuple.de
  have hef := tuple.ef
  have hsum := tuple.sum_eq
  simp [StrictSixAt.toList] at hvalue
  rcases hvalue with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

noncomputable def BoundedPartition.toStrictSixAt
    {size : ℕ} (shape : BoundedPartition 5 size) : StrictSixAt size := by
  let a := (shape.1 0).val + 5
  let b := (shape.1 1).val + 4
  let c := (shape.1 2).val + 3
  let d := (shape.1 3).val + 2
  let e := (shape.1 4).val + 1
  let f := (shape.1 5).val
  refine ⟨a, b, c, d, e, f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : (shape.1 (1 : Fin 6)).val ≤ (shape.1 (0 : Fin 6)).val := by
      simpa using Fin.mk_le_mk.mp (shape.2.1 (0 : Fin 5))
    omega
  · have h : (shape.1 (2 : Fin 6)).val ≤ (shape.1 (1 : Fin 6)).val := by
      simpa using Fin.mk_le_mk.mp (shape.2.1 (1 : Fin 5))
    omega
  · have h : (shape.1 (3 : Fin 6)).val ≤ (shape.1 (2 : Fin 6)).val := by
      simpa using Fin.mk_le_mk.mp (shape.2.1 (2 : Fin 5))
    omega
  · have h : (shape.1 (4 : Fin 6)).val ≤ (shape.1 (3 : Fin 6)).val := by
      simpa using Fin.mk_le_mk.mp (shape.2.1 (3 : Fin 5))
    omega
  · have h : (shape.1 (5 : Fin 6)).val ≤ (shape.1 (4 : Fin 6)).val := by
      simpa using Fin.mk_le_mk.mp (shape.2.1 (4 : Fin 5))
    omega
  · have hsum :
        (shape.1 (0 : Fin 6)).val + (shape.1 (1 : Fin 6)).val +
          (shape.1 (2 : Fin 6)).val + (shape.1 (3 : Fin 6)).val +
          (shape.1 (4 : Fin 6)).val + (shape.1 (5 : Fin 6)).val = size := by
      have hsumAll := shape.2.2
      rw [sum_fin_six] at hsumAll
      exact hsumAll
    omega

noncomputable def StrictSixAt.toBoundedPartition
    {size : ℕ} (tuple : StrictSixAt size) : BoundedPartition 5 size := by
  have hlower := tuple.value_lower_bounds
  let rawRows : Fin 6 → ℕ :=
    sixVector (tuple.a - 5) (tuple.b - 4) (tuple.c - 3)
      (tuple.d - 2) (tuple.e - 1) tuple.f
  have hsum : ∑ row, rawRows row = size := by
    rw [sum_fin_six]
    simp only [rawRows, sixVector_zero, sixVector_one, sixVector_two,
      sixVector_three, sixVector_four, sixVector_five]
    have hab := tuple.ab
    have hbc := tuple.bc
    have hcd := tuple.cd
    have hde := tuple.de
    have hef := tuple.ef
    have htotal := tuple.sum_eq
    omega
  let rows : Fin 6 → Fin (size + 1) := fun row =>
    ⟨rawRows row, by
      have hle : rawRows row ≤ ∑ current, rawRows current :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ row)
      rw [hsum] at hle
      omega⟩
  have hab := tuple.ab
  have hbc := tuple.bc
  have hcd := tuple.cd
  have hde := tuple.de
  have hef := tuple.ef
  refine ⟨rows, ?_, ?_⟩
  · intro index
    fin_cases index
    · change tuple.b - 4 ≤ tuple.a - 5; omega
    · change tuple.c - 3 ≤ tuple.b - 4; omega
    · change tuple.d - 2 ≤ tuple.c - 3; omega
    · change tuple.e - 1 ≤ tuple.d - 2; omega
    · change tuple.f ≤ tuple.e - 1; omega
  · change ∑ row, rawRows row = size
    exact hsum

noncomputable def boundedPartitionStrictSixEquiv (size : ℕ) :
    BoundedPartition 5 size ≃ StrictSixAt size where
  toFun := BoundedPartition.toStrictSixAt
  invFun := StrictSixAt.toBoundedPartition
  left_inv shape := by
    apply Subtype.ext
    funext row
    apply Fin.ext
    fin_cases row <;>
      simp [BoundedPartition.toStrictSixAt,
        StrictSixAt.toBoundedPartition]
  right_inv tuple := by
    cases tuple with
    | mk a b c d e f hab hbc hcd hde hef hsum =>
      apply StrictSixAt.ext <;>
        simp [BoundedPartition.toStrictSixAt,
          StrictSixAt.toBoundedPartition] <;> omega

noncomputable instance strictSixAtFintype (size : ℕ) :
    Fintype (StrictSixAt size) :=
  Fintype.ofEquiv (BoundedPartition 5 size)
    (boundedPartitionStrictSixEquiv size)

theorem boundedFactorialDeterminant_eq_strictSixMatrix
    {size : ℕ} (shape : BoundedPartition 5 size) :
    boundedFactorialDeterminant shape =
      Matrix.det
        (sixFactorialScalarMatrix
          shape.toStrictSixAt.a shape.toStrictSixAt.b
          shape.toStrictSixAt.c shape.toStrictSixAt.d
          shape.toStrictSixAt.e shape.toStrictSixAt.f) := by
  unfold boundedFactorialDeterminant
  apply congrArg Matrix.det
  apply Matrix.ext
  intro row column
  unfold factorialKernelMatrix sixFactorialScalarMatrix
    sixFactorialScalarRow BoundedPartition.shiftedRows
    BoundedPartition.toStrictSixAt
  fin_cases row <;> rfl

theorem strictSixMatrix_eq_boundedFactorialDeterminant
    {size : ℕ} (tuple : StrictSixAt size) :
    Matrix.det
        (sixFactorialScalarMatrix tuple.a tuple.b tuple.c
          tuple.d tuple.e tuple.f) =
      boundedFactorialDeterminant tuple.toBoundedPartition := by
  rw [boundedFactorialDeterminant_eq_strictSixMatrix]
  have hround := (boundedPartitionStrictSixEquiv size).apply_symm_apply tuple
  change tuple.toBoundedPartition.toStrictSixAt = tuple at hround
  have ha := congrArg StrictSixAt.a hround
  have hb := congrArg StrictSixAt.b hround
  have hc := congrArg StrictSixAt.c hround
  have hd := congrArg StrictSixAt.d hround
  have he := congrArg StrictSixAt.e hround
  have hf := congrArg StrictSixAt.f hround
  rw [ha, hb, hc, hd, he, hf]

end FibonacciRibbonKernel
