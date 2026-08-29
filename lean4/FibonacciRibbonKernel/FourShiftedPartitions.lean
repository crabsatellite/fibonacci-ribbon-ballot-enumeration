import FibonacciRibbonKernel.FourFactorialRows
import FibonacciRibbonKernel.FiveShiftedPartitions

namespace FibonacciRibbonKernel

open scoped Classical

theorem exists_four_entries_of_length_eq_four {A : Type*}
    (values : List A) (hlength : values.length = 4) :
    ∃ a b c d, values = [a, b, c, d] := by
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
                  have htail : tail = [] := by simpa using hlength
                  subst tail
                  exact ⟨a, b, c, d, rfl⟩

structure StrictFourAt (size : ℕ) where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  ab : b < a
  bc : c < b
  cd : d < c
  sum_eq : a + b + c + d = size + 6

theorem StrictFourAt.ext {size : ℕ} {left right : StrictFourAt size}
    (ha : left.a = right.a) (hb : left.b = right.b)
    (hc : left.c = right.c) (hd : left.d = right.d) : left = right := by
  cases left
  cases right
  simp_all

def StrictFourAt.toList {size : ℕ} (tuple : StrictFourAt size) : List ℕ :=
  [tuple.a, tuple.b, tuple.c, tuple.d]

@[simp] theorem StrictFourAt.toList_length
    {size : ℕ} (tuple : StrictFourAt size) : tuple.toList.length = 4 := rfl

@[simp] theorem StrictFourAt.toList_sum
    {size : ℕ} (tuple : StrictFourAt size) :
    tuple.toList.sum = size + 6 := by
  simpa only [StrictFourAt.toList, List.sum_cons, List.sum_nil,
    add_zero, add_assoc] using tuple.sum_eq

theorem StrictFourAt.toList_pairwise
    {size : ℕ} (tuple : StrictFourAt size) :
    tuple.toList.Pairwise (fun left right => left > right) := by
  have hab := tuple.ab
  have hbc := tuple.bc
  have hcd := tuple.cd
  simp [StrictFourAt.toList]
  omega

theorem StrictFourAt.value_lower_bounds
    {size : ℕ} (tuple : StrictFourAt size) :
    3 ≤ tuple.a ∧ 2 ≤ tuple.b ∧ 1 ≤ tuple.c := by
  have hab := tuple.ab
  have hbc := tuple.bc
  have hcd := tuple.cd
  omega

theorem StrictFourAt.toList_mem_sublistsLen_of_bound
    {size bound : ℕ} (tuple : StrictFourAt size)
    (hbound : size + 4 ≤ bound) :
    tuple.toList ∈ ((List.range bound).reverse.sublistsLen 4) := by
  rw [List.mem_sublistsLen]
  refine ⟨pairwise_gt_sublist_reverse_range tuple.toList bound
    tuple.toList_pairwise ?_, tuple.toList_length⟩
  intro value hvalue
  have hab := tuple.ab
  have hbc := tuple.bc
  have hcd := tuple.cd
  have hsum := tuple.sum_eq
  simp [StrictFourAt.toList] at hvalue
  rcases hvalue with rfl | rfl | rfl | rfl <;> omega

noncomputable def BoundedPartition.toStrictFourAt
    {size : ℕ} (shape : BoundedPartition 3 size) : StrictFourAt size := by
  let a := (shape.1 0).val + 3
  let b := (shape.1 1).val + 2
  let c := (shape.1 2).val + 1
  let d := (shape.1 3).val
  refine ⟨a, b, c, d, ?_, ?_, ?_, ?_⟩
  · have h : (shape.1 (1 : Fin 4)).val ≤ (shape.1 (0 : Fin 4)).val := by
      simpa using Fin.mk_le_mk.mp (shape.2.1 (0 : Fin 3))
    omega
  · have h : (shape.1 (2 : Fin 4)).val ≤ (shape.1 (1 : Fin 4)).val := by
      simpa using Fin.mk_le_mk.mp (shape.2.1 (1 : Fin 3))
    omega
  · have h : (shape.1 (3 : Fin 4)).val ≤ (shape.1 (2 : Fin 4)).val := by
      simpa using Fin.mk_le_mk.mp (shape.2.1 (2 : Fin 3))
    omega
  · have hsum :
        (shape.1 (0 : Fin 4)).val + (shape.1 (1 : Fin 4)).val +
          (shape.1 (2 : Fin 4)).val + (shape.1 (3 : Fin 4)).val = size := by
      have hsumAll := shape.2.2
      rw [sum_fin_four] at hsumAll
      exact hsumAll
    omega

noncomputable def StrictFourAt.toBoundedPartition
    {size : ℕ} (tuple : StrictFourAt size) : BoundedPartition 3 size := by
  have hlower := tuple.value_lower_bounds
  let rawRows : Fin 4 → ℕ :=
    fourVector (tuple.a - 3) (tuple.b - 2) (tuple.c - 1) tuple.d
  have hsum : ∑ row, rawRows row = size := by
    rw [sum_fin_four]
    simp only [rawRows, fourVector_zero, fourVector_one,
      fourVector_two, fourVector_three]
    have hab := tuple.ab
    have hbc := tuple.bc
    have hcd := tuple.cd
    have htotal := tuple.sum_eq
    omega
  let rows : Fin 4 → Fin (size + 1) := fun row =>
    ⟨rawRows row, by
      have hle : rawRows row ≤ ∑ current, rawRows current :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ row)
      rw [hsum] at hle
      omega⟩
  have hab := tuple.ab
  have hbc := tuple.bc
  have hcd := tuple.cd
  refine ⟨rows, ?_, ?_⟩
  · intro index
    fin_cases index
    · change tuple.b - 2 ≤ tuple.a - 3; omega
    · change tuple.c - 1 ≤ tuple.b - 2; omega
    · change tuple.d ≤ tuple.c - 1; omega
  · change ∑ row, rawRows row = size
    exact hsum

noncomputable def boundedPartitionStrictFourEquiv (size : ℕ) :
    BoundedPartition 3 size ≃ StrictFourAt size where
  toFun := BoundedPartition.toStrictFourAt
  invFun := StrictFourAt.toBoundedPartition
  left_inv shape := by
    apply Subtype.ext
    funext row
    apply Fin.ext
    fin_cases row <;>
      simp [BoundedPartition.toStrictFourAt,
        StrictFourAt.toBoundedPartition]
  right_inv tuple := by
    cases tuple with
    | mk a b c d hab hbc hcd hsum =>
      apply StrictFourAt.ext <;>
        simp [BoundedPartition.toStrictFourAt,
          StrictFourAt.toBoundedPartition] <;> omega

noncomputable instance strictFourAtFintype (size : ℕ) :
    Fintype (StrictFourAt size) :=
  Fintype.ofEquiv (BoundedPartition 3 size)
    (boundedPartitionStrictFourEquiv size)

theorem boundedFactorialDeterminant_eq_strictFourMatrix
    {size : ℕ} (shape : BoundedPartition 3 size) :
    boundedFactorialDeterminant shape =
      Matrix.det (fourFactorialScalarMatrix
        shape.toStrictFourAt.a shape.toStrictFourAt.b
        shape.toStrictFourAt.c shape.toStrictFourAt.d) := by
  unfold boundedFactorialDeterminant
  apply congrArg Matrix.det
  apply Matrix.ext
  intro row column
  unfold factorialKernelMatrix fourFactorialScalarMatrix
    fourFactorialScalarRow BoundedPartition.shiftedRows
    BoundedPartition.toStrictFourAt
  fin_cases row <;> rfl

theorem strictFourMatrix_eq_boundedFactorialDeterminant
    {size : ℕ} (tuple : StrictFourAt size) :
    Matrix.det (fourFactorialScalarMatrix tuple.a tuple.b tuple.c tuple.d) =
      boundedFactorialDeterminant tuple.toBoundedPartition := by
  rw [boundedFactorialDeterminant_eq_strictFourMatrix]
  have hround := (boundedPartitionStrictFourEquiv size).apply_symm_apply tuple
  change tuple.toBoundedPartition.toStrictFourAt = tuple at hround
  rw [congrArg StrictFourAt.a hround, congrArg StrictFourAt.b hround,
    congrArg StrictFourAt.c hround, congrArg StrictFourAt.d hround]

end FibonacciRibbonKernel
