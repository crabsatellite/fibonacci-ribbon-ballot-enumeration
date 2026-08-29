import FibonacciRibbonKernel.FiveFactorialRows

namespace FibonacciRibbonKernel

open scoped Classical

theorem exists_five_entries_of_length_eq_five {A : Type*}
    (values : List A) (hlength : values.length = 5) :
    ∃ a b c d e, values = [a, b, c, d, e] := by
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
                      have htail : tail = [] := by simpa using hlength
                      subst tail
                      exact ⟨a, b, c, d, e, rfl⟩

theorem pairwise_gt_sublist_reverse_range
    (values : List ℕ) (bound : ℕ)
    (hpair : values.Pairwise (fun left right => left > right))
    (hbound : ∀ value ∈ values, value < bound) :
    List.Sublist values (List.range bound).reverse := by
  induction bound generalizing values with
  | zero =>
      have hempty : values = [] := by
        cases values with
        | nil => rfl
        | cons head tail =>
            have := hbound head (by simp)
            omega
      subst values
      exact List.Sublist.slnil
  | succ bound ih =>
      rw [List.range_succ, List.reverse_append]
      simp only [List.reverse_singleton, List.singleton_append]
      cases values with
      | nil => exact List.nil_sublist _
      | cons head tail =>
          have hhead : head < bound + 1 := hbound head (by simp)
          rw [List.pairwise_cons] at hpair
          have htailPair : tail.Pairwise (fun left right => left > right) := by
            exact hpair.2
          have hheadTail : ∀ value ∈ tail, head > value := by
            exact hpair.1
          rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hhead) with hheadEq | hheadLt
          · subst head
            apply List.Sublist.cons_cons
            apply ih tail htailPair
            intro value hvalue
            exact hheadTail value hvalue
          · apply List.Sublist.cons
            apply ih (head :: tail)
            · rw [List.pairwise_cons]
              exact hpair
            · intro value hvalue
              rcases List.mem_cons.mp hvalue with rfl | htail
              · exact hheadLt
              · exact (hheadTail value htail).trans hheadLt

theorem pairwise_gt_reverse_range (bound : ℕ) :
    (List.range bound).reverse.Pairwise
      (fun left right : ℕ => left > right) := by
  simpa using (List.pairwise_lt_range (n := bound)).reverse

structure StrictFiveAt (size : ℕ) where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  e : ℕ
  ab : b < a
  bc : c < b
  cd : d < c
  de : e < d
  sum_eq : a + b + c + d + e = size + 10

theorem StrictFiveAt.ext {size : ℕ} {left right : StrictFiveAt size}
    (ha : left.a = right.a) (hb : left.b = right.b)
    (hc : left.c = right.c) (hd : left.d = right.d)
    (he : left.e = right.e) : left = right := by
  cases left
  cases right
  simp_all

def StrictFiveAt.values {size : ℕ} (tuple : StrictFiveAt size) : Fin 5 → ℕ :=
  fiveVector tuple.a tuple.b tuple.c tuple.d tuple.e

def StrictFiveAt.toList {size : ℕ} (tuple : StrictFiveAt size) : List ℕ :=
  [tuple.a, tuple.b, tuple.c, tuple.d, tuple.e]

@[simp] theorem StrictFiveAt.toList_length
    {size : ℕ} (tuple : StrictFiveAt size) : tuple.toList.length = 5 := rfl

@[simp] theorem StrictFiveAt.toList_sum
    {size : ℕ} (tuple : StrictFiveAt size) :
    tuple.toList.sum = size + 10 := by
  simpa only [StrictFiveAt.toList, List.sum_cons, List.sum_nil, add_zero,
    add_assoc] using tuple.sum_eq

theorem StrictFiveAt.toList_pairwise
    {size : ℕ} (tuple : StrictFiveAt size) :
    tuple.toList.Pairwise (fun left right => left > right) := by
  have hab := tuple.ab
  have hbc := tuple.bc
  have hcd := tuple.cd
  have hde := tuple.de
  simp [StrictFiveAt.toList]
  omega

theorem StrictFiveAt.value_lower_bounds
    {size : ℕ} (tuple : StrictFiveAt size) :
    4 ≤ tuple.a ∧ 3 ≤ tuple.b ∧ 2 ≤ tuple.c ∧ 1 ≤ tuple.d := by
  have hab := tuple.ab
  have hbc := tuple.bc
  have hcd := tuple.cd
  have hde := tuple.de
  omega

theorem StrictFiveAt.toList_mem_sublistsLen
    {size : ℕ} (tuple : StrictFiveAt size) :
    tuple.toList ∈
      ((List.range (size + 5)).reverse.sublistsLen 5) := by
  rw [List.mem_sublistsLen]
  refine ⟨pairwise_gt_sublist_reverse_range tuple.toList (size + 5)
    tuple.toList_pairwise ?_, tuple.toList_length⟩
  intro value hvalue
  have hab := tuple.ab
  have hbc := tuple.bc
  have hcd := tuple.cd
  have hde := tuple.de
  have hsum := tuple.sum_eq
  simp [StrictFiveAt.toList] at hvalue
  rcases hvalue with rfl | rfl | rfl | rfl | rfl <;> omega

theorem StrictFiveAt.toList_mem_sublistsLen_of_bound
    {size bound : ℕ} (tuple : StrictFiveAt size)
    (hbound : size + 5 ≤ bound) :
    tuple.toList ∈ ((List.range bound).reverse.sublistsLen 5) := by
  rw [List.mem_sublistsLen]
  refine ⟨pairwise_gt_sublist_reverse_range tuple.toList bound
    tuple.toList_pairwise ?_, tuple.toList_length⟩
  intro value hvalue
  have hab := tuple.ab
  have hbc := tuple.bc
  have hcd := tuple.cd
  have hde := tuple.de
  have hsum := tuple.sum_eq
  simp [StrictFiveAt.toList] at hvalue
  rcases hvalue with rfl | rfl | rfl | rfl | rfl <;> omega

noncomputable def BoundedPartition.toStrictFiveAt
    {size : ℕ} (shape : BoundedPartition 4 size) : StrictFiveAt size := by
  let a := (shape.1 0).val + 4
  let b := (shape.1 1).val + 3
  let c := (shape.1 2).val + 2
  let d := (shape.1 3).val + 1
  let e := (shape.1 4).val
  refine ⟨a, b, c, d, e, ?_, ?_, ?_, ?_, ?_⟩
  · have h : (shape.1 (1 : Fin 5)).val ≤
        (shape.1 (0 : Fin 5)).val := by
      simpa using Fin.mk_le_mk.mp (shape.2.1 (0 : Fin 4))
    omega
  · have h : (shape.1 (2 : Fin 5)).val ≤
        (shape.1 (1 : Fin 5)).val := by
      simpa using Fin.mk_le_mk.mp (shape.2.1 (1 : Fin 4))
    omega
  · have h : (shape.1 (3 : Fin 5)).val ≤
        (shape.1 (2 : Fin 5)).val := by
      simpa using Fin.mk_le_mk.mp (shape.2.1 (2 : Fin 4))
    omega
  · have h : (shape.1 (4 : Fin 5)).val ≤
        (shape.1 (3 : Fin 5)).val := by
      simpa using Fin.mk_le_mk.mp (shape.2.1 (3 : Fin 4))
    omega
  · have hsum :
        (shape.1 (0 : Fin 5)).val + (shape.1 (1 : Fin 5)).val +
          (shape.1 (2 : Fin 5)).val + (shape.1 (3 : Fin 5)).val +
          (shape.1 (4 : Fin 5)).val = size := by
      have hsumAll := shape.2.2
      rw [sum_fin_five] at hsumAll
      exact hsumAll
    omega

noncomputable def StrictFiveAt.toBoundedPartition
    {size : ℕ} (tuple : StrictFiveAt size) : BoundedPartition 4 size := by
  have hlower := tuple.value_lower_bounds
  let rawRows : Fin 5 → ℕ :=
    fiveVector (tuple.a - 4) (tuple.b - 3) (tuple.c - 2)
      (tuple.d - 1) tuple.e
  have hsum : ∑ row, rawRows row = size := by
    rw [sum_fin_five]
    simp only [rawRows, fiveVector_zero, fiveVector_one, fiveVector_two,
      fiveVector_three, fiveVector_four]
    have hab := tuple.ab
    have hbc := tuple.bc
    have hcd := tuple.cd
    have hde := tuple.de
    have htotal := tuple.sum_eq
    omega
  let rows : Fin 5 → Fin (size + 1) := fun row =>
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
  refine ⟨rows, ?_, ?_⟩
  · intro index
    fin_cases index
    · change tuple.b - 3 ≤ tuple.a - 4
      omega
    · change tuple.c - 2 ≤ tuple.b - 3
      omega
    · change tuple.d - 1 ≤ tuple.c - 2
      omega
    · change tuple.e ≤ tuple.d - 1
      omega
  · change ∑ row, rawRows row = size
    exact hsum

noncomputable def boundedPartitionStrictFiveEquiv (size : ℕ) :
    BoundedPartition 4 size ≃ StrictFiveAt size where
  toFun := BoundedPartition.toStrictFiveAt
  invFun := StrictFiveAt.toBoundedPartition
  left_inv shape := by
    apply Subtype.ext
    funext row
    apply Fin.ext
    fin_cases row <;>
      simp [BoundedPartition.toStrictFiveAt,
        StrictFiveAt.toBoundedPartition]
  right_inv tuple := by
    cases tuple with
    | mk a b c d e hab hbc hcd hde hsum =>
      apply StrictFiveAt.ext <;>
        simp [BoundedPartition.toStrictFiveAt,
          StrictFiveAt.toBoundedPartition] <;> omega

noncomputable instance strictFiveAtFintype (size : ℕ) :
    Fintype (StrictFiveAt size) :=
  Fintype.ofEquiv (BoundedPartition 4 size)
    (boundedPartitionStrictFiveEquiv size)

theorem boundedFactorialDeterminant_eq_strictFiveMatrix
    {size : ℕ} (shape : BoundedPartition 4 size) :
    boundedFactorialDeterminant shape =
      Matrix.det
        (fiveFactorialScalarMatrix
          shape.toStrictFiveAt.a shape.toStrictFiveAt.b
          shape.toStrictFiveAt.c shape.toStrictFiveAt.d
          shape.toStrictFiveAt.e) := by
  unfold boundedFactorialDeterminant
  apply congrArg Matrix.det
  apply Matrix.ext
  intro row column
  unfold factorialKernelMatrix fiveFactorialScalarMatrix
    fiveFactorialScalarRow BoundedPartition.shiftedRows
    BoundedPartition.toStrictFiveAt
  fin_cases row <;> rfl

theorem strictFiveMatrix_eq_boundedFactorialDeterminant
    {size : ℕ} (tuple : StrictFiveAt size) :
    Matrix.det
        (fiveFactorialScalarMatrix tuple.a tuple.b tuple.c tuple.d tuple.e) =
      boundedFactorialDeterminant tuple.toBoundedPartition := by
  rw [boundedFactorialDeterminant_eq_strictFiveMatrix]
  have hround := (boundedPartitionStrictFiveEquiv size).apply_symm_apply tuple
  change tuple.toBoundedPartition.toStrictFiveAt = tuple at hround
  have ha := congrArg StrictFiveAt.a hround
  have hb := congrArg StrictFiveAt.b hround
  have hc := congrArg StrictFiveAt.c hround
  have hd := congrArg StrictFiveAt.d hround
  have he := congrArg StrictFiveAt.e hround
  rw [ha, hb, hc, hd, he]

end FibonacciRibbonKernel
