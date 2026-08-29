import FibonacciRibbonKernel.FrobeniusDeterminant

namespace FibonacciRibbonKernel

open scoped Classical

/-- The staircase weight `0+1+⋯+rank`, written in the same reversed row
coordinates as the Frobenius determinant. -/
def staircaseWeight (rank : ℕ) : ℕ :=
  ∑ row : Fin (rank + 1), row.rev.val

theorem staircaseWeight_formula (rank : ℕ) :
    staircaseWeight rank = (rank + 1) * rank / 2 := by
  unfold staircaseWeight
  calc
    (∑ row : Fin (rank + 1), row.rev.val) =
        ∑ row : Fin (rank + 1), row.val := by
      exact Equiv.sum_comp Fin.revPerm (fun row : Fin (rank + 1) => row.val)
    _ = ∑ value ∈ Finset.range (rank + 1), value := by
      simpa using (Fin.sum_univ_eq_sum_range (n := rank + 1)
        (fun value : ℕ => value))
    _ = (rank + 1) * rank / 2 := by
      rw [Finset.sum_range_id, Nat.add_sub_cancel]

/-- Strict shifted row coordinates for an arbitrary bounded partition.  The
lower-bound field records the literal staircase support needed for the inverse
subtraction; it is redundant mathematically but keeps every Nat subtraction
explicit and lossless. -/
structure StrictShiftedTuple (rank size : ℕ) where
  values : Fin (rank + 1) → ℕ
  strict : ∀ row : Fin rank, values row.succ < values row.castSucc
  staircase_le : ∀ row, row.rev.val ≤ values row
  sum_eq : ∑ row, values row = size + staircaseWeight rank

theorem StrictShiftedTuple.ext
    {rank size : ℕ} {left right : StrictShiftedTuple rank size}
    (hvalues : left.values = right.values) : left = right := by
  cases left
  cases right
  simp_all

noncomputable def BoundedPartition.toStrictShiftedTuple
    {rank size : ℕ} (shape : BoundedPartition rank size) :
    StrictShiftedTuple rank size := by
  let values : Fin (rank + 1) → ℕ :=
    fun row => (shape.1 row).val + row.rev.val
  refine ⟨values, ?_, ?_, ?_⟩
  · intro row
    have hrows : (shape.1 row.succ).val ≤
        (shape.1 row.castSucc).val := by
      simpa using Fin.mk_le_mk.mp (shape.2.1 row)
    have hrev : row.succ.rev.val + 1 = row.castSucc.rev.val := by
      simp [Fin.rev]
      omega
    dsimp only [values]
    omega
  · intro row
    dsimp only [values]
    omega
  · dsimp only [values, staircaseWeight]
    rw [Finset.sum_add_distrib]
    have hshape : ∑ row, (shape.1 row).val = size := shape.2.2
    rw [hshape]

noncomputable def StrictShiftedTuple.toBoundedPartition
    {rank size : ℕ} (tuple : StrictShiftedTuple rank size) :
    BoundedPartition rank size := by
  let rawRows : Fin (rank + 1) → ℕ :=
    fun row => tuple.values row - row.rev.val
  have hsum : ∑ row, rawRows row = size := by
    have hsub := Finset.sum_tsub_distrib Finset.univ
      (fun row _ => tuple.staircase_le row)
    change Finset.sum Finset.univ
      (fun row : Fin (rank + 1) =>
        tuple.values row - (Fin.rev row).val) = size
    rw [hsub, tuple.sum_eq]
    unfold staircaseWeight
    omega
  let rows : Fin (rank + 1) → Fin (size + 1) := fun row =>
    ⟨rawRows row, by
      have hle : rawRows row ≤ ∑ current, rawRows current :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ row)
      rw [hsum] at hle
      omega⟩
  refine ⟨rows, ?_, ?_⟩
  · intro row
    have hstrict := tuple.strict row
    have hrev : row.succ.rev.val + 1 = row.castSucc.rev.val := by
      simp [Fin.rev]
      omega
    have hlower := tuple.staircase_le row.succ
    have hupper := tuple.staircase_le row.castSucc
    change tuple.values row.succ - row.succ.rev.val ≤
      tuple.values row.castSucc - row.castSucc.rev.val
    omega
  · change ∑ row, rawRows row = size
    exact hsum

noncomputable def boundedPartitionStrictShiftedEquiv (rank size : ℕ) :
    BoundedPartition rank size ≃ StrictShiftedTuple rank size where
  toFun := BoundedPartition.toStrictShiftedTuple
  invFun := StrictShiftedTuple.toBoundedPartition
  left_inv shape := by
    apply Subtype.ext
    funext row
    apply Fin.ext
    simp [BoundedPartition.toStrictShiftedTuple,
      StrictShiftedTuple.toBoundedPartition]
  right_inv tuple := by
    apply StrictShiftedTuple.ext
    funext row
    simp only [BoundedPartition.toStrictShiftedTuple,
      StrictShiftedTuple.toBoundedPartition]
    exact Nat.sub_add_cancel (tuple.staircase_le row)

noncomputable instance strictShiftedTupleFintype (rank size : ℕ) :
    Fintype (StrictShiftedTuple rank size) :=
  Fintype.ofEquiv (BoundedPartition rank size)
    (boundedPartitionStrictShiftedEquiv rank size)

theorem BoundedPartition.toStrictShiftedTuple_values
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (row : Fin (rank + 1)) :
    shape.toStrictShiftedTuple.values row =
      (shape.1 row).val + row.rev.val := rfl

theorem StrictShiftedTuple.roundtrip_values
    {rank size : ℕ} (tuple : StrictShiftedTuple rank size) :
    tuple.toBoundedPartition.toStrictShiftedTuple.values = tuple.values := by
  exact congrArg StrictShiftedTuple.values
    ((boundedPartitionStrictShiftedEquiv rank size).apply_symm_apply tuple)

def StrictShiftedTuple.toList
    {rank size : ℕ} (tuple : StrictShiftedTuple rank size) : List ℕ :=
  List.ofFn tuple.values

@[simp] theorem StrictShiftedTuple.toList_length
    {rank size : ℕ} (tuple : StrictShiftedTuple rank size) :
    tuple.toList.length = rank + 1 := by simp [StrictShiftedTuple.toList]

@[simp] theorem StrictShiftedTuple.toList_sum
    {rank size : ℕ} (tuple : StrictShiftedTuple rank size) :
    tuple.toList.sum = size + staircaseWeight rank := by
  rw [StrictShiftedTuple.toList, List.sum_ofFn, tuple.sum_eq]

theorem StrictShiftedTuple.strictAnti
    {rank size : ℕ} (tuple : StrictShiftedTuple rank size) :
    StrictAnti tuple.values :=
  Fin.strictAnti_iff_succ_lt.mpr tuple.strict

theorem StrictShiftedTuple.toList_pairwise
    {rank size : ℕ} (tuple : StrictShiftedTuple rank size) :
    tuple.toList.Pairwise (fun left right => left > right) := by
  rw [StrictShiftedTuple.toList, List.pairwise_ofFn]
  intro left right hleftRight
  exact tuple.strictAnti hleftRight

theorem StrictShiftedTuple.value_le_sum
    {rank size : ℕ} (tuple : StrictShiftedTuple rank size)
    (row : Fin (rank + 1)) : tuple.values row ≤ size + staircaseWeight rank := by
  rw [← tuple.sum_eq]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ row)

theorem pairwise_gt_sublist_reverse_range_general
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
          rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hhead) with hheadEq | hheadLt
          · subst head
            apply List.Sublist.cons_cons
            apply ih tail hpair.2
            intro value hvalue
            exact hpair.1 value hvalue
          · apply List.Sublist.cons
            apply ih (head :: tail) (List.pairwise_cons.mpr hpair)
            intro value hvalue
            rcases List.mem_cons.mp hvalue with rfl | htail
            · exact hheadLt
            · exact (hpair.1 value htail).trans hheadLt

theorem pairwise_gt_reverse_range_general (bound : ℕ) :
    (List.range bound).reverse.Pairwise
      (fun left right : ℕ => left > right) := by
  simpa using (List.pairwise_lt_range (n := bound)).reverse

theorem StrictShiftedTuple.toList_mem_sublistsLen_of_bound
    {rank size bound : ℕ} (tuple : StrictShiftedTuple rank size)
    (hbound : size + staircaseWeight rank < bound) :
    tuple.toList ∈ ((List.range bound).reverse.sublistsLen (rank + 1)) := by
  rw [List.mem_sublistsLen]
  refine ⟨pairwise_gt_sublist_reverse_range_general tuple.toList bound
    tuple.toList_pairwise ?_, tuple.toList_length⟩
  intro value hvalue
  rw [StrictShiftedTuple.toList, List.mem_ofFn] at hvalue
  obtain ⟨row, rfl⟩ := hvalue
  exact (tuple.value_le_sum row).trans_lt hbound

theorem strictAnti_staircase_le
    {dimension : ℕ} (values : Fin (dimension + 1) → ℕ)
    (hstrict : StrictAnti values) (row : Fin (dimension + 1)) :
    row.rev.val ≤ values row := by
  induction row using Fin.reverseInduction with
  | last => simp [Fin.rev]
  | cast row ih =>
      have hlt : values row.succ < values row.castSucc :=
        hstrict Fin.castSucc_lt_succ
      have hrev : row.castSucc.rev.val = row.succ.rev.val + 1 := by
        simp [Fin.rev]
        omega
      omega

end FibonacciRibbonKernel
