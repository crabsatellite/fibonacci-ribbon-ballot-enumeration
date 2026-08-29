import FibonacciRibbonKernel.RegevAffineCompactRiemann

namespace FibonacciRibbonKernel

open scoped Classical

structure GeneralShiftTuple (rank size : ℕ) where
  values : Fin (rank + 1) → ℤ
  antitone : Antitone values
  lower : ∀ row, -(generalRegevCenterFloor rank size : ℤ) ≤ values row
  sum_remainder : ∑ row, values row = (size % (rank + 1) : ℕ)

theorem GeneralShiftTuple.ext
    {rank size : ℕ} {left right : GeneralShiftTuple rank size}
    (hvalues : left.values = right.values) : left = right := by
  cases left
  cases right
  simp_all

noncomputable def BoundedPartition.toGeneralShiftTuple
    {rank size : ℕ} (shape : BoundedPartition rank size) :
    GeneralShiftTuple rank size where
  values := fun row =>
    ((shape.1 row).val : ℤ) - generalRegevCenterFloor rank size
  antitone := by
    intro row next hrowNext
    exact sub_le_sub_right (by exact_mod_cast shape.rows_antitone hrowNext) _
  lower := by
    intro row
    omega
  sum_remainder := by
    rw [Finset.sum_sub_distrib]
    have hshape :
        (∑ row : Fin (rank + 1), ((shape.1 row).val : ℤ)) = size := by
      exact_mod_cast shape.2.2
    rw [hshape]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    unfold generalRegevCenterFloor
    have hdivision := Nat.div_add_mod size (rank + 1)
    have hdivisionInt :
        (((rank + 1) * (size / (rank + 1)) +
          size % (rank + 1) : ℕ) : ℤ) = size := by
      exact_mod_cast hdivision
    push_cast at hdivisionInt
    omega

noncomputable def GeneralShiftTuple.rawRows
    {rank size : ℕ} (tuple : GeneralShiftTuple rank size) :
    Fin (rank + 1) → ℕ :=
  fun row => Int.toNat
    ((generalRegevCenterFloor rank size : ℤ) + tuple.values row)

theorem GeneralShiftTuple.rawRows_cast
    {rank size : ℕ} (tuple : GeneralShiftTuple rank size)
    (row : Fin (rank + 1)) :
    (tuple.rawRows row : ℤ) =
      (generalRegevCenterFloor rank size : ℤ) + tuple.values row := by
  rw [GeneralShiftTuple.rawRows, Int.toNat_of_nonneg]
  linarith [tuple.lower row]

theorem GeneralShiftTuple.rawRows_sum
    {rank size : ℕ} (tuple : GeneralShiftTuple rank size) :
    ∑ row, tuple.rawRows row = size := by
  have hsumInt :
      (∑ row, (tuple.rawRows row : ℤ)) = (size : ℤ) := by
    simp_rw [tuple.rawRows_cast]
    rw [Finset.sum_add_distrib, tuple.sum_remainder]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    unfold generalRegevCenterFloor
    have hdivision := Nat.div_add_mod size (rank + 1)
    exact_mod_cast hdivision
  exact_mod_cast hsumInt

noncomputable def GeneralShiftTuple.toBoundedPartition
    {rank size : ℕ} (tuple : GeneralShiftTuple rank size) :
    BoundedPartition rank size := by
  let rows : Fin (rank + 1) → Fin (size + 1) :=
    fun row => ⟨tuple.rawRows row, by
      have hle : tuple.rawRows row ≤ ∑ current, tuple.rawRows current :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ row)
      rw [tuple.rawRows_sum] at hle
      omega⟩
  refine ⟨rows, ?_, ?_⟩
  · intro row
    apply Fin.mk_le_mk.mpr
    apply Int.ofNat_le.mp
    rw [tuple.rawRows_cast, tuple.rawRows_cast]
    simpa [add_comm] using add_le_add_left
      (tuple.antitone row.castSucc_le_succ)
      (generalRegevCenterFloor rank size : ℤ)
  · change ∑ row, tuple.rawRows row = size
    exact tuple.rawRows_sum

theorem BoundedPartition.generalShift_roundtrip
    {rank size : ℕ} (shape : BoundedPartition rank size) :
    shape.toGeneralShiftTuple.toBoundedPartition = shape := by
  apply Subtype.ext
  funext row
  apply Fin.ext
  unfold GeneralShiftTuple.toBoundedPartition
  dsimp only
  change Int.toNat ((generalRegevCenterFloor rank size : ℤ) +
      (((shape.1 row).val : ℤ) - generalRegevCenterFloor rank size)) =
    (shape.1 row).val
  have hnonneg : (0 : ℤ) ≤
      (generalRegevCenterFloor rank size : ℤ) +
        (((shape.1 row).val : ℤ) - generalRegevCenterFloor rank size) := by
    omega
  apply Int.ofNat_injective
  calc
    Int.ofNat (Int.toNat ((generalRegevCenterFloor rank size : ℤ) +
        (((shape.1 row).val : ℤ) - generalRegevCenterFloor rank size))) =
      (generalRegevCenterFloor rank size : ℤ) +
        (((shape.1 row).val : ℤ) - generalRegevCenterFloor rank size) :=
      Int.toNat_of_nonneg hnonneg
    _ = ((shape.1 row).val : ℤ) := by ring
    _ = Int.ofNat (shape.1 row).val := rfl

theorem GeneralShiftTuple.generalShift_roundtrip
    {rank size : ℕ} (tuple : GeneralShiftTuple rank size) :
    tuple.toBoundedPartition.toGeneralShiftTuple = tuple := by
  apply GeneralShiftTuple.ext
  funext row
  unfold BoundedPartition.toGeneralShiftTuple
  change (tuple.rawRows row : ℤ) -
      generalRegevCenterFloor rank size = tuple.values row
  rw [tuple.rawRows_cast]
  ring

noncomputable def boundedPartitionGeneralShiftEquiv (rank size : ℕ) :
    BoundedPartition rank size ≃ GeneralShiftTuple rank size where
  toFun := BoundedPartition.toGeneralShiftTuple
  invFun := GeneralShiftTuple.toBoundedPartition
  left_inv := BoundedPartition.generalShift_roundtrip
  right_inv := GeneralShiftTuple.generalShift_roundtrip

noncomputable def generalExtendInt
    (rank size : ℕ) (coordinates : Fin rank → ℤ) :
    Fin (rank + 1) → ℤ :=
  Fin.lastCases
    ((size % (rank + 1) : ℕ) - ∑ row, coordinates row)
    coordinates

@[simp] theorem generalExtendInt_last
    (rank size : ℕ) (coordinates : Fin rank → ℤ) :
    generalExtendInt rank size coordinates (Fin.last rank) =
      (size % (rank + 1) : ℕ) - ∑ row, coordinates row := by
  simp [generalExtendInt]

@[simp] theorem generalExtendInt_castSucc
    (rank size : ℕ) (coordinates : Fin rank → ℤ) (row : Fin rank) :
    generalExtendInt rank size coordinates row.castSucc = coordinates row := by
  simp [generalExtendInt]

theorem generalExtendInt_sum
    (rank size : ℕ) (coordinates : Fin rank → ℤ) :
    ∑ row, generalExtendInt rank size coordinates row =
      (size % (rank + 1) : ℕ) := by
  rw [Fin.sum_univ_castSucc, generalExtendInt_last]
  simp only [generalExtendInt_castSucc]
  ring

structure GeneralChartTuple (rank size : ℕ) where
  coordinates : Fin rank → ℤ
  antitone : Antitone (generalExtendInt rank size coordinates)
  lower : ∀ row, -(generalRegevCenterFloor rank size : ℤ) ≤
    generalExtendInt rank size coordinates row

theorem GeneralChartTuple.ext
    {rank size : ℕ} {left right : GeneralChartTuple rank size}
    (hcoordinates : left.coordinates = right.coordinates) : left = right := by
  cases left
  cases right
  simp_all

noncomputable def GeneralShiftTuple.toGeneralChart
    {rank size : ℕ} (tuple : GeneralShiftTuple rank size) :
    GeneralChartTuple rank size where
  coordinates := fun row => tuple.values row.castSucc
  antitone := by
    have hvalues : generalExtendInt rank size
        (fun row => tuple.values row.castSucc) = tuple.values := by
      funext row
      cases row using Fin.lastCases with
      | cast row => simp
      | last =>
          rw [generalExtendInt_last]
          have hsum := tuple.sum_remainder
          rw [Fin.sum_univ_castSucc] at hsum
          linarith
    rw [hvalues]
    exact tuple.antitone
  lower := by
    intro row
    have hvalues : generalExtendInt rank size
        (fun row => tuple.values row.castSucc) row = tuple.values row := by
      cases row using Fin.lastCases with
      | cast row => simp
      | last =>
          rw [generalExtendInt_last]
          have hsum := tuple.sum_remainder
          rw [Fin.sum_univ_castSucc] at hsum
          linarith
    rw [hvalues]
    exact tuple.lower row

noncomputable def GeneralChartTuple.toGeneralShift
    {rank size : ℕ} (chart : GeneralChartTuple rank size) :
    GeneralShiftTuple rank size where
  values := generalExtendInt rank size chart.coordinates
  antitone := chart.antitone
  lower := chart.lower
  sum_remainder := generalExtendInt_sum rank size chart.coordinates

theorem GeneralShiftTuple.generalChart_roundtrip
    {rank size : ℕ} (tuple : GeneralShiftTuple rank size) :
    tuple.toGeneralChart.toGeneralShift = tuple := by
  apply GeneralShiftTuple.ext
  funext row
  cases row using Fin.lastCases with
  | cast row => simp [GeneralChartTuple.toGeneralShift,
      GeneralShiftTuple.toGeneralChart]
  | last =>
      change generalExtendInt rank size tuple.toGeneralChart.coordinates
        (Fin.last rank) = tuple.values (Fin.last rank)
      rw [generalExtendInt_last]
      dsimp only [GeneralShiftTuple.toGeneralChart]
      have hsum := tuple.sum_remainder
      rw [Fin.sum_univ_castSucc] at hsum
      linarith

theorem GeneralChartTuple.generalShift_roundtrip
    {rank size : ℕ} (chart : GeneralChartTuple rank size) :
    chart.toGeneralShift.toGeneralChart = chart := by
  apply GeneralChartTuple.ext
  funext row
  simp [GeneralChartTuple.toGeneralShift, GeneralShiftTuple.toGeneralChart]

noncomputable def generalShiftChartEquiv (rank size : ℕ) :
    GeneralShiftTuple rank size ≃ GeneralChartTuple rank size where
  toFun := GeneralShiftTuple.toGeneralChart
  invFun := GeneralChartTuple.toGeneralShift
  left_inv := GeneralShiftTuple.generalChart_roundtrip
  right_inv := GeneralChartTuple.generalShift_roundtrip

noncomputable def boundedPartitionGeneralChartEquiv (rank size : ℕ) :
    BoundedPartition rank size ≃ GeneralChartTuple rank size :=
  (boundedPartitionGeneralShiftEquiv rank size).trans
    (generalShiftChartEquiv rank size)

@[simp] theorem boundedPartitionGeneralChartEquiv_coordinates
    {rank size : ℕ} (shape : BoundedPartition rank size) :
    ((boundedPartitionGeneralChartEquiv rank size) shape).coordinates =
      generalShapeIntegerCoordinates shape := by
  rfl

end FibonacciRibbonKernel
