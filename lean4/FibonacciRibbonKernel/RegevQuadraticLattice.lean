import FibonacciRibbonKernel.RegevRiemannSum

namespace FibonacciRibbonKernel

open Submodule Pointwise
open scoped Classical Pointwise

def quadraticSize (rank mesh : ℕ) : ℕ :=
  (rank + 1) * mesh ^ 2

/-- Integer deviations from the rectangular center `mesh²` when the total
size is `(rank+1)mesh²`. -/
structure QuadraticShiftTuple (rank mesh : ℕ) where
  values : Fin (rank + 1) → ℤ
  antitone : Antitone values
  lower : ∀ row, -(mesh ^ 2 : ℤ) ≤ values row
  sum_zero : ∑ row, values row = 0

theorem QuadraticShiftTuple.ext
    {rank mesh : ℕ} {left right : QuadraticShiftTuple rank mesh}
    (hvalues : left.values = right.values) : left = right := by
  cases left
  cases right
  simp_all

noncomputable def BoundedPartition.toQuadraticShiftTuple
    {rank mesh : ℕ} (shape : BoundedPartition rank (quadraticSize rank mesh)) :
    QuadraticShiftTuple rank mesh where
  values := fun row => ((shape.1 row).val : ℤ) - mesh ^ 2
  antitone := by
    intro row next hrowNext
    have hrows := shape.rows_antitone hrowNext
    have hrowsInt : ((shape.1 next).val : ℤ) ≤
        ((shape.1 row).val : ℤ) := by exact_mod_cast hrows
    exact sub_le_sub_right hrowsInt _
  lower := by
    intro row
    omega
  sum_zero := by
    rw [Finset.sum_sub_distrib]
    have hshape :
        (∑ row : Fin (rank + 1), ((shape.1 row).val : ℤ)) =
          (quadraticSize rank mesh : ℤ) := by
      exact_mod_cast shape.2.2
    rw [hshape]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, quadraticSize]
    push_cast
    ring

noncomputable def QuadraticShiftTuple.rawRows
    {rank mesh : ℕ} (tuple : QuadraticShiftTuple rank mesh) :
    Fin (rank + 1) → ℕ :=
  fun row => Int.toNat ((mesh ^ 2 : ℤ) + tuple.values row)

theorem QuadraticShiftTuple.rawRows_cast
    {rank mesh : ℕ} (tuple : QuadraticShiftTuple rank mesh)
    (row : Fin (rank + 1)) :
    (tuple.rawRows row : ℤ) = (mesh ^ 2 : ℤ) + tuple.values row := by
  rw [QuadraticShiftTuple.rawRows, Int.toNat_of_nonneg]
  linarith [tuple.lower row]

theorem QuadraticShiftTuple.rawRows_sum
    {rank mesh : ℕ} (tuple : QuadraticShiftTuple rank mesh) :
    ∑ row, tuple.rawRows row = quadraticSize rank mesh := by
  have hsumInt :
      (∑ row, (tuple.rawRows row : ℤ)) =
        (quadraticSize rank mesh : ℤ) := by
    simp_rw [tuple.rawRows_cast]
    rw [Finset.sum_add_distrib, tuple.sum_zero, add_zero]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, quadraticSize]
    push_cast
    ring
  exact_mod_cast hsumInt

noncomputable def QuadraticShiftTuple.toBoundedPartition
    {rank mesh : ℕ} (tuple : QuadraticShiftTuple rank mesh) :
    BoundedPartition rank (quadraticSize rank mesh) := by
  let rows : Fin (rank + 1) → Fin (quadraticSize rank mesh + 1) :=
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
    have hanti := tuple.antitone row.castSucc_le_succ
    omega
  · change ∑ row, tuple.rawRows row = quadraticSize rank mesh
    exact tuple.rawRows_sum

theorem BoundedPartition.quadratic_roundtrip
    {rank mesh : ℕ} (shape : BoundedPartition rank (quadraticSize rank mesh)) :
    shape.toQuadraticShiftTuple.toBoundedPartition = shape := by
  apply Subtype.ext
  funext row
  apply Fin.ext
  unfold QuadraticShiftTuple.toBoundedPartition
  dsimp only
  change Int.toNat ((mesh ^ 2 : ℤ) +
      (((shape.1 row).val : ℤ) - mesh ^ 2)) = (shape.1 row).val
  have hnonneg : (0 : ℤ) ≤
      (mesh ^ 2 : ℤ) + (((shape.1 row).val : ℤ) - mesh ^ 2) := by
    omega
  apply Int.ofNat_injective
  calc
    Int.ofNat (Int.toNat ((mesh ^ 2 : ℤ) +
        (((shape.1 row).val : ℤ) - mesh ^ 2))) =
        (mesh ^ 2 : ℤ) + (((shape.1 row).val : ℤ) - mesh ^ 2) :=
      Int.toNat_of_nonneg hnonneg
    _ = ((shape.1 row).val : ℤ) := by ring
    _ = Int.ofNat (shape.1 row).val := rfl

theorem QuadraticShiftTuple.quadratic_roundtrip
    {rank mesh : ℕ} (tuple : QuadraticShiftTuple rank mesh) :
    tuple.toBoundedPartition.toQuadraticShiftTuple = tuple := by
  apply QuadraticShiftTuple.ext
  funext row
  unfold BoundedPartition.toQuadraticShiftTuple
  change (tuple.rawRows row : ℤ) - mesh ^ 2 = tuple.values row
  rw [tuple.rawRows_cast]
  ring

noncomputable def boundedPartitionQuadraticShiftEquiv (rank mesh : ℕ) :
    BoundedPartition rank (quadraticSize rank mesh) ≃
      QuadraticShiftTuple rank mesh where
  toFun := BoundedPartition.toQuadraticShiftTuple
  invFun := QuadraticShiftTuple.toBoundedPartition
  left_inv := BoundedPartition.quadratic_roundtrip
  right_inv := QuadraticShiftTuple.quadratic_roundtrip

noncomputable def tracelessExtendInt {rank : ℕ}
    (coordinates : Fin rank → ℤ) : Fin (rank + 1) → ℤ :=
  Fin.lastCases (-∑ row, coordinates row) coordinates

@[simp] theorem tracelessExtendInt_last
    {rank : ℕ} (coordinates : Fin rank → ℤ) :
    tracelessExtendInt coordinates (Fin.last rank) =
      -∑ row, coordinates row := by
  simp [tracelessExtendInt]

@[simp] theorem tracelessExtendInt_castSucc
    {rank : ℕ} (coordinates : Fin rank → ℤ) (row : Fin rank) :
    tracelessExtendInt coordinates row.castSucc = coordinates row := by
  simp [tracelessExtendInt]

theorem tracelessExtendInt_sum
    {rank : ℕ} (coordinates : Fin rank → ℤ) :
    ∑ row, tracelessExtendInt coordinates row = 0 := by
  rw [Fin.sum_univ_castSucc, tracelessExtendInt_last]
  simp

structure QuadraticChartTuple (rank mesh : ℕ) where
  coordinates : Fin rank → ℤ
  antitone : Antitone (tracelessExtendInt coordinates)
  lower : ∀ row, -(mesh ^ 2 : ℤ) ≤ tracelessExtendInt coordinates row

theorem QuadraticChartTuple.ext
    {rank mesh : ℕ} {left right : QuadraticChartTuple rank mesh}
    (hcoordinates : left.coordinates = right.coordinates) : left = right := by
  cases left
  cases right
  simp_all

theorem QuadraticShiftTuple.values_eq_tracelessExtendInt
    {rank mesh : ℕ} (tuple : QuadraticShiftTuple rank mesh) :
    tuple.values = tracelessExtendInt
      (fun row : Fin rank => tuple.values row.castSucc) := by
  funext row
  cases row using Fin.lastCases with
  | last =>
      rw [tracelessExtendInt_last]
      have hsum := tuple.sum_zero
      rw [Fin.sum_univ_castSucc] at hsum
      linarith
  | cast row => simp

noncomputable def QuadraticShiftTuple.toChart
    {rank mesh : ℕ} (tuple : QuadraticShiftTuple rank mesh) :
    QuadraticChartTuple rank mesh where
  coordinates := fun row => tuple.values row.castSucc
  antitone := by
    rw [← tuple.values_eq_tracelessExtendInt]
    exact tuple.antitone
  lower := by
    rw [← tuple.values_eq_tracelessExtendInt]
    exact tuple.lower

noncomputable def QuadraticChartTuple.toShift
    {rank mesh : ℕ} (chart : QuadraticChartTuple rank mesh) :
    QuadraticShiftTuple rank mesh where
  values := tracelessExtendInt chart.coordinates
  antitone := chart.antitone
  lower := chart.lower
  sum_zero := tracelessExtendInt_sum chart.coordinates

theorem QuadraticShiftTuple.chart_roundtrip
    {rank mesh : ℕ} (tuple : QuadraticShiftTuple rank mesh) :
    tuple.toChart.toShift = tuple := by
  apply QuadraticShiftTuple.ext
  exact tuple.values_eq_tracelessExtendInt.symm

theorem QuadraticChartTuple.shift_roundtrip
    {rank mesh : ℕ} (chart : QuadraticChartTuple rank mesh) :
    chart.toShift.toChart = chart := by
  apply QuadraticChartTuple.ext
  funext row
  simp [QuadraticShiftTuple.toChart, QuadraticChartTuple.toShift]

noncomputable def quadraticShiftChartEquiv (rank mesh : ℕ) :
    QuadraticShiftTuple rank mesh ≃ QuadraticChartTuple rank mesh where
  toFun := QuadraticShiftTuple.toChart
  invFun := QuadraticChartTuple.toShift
  left_inv := QuadraticShiftTuple.chart_roundtrip
  right_inv := QuadraticChartTuple.shift_roundtrip

noncomputable def boundedPartitionQuadraticChartEquiv (rank mesh : ℕ) :
    BoundedPartition rank (quadraticSize rank mesh) ≃
      QuadraticChartTuple rank mesh :=
  (boundedPartitionQuadraticShiftEquiv rank mesh).trans
    (quadraticShiftChartEquiv rank mesh)

noncomputable def quadraticCenteredPoint
    {rank mesh : ℕ} (chart : QuadraticChartTuple rank mesh) :
    Fin rank → ℝ :=
  fun row => (chart.coordinates row : ℝ) / (mesh : ℝ)

theorem tracelessExtend_quadraticCenteredPoint
    {rank mesh : ℕ} (chart : QuadraticChartTuple rank mesh)
    (_hmesh : 1 ≤ mesh) (row : Fin (rank + 1)) :
    tracelessExtend (quadraticCenteredPoint chart) row =
      (tracelessExtendInt chart.coordinates row : ℝ) / (mesh : ℝ) := by
  cases row using Fin.lastCases with
  | last =>
      rw [tracelessExtend_last, tracelessExtendInt_last]
      unfold quadraticCenteredPoint
      push_cast
      have hsumdivGeneral (indices : Finset (Fin rank)) :
          (∑ row ∈ indices, (chart.coordinates row : ℝ)) / (mesh : ℝ) =
            ∑ row ∈ indices, (chart.coordinates row : ℝ) / (mesh : ℝ) := by
        induction indices using Finset.induction_on with
        | empty => simp
        | @insert row indices hrow ih =>
            simp only [Finset.sum_insert hrow]
            rw [add_div, ih]
      have hsumdiv :
          (∑ row, (chart.coordinates row : ℝ)) / (mesh : ℝ) =
            ∑ row, (chart.coordinates row : ℝ) / (mesh : ℝ) := by
        simpa using hsumdivGeneral Finset.univ
      rw [← hsumdiv]
      ring
  | cast row => simp [quadraticCenteredPoint]

theorem quadraticCenteredPoint_mem_chamber
    {rank mesh : ℕ} (chart : QuadraticChartTuple rank mesh)
    (hmesh : 1 ≤ mesh) :
    quadraticCenteredPoint chart ∈ regevChamber rank := by
  rw [regevChamber_mem_iff]
  intro row next hrowNext
  rw [tracelessExtend_quadraticCenteredPoint chart hmesh,
    tracelessExtend_quadraticCenteredPoint chart hmesh]
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast chart.antitone hrowNext)
    (by positivity : (0 : ℝ) ≤ mesh)

theorem quadratic_local_scale
    (rank mesh : ℕ) (hmesh : 1 ≤ mesh) :
    Real.sqrt (((rank + 1 : ℕ) : ℝ) /
        (quadraticSize rank mesh : ℝ)) =
      ((mesh : ℝ)⁻¹) := by
  have hdimension : (0 : ℝ) < rank + 1 := by positivity
  have hmeshPos : (0 : ℝ) < mesh := by positivity
  have hratio : (((rank + 1 : ℕ) : ℝ) /
        (quadraticSize rank mesh : ℝ)) =
      ((mesh : ℝ)⁻¹) ^ 2 := by
    unfold quadraticSize
    push_cast
    field_simp
  rw [hratio, Real.sqrt_sq]
  positivity

theorem quadratic_center
    (rank mesh : ℕ) :
    (quadraticSize rank mesh : ℝ) / ((rank + 1 : ℕ) : ℝ) =
      (mesh : ℝ) ^ 2 := by
  unfold quadraticSize
  have hdimension : (0 : ℝ) < rank + 1 := by positivity
  push_cast
  field_simp

theorem quadraticCenteredPoint_eq_regevCenteredRow
    {rank mesh : ℕ}
    (shape : BoundedPartition rank (quadraticSize rank mesh))
    (hmesh : 1 ≤ mesh) (row : Fin rank) :
    quadraticCenteredPoint
        ((boundedPartitionQuadraticChartEquiv rank mesh) shape) row =
      regevCenteredRow shape row.castSucc := by
  unfold quadraticCenteredPoint
  change (((shape.1 row.castSucc).val : ℤ) - mesh ^ 2 : ℤ) /
      (mesh : ℝ) = _
  unfold regevCenteredRow
  push_cast
  have hscale : Real.sqrt (((rank : ℝ) + 1) /
      (quadraticSize rank mesh : ℝ)) = (mesh : ℝ)⁻¹ := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      quadratic_local_scale rank mesh hmesh
  have hcenter : (quadraticSize rank mesh : ℝ) /
      ((rank : ℝ) + 1) = (mesh : ℝ) ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      quadratic_center rank mesh
  rw [hscale, hcenter]
  field_simp

theorem quadraticCenteredPoint_eq_regevCenteredRow_full
    {rank mesh : ℕ}
    (shape : BoundedPartition rank (quadraticSize rank mesh))
    (hmesh : 1 ≤ mesh) (row : Fin (rank + 1)) :
    tracelessExtend
        (quadraticCenteredPoint
          ((boundedPartitionQuadraticChartEquiv rank mesh) shape)) row =
      regevCenteredRow shape row := by
  cases row using Fin.lastCases with
  | cast row =>
      rw [tracelessExtend_castSucc]
      exact quadraticCenteredPoint_eq_regevCenteredRow shape hmesh row
  | last =>
      have hleft := tracelessExtend_sum
        (quadraticCenteredPoint
          ((boundedPartitionQuadraticChartEquiv rank mesh) shape))
      have hright := regevCenteredRow_sum_zero shape
      rw [Fin.sum_univ_castSucc] at hleft hright
      have hfirst :
          (∑ index : Fin rank,
              tracelessExtend
                (quadraticCenteredPoint
                  ((boundedPartitionQuadraticChartEquiv rank mesh) shape))
                index.castSucc) =
            ∑ index : Fin rank,
              regevCenteredRow shape index.castSucc := by
        apply Finset.sum_congr rfl
        intro index hindex
        rw [tracelessExtend_castSucc]
        exact quadraticCenteredPoint_eq_regevCenteredRow shape hmesh index
      rw [hfirst] at hleft
      linarith

theorem quadraticSize_tendsto_atTop
    {rank : ℕ} {meshes : ℕ → ℕ}
    (hmeshes : Filter.Tendsto meshes Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun index => quadraticSize rank (meshes index))
      Filter.atTop Filter.atTop := by
  have hsquare : Filter.Tendsto (fun index => meshes index * meshes index)
      Filter.atTop Filter.atTop := hmeshes.atTop_mul_atTop hmeshes
  apply Filter.tendsto_atTop_mono' Filter.atTop
    (Filter.Eventually.of_forall fun index => ?_) hsquare
  unfold quadraticSize
  have hdimension : 1 ≤ rank + 1 := Nat.succ_le_succ (Nat.zero_le rank)
  nlinarith

theorem matsumotoLocalNormalizedTableau_quadratic_tendsto
    {rank : ℕ} (meshes : ℕ → ℕ)
    (shapes : ∀ index,
      BoundedPartition rank (quadraticSize rank (meshes index)))
    (limit : Fin rank → ℝ)
    (hmeshes : Filter.Tendsto meshes Filter.atTop Filter.atTop)
    (hpoints : Filter.Tendsto
      (fun index => quadraticCenteredPoint
        ((boundedPartitionQuadraticChartEquiv rank (meshes index))
          (shapes index))) Filter.atTop (nhds limit)) :
    Filter.Tendsto
      (fun index => matsumotoLocalNormalizedTableau (shapes index))
      Filter.atTop (nhds (regevLocalIntegrand rank limit)) := by
  have heventMesh : ∀ᶠ index in Filter.atTop, 1 ≤ meshes index :=
    hmeshes.eventually (Filter.eventually_ge_atTop 1)
  have hcentered (row : Fin (rank + 1)) :
      Filter.Tendsto (fun index => regevCenteredRow (shapes index) row)
        Filter.atTop (nhds (tracelessExtend limit row)) := by
    have hextend := (continuous_tracelessExtend_apply row).continuousAt.tendsto.comp
      hpoints
    apply hextend.congr'
    filter_upwards [heventMesh] with index hmesh
    simpa only [Function.comp_apply] using
      quadraticCenteredPoint_eq_regevCenteredRow_full
        (shapes index) hmesh row
  have hlocal := matsumotoLocalNormalizedTableau_tendsto
    (fun index => quadraticSize rank (meshes index)) shapes
    (tracelessExtend limit)
    (quadraticSize_tendsto_atTop hmeshes) hcentered
  simpa [regevLocalIntegrand, regevGaussianKernel,
    regevVandermonde] using hlocal

noncomputable def quadraticIntegerPoint
    {rank : ℕ} (mesh : ℕ) (coordinates : Fin rank → ℤ) :
    Fin rank → ℝ :=
  fun row => (coordinates row : ℝ) / (mesh : ℝ)

theorem quadraticIntegerPoint_injective
    {rank mesh : ℕ} (hmesh : 1 ≤ mesh) :
    Function.Injective
      (quadraticIntegerPoint (rank := rank) mesh) := by
  intro left right heq
  funext row
  have hrow := congrFun heq row
  unfold quadraticIntegerPoint at hrow
  have hmeshNe : (mesh : ℝ) ≠ 0 := by positivity
  have hcast : (left row : ℝ) = (right row : ℝ) :=
    (div_left_inj' hmeshNe).mp hrow
  exact_mod_cast hcast

theorem range_quadraticIntegerPoint_eq_scaled_lattice
    (rank mesh : ℕ) (hmesh : 1 ≤ mesh) :
    Set.range (quadraticIntegerPoint (rank := rank) mesh) =
      (mesh : ℝ)⁻¹ • regevIntegerLattice rank := by
  letI : NeZero mesh := ⟨by omega⟩
  unfold regevIntegerLattice
  ext point
  constructor
  · rintro ⟨coordinates, rfl⟩
    apply (BoxIntegral.unitPartition.mem_smul_span_iff
      (ι := Fin rank) (n := mesh)).2
    intro row
    refine ⟨coordinates row, ?_⟩
    unfold quadraticIntegerPoint
    field_simp
    rfl
  · intro hpoint
    have hpointCoordinates :=
      (BoxIntegral.unitPartition.mem_smul_span_iff
        (ι := Fin rank) (n := mesh)).1 hpoint
    choose coordinates hcoordinates using hpointCoordinates
    refine ⟨coordinates, ?_⟩
    funext row
    unfold quadraticIntegerPoint
    have hmeshNe : (mesh : ℝ) ≠ 0 := by positivity
    apply (div_eq_iff hmeshNe).2
    rw [mul_comm]
    exact hcoordinates row

theorem tracelessExtend_quadraticIntegerPoint
    {rank mesh : ℕ} (coordinates : Fin rank → ℤ)
    (_hmesh : 1 ≤ mesh) (row : Fin (rank + 1)) :
    tracelessExtend (quadraticIntegerPoint mesh coordinates) row =
      (tracelessExtendInt coordinates row : ℝ) / (mesh : ℝ) := by
  cases row using Fin.lastCases with
  | last =>
      rw [tracelessExtend_last, tracelessExtendInt_last]
      unfold quadraticIntegerPoint
      push_cast
      have hsumdivGeneral (indices : Finset (Fin rank)) :
          (∑ row ∈ indices, (coordinates row : ℝ)) / (mesh : ℝ) =
            ∑ row ∈ indices, (coordinates row : ℝ) / (mesh : ℝ) := by
        induction indices using Finset.induction_on with
        | empty => simp
        | @insert row indices hrow ih =>
            simp only [Finset.sum_insert hrow]
            rw [add_div, ih]
      have hsumdiv :
          (∑ row, (coordinates row : ℝ)) / (mesh : ℝ) =
            ∑ row, (coordinates row : ℝ) / (mesh : ℝ) := by
        simpa using hsumdivGeneral Finset.univ
      rw [← hsumdiv]
      ring
  | cast row => simp [quadraticIntegerPoint]

def quadraticFeasibleLatticeSet (rank mesh : ℕ) :
    Set (Fin rank → ℝ) :=
  regevChamber rank ∩
    ((mesh : ℝ)⁻¹ • regevIntegerLattice rank) ∩
    {point | ∀ row : Fin (rank + 1),
      -(mesh : ℝ) ≤ tracelessExtend point row}

noncomputable def quadraticChartToFeasiblePoint
    {rank mesh : ℕ} (hmesh : 1 ≤ mesh)
    (chart : QuadraticChartTuple rank mesh) :
    ↑(quadraticFeasibleLatticeSet rank mesh) := by
  refine ⟨quadraticCenteredPoint chart, ?_⟩
  refine ⟨⟨quadraticCenteredPoint_mem_chamber chart hmesh, ?_⟩, ?_⟩
  · rw [← range_quadraticIntegerPoint_eq_scaled_lattice rank mesh hmesh]
    exact ⟨chart.coordinates, rfl⟩
  · intro row
    rw [tracelessExtend_quadraticCenteredPoint chart hmesh]
    have hmeshPos : (0 : ℝ) < mesh := by positivity
    apply (le_div_iff₀ hmeshPos).2
    have hlower : (-(mesh ^ 2 : ℤ) : ℝ) ≤
        (tracelessExtendInt chart.coordinates row : ℤ) := by
      exact_mod_cast chart.lower row
    push_cast at hlower ⊢
    nlinarith

theorem quadraticChartToFeasiblePoint_injective
    {rank mesh : ℕ} (hmesh : 1 ≤ mesh) :
    Function.Injective (quadraticChartToFeasiblePoint
      (rank := rank) (mesh := mesh) hmesh) := by
  intro left right heq
  apply QuadraticChartTuple.ext
  apply quadraticIntegerPoint_injective hmesh
  exact congrArg Subtype.val heq

theorem quadraticChartToFeasiblePoint_surjective
    {rank mesh : ℕ} (hmesh : 1 ≤ mesh) :
    Function.Surjective (quadraticChartToFeasiblePoint
      (rank := rank) (mesh := mesh) hmesh) := by
  intro point
  have hlattice : point.1 ∈
      (mesh : ℝ)⁻¹ • regevIntegerLattice rank := point.2.1.2
  have hlatticeRange : point.1 ∈
      Set.range (quadraticIntegerPoint (rank := rank) mesh) := by
    rw [range_quadraticIntegerPoint_eq_scaled_lattice rank mesh hmesh]
    exact hlattice
  obtain ⟨coordinates, hcoordinates⟩ := hlatticeRange
  let chart : QuadraticChartTuple rank mesh :=
    { coordinates := coordinates
      antitone := by
        intro row next hrowNext
        have hchamber := (regevChamber_mem_iff point.1).mp point.2.1.1
        have hineq := hchamber row next hrowNext
        rw [← hcoordinates,
          tracelessExtend_quadraticIntegerPoint coordinates hmesh,
          tracelessExtend_quadraticIntegerPoint coordinates hmesh] at hineq
        have hmeshPos : (0 : ℝ) < mesh := by positivity
        have hcast : (tracelessExtendInt coordinates next : ℝ) ≤
            (tracelessExtendInt coordinates row : ℝ) := by
          exact (div_le_div_iff_of_pos_right hmeshPos).mp hineq
        exact_mod_cast hcast
      lower := by
        intro row
        have hfeasible := point.2.2 row
        rw [← hcoordinates,
          tracelessExtend_quadraticIntegerPoint coordinates hmesh] at hfeasible
        have hmeshPos : (0 : ℝ) < mesh := by positivity
        have hcast : (-(mesh ^ 2 : ℤ) : ℝ) ≤
            (tracelessExtendInt coordinates row : ℤ) := by
          have hmul : (-(mesh : ℝ)) * (mesh : ℝ) ≤
              (tracelessExtendInt coordinates row : ℝ) :=
            (le_div_iff₀ hmeshPos).mp hfeasible
          push_cast
          nlinarith
        exact_mod_cast hcast }
  refine ⟨chart, ?_⟩
  apply Subtype.ext
  exact hcoordinates

noncomputable def quadraticChartFeasiblePointEquiv
    (rank mesh : ℕ) (hmesh : 1 ≤ mesh) :
    QuadraticChartTuple rank mesh ≃
      ↑(quadraticFeasibleLatticeSet rank mesh) :=
  Equiv.ofBijective (quadraticChartToFeasiblePoint
      (rank := rank) (mesh := mesh) hmesh)
    ⟨quadraticChartToFeasiblePoint_injective
        (rank := rank) (mesh := mesh) hmesh,
      quadraticChartToFeasiblePoint_surjective
        (rank := rank) (mesh := mesh) hmesh⟩

noncomputable def boundedPartitionQuadraticFeasiblePointEquiv
    (rank mesh : ℕ) (hmesh : 1 ≤ mesh) :
    BoundedPartition rank (quadraticSize rank mesh) ≃
      ↑(quadraticFeasibleLatticeSet rank mesh) :=
  (boundedPartitionQuadraticChartEquiv rank mesh).trans
    (quadraticChartFeasiblePointEquiv rank mesh hmesh)

theorem abs_tracelessExtend_le_dimension_mul_norm
    {rank : ℕ} (coordinates : Fin rank → ℝ)
    (row : Fin (rank + 1)) :
    |tracelessExtend coordinates row| ≤
      ((rank + 1 : ℕ) : ℝ) * ‖coordinates‖ := by
  have happly (index : Fin rank) :
      |coordinates index| ≤ ‖coordinates‖ := by
    rw [← Real.norm_eq_abs]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg coordinates)).mp le_rfl index
  cases row using Fin.lastCases with
  | last =>
      rw [tracelessExtend_last, abs_neg]
      calc
        |∑ index, coordinates index| ≤
            ∑ index, |coordinates index| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _index : Fin rank, ‖coordinates‖ := by
          apply Finset.sum_le_sum
          intro index hindex
          exact happly index
        _ = (rank : ℝ) * ‖coordinates‖ := by simp
        _ ≤ ((rank + 1 : ℕ) : ℝ) * ‖coordinates‖ := by
          gcongr
          omega
  | cast index =>
      rw [tracelessExtend_castSucc]
      calc
        |coordinates index| ≤ ‖coordinates‖ := happly index
        _ ≤ ((rank + 1 : ℕ) : ℝ) * ‖coordinates‖ := by
          have hdimension : (1 : ℝ) ≤ (rank + 1 : ℕ) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le rank)
          nlinarith [norm_nonneg coordinates]

theorem truncated_chamber_subset_feasible
    (rank mesh : ℕ) (radius : ℝ)
    (_hradius : 0 ≤ radius)
    (hmeshRadius : ((rank + 1 : ℕ) : ℝ) * radius ≤ mesh) :
    regevTruncatedChamber rank radius ⊆
      {point | ∀ row : Fin (rank + 1),
        -(mesh : ℝ) ≤ tracelessExtend point row} := by
  intro point hpoint row
  have hnorm : ‖point‖ ≤ radius := by
    exact mem_closedBall_zero_iff.mp hpoint.2
  have habs := abs_tracelessExtend_le_dimension_mul_norm point row
  have hbound : |tracelessExtend point row| ≤ (mesh : ℝ) := by
    exact habs.trans <| (mul_le_mul_of_nonneg_left hnorm (by positivity)).trans
      hmeshRadius
  exact (neg_le_neg hbound).trans
    (neg_abs_le (tracelessExtend point row))

theorem truncated_scaled_lattice_eq_feasible_truncated
    (rank mesh : ℕ) (radius : ℝ)
    (hradius : 0 ≤ radius)
    (hmeshRadius : ((rank + 1 : ℕ) : ℝ) * radius ≤ mesh) :
    regevTruncatedChamber rank radius ∩
        ((mesh : ℝ)⁻¹ • regevIntegerLattice rank) =
      quadraticFeasibleLatticeSet rank mesh ∩
        Metric.closedBall 0 radius := by
  ext point
  constructor
  · intro hpoint
    refine ⟨⟨⟨hpoint.1.1, hpoint.2⟩, ?_⟩, hpoint.1.2⟩
    exact truncated_chamber_subset_feasible rank mesh radius
      hradius hmeshRadius hpoint.1
  · intro hpoint
    exact ⟨⟨hpoint.1.1.1, hpoint.2⟩, hpoint.1.1.2⟩

noncomputable def boundedPartitionQuadraticTruncatedEquiv
    (rank mesh : ℕ) (hmesh : 1 ≤ mesh) (radius : ℝ) :
    {shape : BoundedPartition rank (quadraticSize rank mesh) //
      ((boundedPartitionQuadraticFeasiblePointEquiv rank mesh hmesh) shape).1 ∈
        Metric.closedBall 0 radius} ≃
      {point : ↑(quadraticFeasibleLatticeSet rank mesh) //
        point.1 ∈ Metric.closedBall 0 radius} :=
  Equiv.subtypeEquivOfSubtype
    (p := fun point : ↑(quadraticFeasibleLatticeSet rank mesh) =>
      point.1 ∈ Metric.closedBall 0 radius)
    (boundedPartitionQuadraticFeasiblePointEquiv rank mesh hmesh)

noncomputable def boundedPartitionQuadraticRiemannPointEquiv
    (rank mesh : ℕ) (hmesh : 1 ≤ mesh) (radius : ℝ)
    (hradius : 0 ≤ radius)
    (hmeshRadius : ((rank + 1 : ℕ) : ℝ) * radius ≤ mesh) :
    {shape : BoundedPartition rank (quadraticSize rank mesh) //
      ((boundedPartitionQuadraticFeasiblePointEquiv rank mesh hmesh) shape).1 ∈
        Metric.closedBall 0 radius} ≃
      ↑(regevTruncatedChamber rank radius ∩
        ((mesh : ℝ)⁻¹ • regevIntegerLattice rank)) :=
  (boundedPartitionQuadraticTruncatedEquiv rank mesh hmesh radius).trans <|
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun point : Fin rank → ℝ =>
        point ∈ quadraticFeasibleLatticeSet rank mesh)
      (fun point : Fin rank → ℝ =>
        point ∈ Metric.closedBall 0 radius)).trans <|
      Equiv.setCongr
        (truncated_scaled_lattice_eq_feasible_truncated
          rank mesh radius hradius hmeshRadius).symm

end FibonacciRibbonKernel
