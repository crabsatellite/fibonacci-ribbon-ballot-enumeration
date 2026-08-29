import FibonacciRibbonKernel.RegevGeneralShapeTail

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set Submodule Pointwise
open scoped Classical Topology Pointwise

noncomputable def quadraticIntegerScaledLatticeEquiv
    (rank mesh : ℕ) (hmesh : 1 ≤ mesh) :
    (Fin rank → ℤ) ≃
      ↑((mesh : ℝ)⁻¹ • (regevIntegerLattice rank : Set (Fin rank → ℝ))) := by
  let map : (Fin rank → ℤ) →
      ↑((mesh : ℝ)⁻¹ • (regevIntegerLattice rank : Set (Fin rank → ℝ))) :=
    fun coordinates => ⟨quadraticIntegerPoint mesh coordinates, by
      have hrange : quadraticIntegerPoint mesh coordinates ∈ Set.range
          (quadraticIntegerPoint (rank := rank) mesh) := ⟨coordinates, rfl⟩
      exact (Set.ext_iff.mp
        (range_quadraticIntegerPoint_eq_scaled_lattice rank mesh hmesh)
        (quadraticIntegerPoint mesh coordinates)).mp hrange⟩
  apply Equiv.ofBijective map
  constructor
  · intro first second heq
    apply quadraticIntegerPoint_injective hmesh
    exact congrArg Subtype.val heq
  · intro point
    have hmem : point.1 ∈ Set.range
        (quadraticIntegerPoint (rank := rank) mesh) := by
      exact (Set.ext_iff.mp
        (range_quadraticIntegerPoint_eq_scaled_lattice rank mesh hmesh)
        point.1).mpr point.2
    obtain ⟨coordinates, hcoordinates⟩ := hmem
    exact ⟨coordinates, Subtype.ext hcoordinates⟩

def IntegerBallIndex (rank mesh : ℕ) (radius : ℝ) :=
  {coordinates : Fin rank → ℤ //
    quadraticIntegerPoint mesh coordinates ∈ Metric.closedBall 0 radius}

noncomputable def integerBallPointEquiv
    (rank mesh : ℕ) (hmesh : 1 ≤ mesh) (radius : ℝ) :
    IntegerBallIndex rank mesh radius ≃
      ↑(Metric.closedBall (0 : Fin rank → ℝ) radius ∩
        ((mesh : ℝ)⁻¹ • (regevIntegerLattice rank : Set (Fin rank → ℝ)))) := by
  let equivalence := quadraticIntegerScaledLatticeEquiv rank mesh hmesh
  exact {
    toFun := fun coordinates =>
      ⟨quadraticIntegerPoint mesh coordinates.1,
        coordinates.2, (equivalence coordinates.1).2⟩
    invFun := fun point =>
      ⟨equivalence.symm ⟨point.1, point.2.2⟩, by
        have happly := congrArg Subtype.val
          (equivalence.apply_symm_apply ⟨point.1, point.2.2⟩)
        rw [show quadraticIntegerPoint mesh
          (equivalence.symm ⟨point.1, point.2.2⟩) = point.1 by exact happly]
        exact point.2.1⟩
    left_inv := fun coordinates => Subtype.ext (by
      let latticePoint :
          ↑((mesh : ℝ)⁻¹ •
            (regevIntegerLattice rank : Set (Fin rank → ℝ))) :=
        ⟨quadraticIntegerPoint mesh coordinates.1,
          (equivalence coordinates.1).2⟩
      have hlattice : latticePoint = equivalence coordinates.1 :=
        Subtype.ext rfl
      change equivalence.symm latticePoint = coordinates.1
      rw [hlattice, equivalence.symm_apply_apply])
    right_inv := fun point => Subtype.ext (by
      change quadraticIntegerPoint mesh
        (equivalence.symm ⟨point.1, point.2.2⟩) = point.1
      exact congrArg Subtype.val
        (equivalence.apply_symm_apply ⟨point.1, point.2.2⟩))
  }

@[reducible] noncomputable def integerBallIndexFintype
    (rank mesh : ℕ) (hmesh : 1 ≤ mesh) (radius : ℝ) :
    Fintype (IntegerBallIndex rank mesh radius) := by
  letI : NeZero mesh := ⟨by omega⟩
  have hfinite : Set.Finite
      (Metric.closedBall (0 : Fin rank → ℝ) radius ∩
        ((mesh : ℝ)⁻¹ •
          (regevIntegerLattice rank : Set (Fin rank → ℝ)))) := by
    unfold regevIntegerLattice
    rw [← coe_pointwise_smul,
      ZSpan.smul _ (inv_ne_zero (NeZero.ne _))]
    exact ZSpan.setFinite_inter _ Metric.isBounded_closedBall
  letI : Fintype ↑(Metric.closedBall (0 : Fin rank → ℝ) radius ∩
      ((mesh : ℝ)⁻¹ •
        (regevIntegerLattice rank : Set (Fin rank → ℝ)))) :=
    hfinite.fintype
  exact Fintype.ofEquiv _
    (integerBallPointEquiv rank mesh hmesh radius).symm

theorem closedBall_null_frontier
    (rank : ℕ) (radius : ℝ) :
    volume (frontier (Metric.closedBall
      (0 : Fin rank → ℝ) radius)) = 0 :=
  (convex_closedBall (0 : Fin rank → ℝ) radius).addHaar_frontier volume

/-- The existing unit-partition theorem, reindexed from scaled-lattice points
to literal integer coordinate tuples. -/
theorem integer_ball_riemann_sum_tendsto
    (rank : ℕ) (radius : ℝ) (function : (Fin rank → ℝ) → ℝ)
    (hfunction : Continuous function) :
    Tendsto
      (fun mesh : ℕ =>
        (∑' coordinates : IntegerBallIndex rank mesh radius,
          function (quadraticIntegerPoint mesh coordinates.1)) /
            mesh ^ rank)
      atTop
      (nhds (∫ coordinates in Metric.closedBall 0 radius,
        function coordinates)) := by
  have hriemann := tendsto_tsum_div_pow_atTop_integral
    (Metric.closedBall (0 : Fin rank → ℝ) radius)
    function hfunction Metric.isBounded_closedBall
    Metric.isClosed_closedBall.measurableSet
    (closedBall_null_frontier rank radius)
  apply hriemann.congr'
  filter_upwards [eventually_ge_atTop 1] with mesh hmesh
  simp only [Fintype.card_fin]
  congr 1
  exact ((integerBallPointEquiv rank mesh hmesh radius).tsum_eq
    (fun point => function point.1)).symm

theorem integer_full_sum_eq_ball_sum
    (rank mesh : ℕ) (radius : ℝ)
    (function : (Fin rank → ℝ) → ℝ)
    (hsupport : ∀ coordinates,
      function coordinates ≠ 0 → coordinates ∈ Metric.closedBall 0 radius) :
    (∑' coordinates : Fin rank → ℤ,
      function (quadraticIntegerPoint mesh coordinates)) =
      ∑' coordinates : IntegerBallIndex rank mesh radius,
        function (quadraticIntegerPoint mesh coordinates.1) := by
  symm
  unfold IntegerBallIndex
  refine tsum_subtype_eq_of_support_subset
    (f := fun coordinates : Fin rank → ℤ =>
      function (quadraticIntegerPoint mesh coordinates))
    (s := {coordinates |
      quadraticIntegerPoint mesh coordinates ∈ Metric.closedBall 0 radius}) ?_
  intro coordinates hcoordinates
  exact hsupport _ hcoordinates

theorem integral_eq_setIntegral_closedBall
    (rank : ℕ) (radius : ℝ)
    (function : (Fin rank → ℝ) → ℝ)
    (hsupport : ∀ coordinates,
      coordinates ∉ Metric.closedBall 0 radius → function coordinates = 0) :
    (∫ coordinates : Fin rank → ℝ, function coordinates) =
      ∫ coordinates in Metric.closedBall 0 radius, function coordinates := by
  have hindicator : function =
      (Metric.closedBall (0 : Fin rank → ℝ) radius).indicator function := by
    funext coordinates
    by_cases hcoordinates : coordinates ∈ Metric.closedBall 0 radius
    · rw [Set.indicator_of_mem hcoordinates]
    · rw [Set.indicator_of_notMem hcoordinates, hsupport coordinates hcoordinates]
  calc
    (∫ coordinates : Fin rank → ℝ, function coordinates) =
        ∫ coordinates : Fin rank → ℝ,
          (Metric.closedBall (0 : Fin rank → ℝ) radius).indicator
            function coordinates := by rw [← hindicator]
    _ = ∫ coordinates in Metric.closedBall 0 radius,
        function coordinates :=
      integral_indicator Metric.isClosed_closedBall.measurableSet

/-- Whole-space integer-grid Riemann convergence for a continuous function
with support in a fixed closed ball. -/
theorem integer_full_riemann_sum_tendsto
    (rank : ℕ) (radius : ℝ) (function : (Fin rank → ℝ) → ℝ)
    (hfunction : Continuous function)
    (hsupport : ∀ coordinates,
      coordinates ∉ Metric.closedBall 0 radius → function coordinates = 0) :
    Tendsto
      (fun mesh : ℕ =>
        (∑' coordinates : Fin rank → ℤ,
          function (quadraticIntegerPoint mesh coordinates)) /
            mesh ^ rank)
      atTop (nhds (∫ coordinates, function coordinates)) := by
  have hball := integer_ball_riemann_sum_tendsto
    rank radius function hfunction
  rw [integral_eq_setIntegral_closedBall rank radius function hsupport]
  apply hball.congr'
  filter_upwards with mesh
  rw [integer_full_sum_eq_ball_sum rank mesh radius function]
  intro coordinates hnonzero
  by_contra hnot
  exact hnonzero (hsupport _ hnot)

end FibonacciRibbonKernel
