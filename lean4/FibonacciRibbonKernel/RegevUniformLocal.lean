import FibonacciRibbonKernel.RegevQuadraticLattice
import Mathlib.Topology.MetricSpace.Sequences

namespace FibonacciRibbonKernel

open Filter
open scoped Classical Topology

noncomputable def quadraticShapePoint
    {rank mesh : ℕ}
    (shape : BoundedPartition rank (quadraticSize rank mesh)) :
    Fin rank → ℝ :=
  quadraticCenteredPoint
    ((boundedPartitionQuadraticChartEquiv rank mesh) shape)

theorem quadraticShapePoint_eq_feasiblePoint
    {rank mesh : ℕ} (hmesh : 1 ≤ mesh)
    (shape : BoundedPartition rank (quadraticSize rank mesh)) :
    quadraticShapePoint shape =
      ((boundedPartitionQuadraticFeasiblePointEquiv rank mesh hmesh) shape).1 :=
  rfl

/-- Sequential compactness upgrades Matsumoto's moving-point local limit to
uniform convergence on every fixed closed ball. -/
theorem matsumoto_quadratic_local_uniform_on_closedBall
    (rank : ℕ) (radius : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ mesh : ℕ in atTop,
      ∀ shape : BoundedPartition rank (quadraticSize rank mesh),
        quadraticShapePoint shape ∈ Metric.closedBall 0 radius →
        dist (matsumotoLocalNormalizedTableau shape)
          (regevLocalIntegrand rank (quadraticShapePoint shape)) < ε := by
  by_contra hnot
  rw [Filter.eventually_atTop] at hnot
  have hbad (threshold : ℕ) :
      ∃ mesh, threshold ≤ mesh ∧
        ∃ shape : BoundedPartition rank (quadraticSize rank mesh),
          quadraticShapePoint shape ∈ Metric.closedBall 0 radius ∧
          ε ≤ dist (matsumotoLocalNormalizedTableau shape)
            (regevLocalIntegrand rank (quadraticShapePoint shape)) := by
    by_contra hbadNot
    have hall : ∀ mesh, threshold ≤ mesh →
        ∀ shape : BoundedPartition rank (quadraticSize rank mesh),
          quadraticShapePoint shape ∈ Metric.closedBall 0 radius →
          dist (matsumotoLocalNormalizedTableau shape)
            (regevLocalIntegrand rank (quadraticShapePoint shape)) < ε := by
      intro mesh hmesh shape hpoint
      by_contra herror
      apply hbadNot
      exact ⟨mesh, hmesh, shape, hpoint, le_of_not_gt herror⟩
    exact hnot ⟨threshold, hall⟩
  choose meshes hmeshes shapes hpoints herrors using hbad
  have hmeshesTop : Tendsto meshes atTop atTop := by
    apply Filter.tendsto_atTop_mono' atTop
      (Filter.Eventually.of_forall hmeshes) tendsto_id
  obtain ⟨limit, hlimitClosure, subsequence, hsubsequence,
      hpointsTendsto⟩ :=
    tendsto_subseq_of_bounded Metric.isBounded_closedBall hpoints
  have hlimit : limit ∈ Metric.closedBall (0 : Fin rank → ℝ) radius := by
    rw [Metric.isClosed_closedBall.closure_eq] at hlimitClosure
    exact hlimitClosure
  let submeshes : ℕ → ℕ := meshes ∘ subsequence
  let subshapes : ∀ index,
      BoundedPartition rank (quadraticSize rank (submeshes index)) :=
    fun index => shapes (subsequence index)
  have hsubmeshes : Tendsto submeshes atTop atTop :=
    hmeshesTop.comp hsubsequence.tendsto_atTop
  have hsubpoints : Tendsto
      (fun index => quadraticShapePoint (subshapes index))
      atTop (nhds limit) := by
    simpa [subshapes, submeshes, Function.comp_def] using hpointsTendsto
  have hlocal := matsumotoLocalNormalizedTableau_quadratic_tendsto
    submeshes subshapes limit hsubmeshes hsubpoints
  have hintegrand : Tendsto
      (fun index => regevLocalIntegrand rank
        (quadraticShapePoint (subshapes index)))
      atTop (nhds (regevLocalIntegrand rank limit)) :=
    (continuous_regevLocalIntegrand rank).continuousAt.tendsto.comp hsubpoints
  have hdist : Tendsto
      (fun index => dist
        (matsumotoLocalNormalizedTableau (subshapes index))
        (regevLocalIntegrand rank (quadraticShapePoint (subshapes index))))
      atTop (nhds 0) := by
    simpa using hlocal.dist hintegrand
  have heventSmall : ∀ᶠ index in atTop,
      dist (matsumotoLocalNormalizedTableau (subshapes index))
        (regevLocalIntegrand rank (quadraticShapePoint (subshapes index))) < ε :=
    by
      have heventBall := hdist.eventually (Metric.ball_mem_nhds 0 hε)
      filter_upwards [heventBall] with index hball
      simpa [Real.dist_eq, abs_of_nonneg (dist_nonneg :
        0 ≤ dist (matsumotoLocalNormalizedTableau (subshapes index))
          (regevLocalIntegrand rank (quadraticShapePoint (subshapes index))))]
        using hball
  obtain ⟨index, hsmall⟩ := heventSmall.exists
  exact (not_lt_of_ge (herrors (subsequence index))) hsmall

end FibonacciRibbonKernel
