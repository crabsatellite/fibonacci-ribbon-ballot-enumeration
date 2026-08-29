import FibonacciRibbonKernel.RegevQuadraticFullLimit

namespace FibonacciRibbonKernel

open Filter
open scoped Classical Topology

noncomputable def generalShapePoint
    {rank size : ℕ} (shape : BoundedPartition rank size) :
    Fin rank → ℝ :=
  fun row => regevCenteredRow shape row.castSucc

theorem tracelessExtend_generalShapePoint
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (row : Fin (rank + 1)) :
    tracelessExtend (generalShapePoint shape) row =
      regevCenteredRow shape row := by
  cases row using Fin.lastCases with
  | cast row =>
      rw [tracelessExtend_castSucc]
      rfl
  | last =>
      have hleft := tracelessExtend_sum (generalShapePoint shape)
      have hright := regevCenteredRow_sum_zero shape
      rw [Fin.sum_univ_castSucc] at hleft hright
      have hfirst :
          (∑ index : Fin rank,
            tracelessExtend (generalShapePoint shape) index.castSucc) =
          ∑ index : Fin rank,
            regevCenteredRow shape index.castSucc := by
        apply Finset.sum_congr rfl
        intro index hindex
        rw [tracelessExtend_castSucc]
        rfl
      rw [hfirst] at hleft
      linarith

theorem matsumotoLocalNormalizedTableau_general_tendsto
    {rank : ℕ} (sizes : ℕ → ℕ)
    (shapes : ∀ index, BoundedPartition rank (sizes index))
    (limit : Fin rank → ℝ)
    (hsizes : Tendsto sizes atTop atTop)
    (hpoints : Tendsto (fun index => generalShapePoint (shapes index))
      atTop (nhds limit)) :
    Tendsto (fun index => matsumotoLocalNormalizedTableau (shapes index))
      atTop (nhds (regevLocalIntegrand rank limit)) := by
  have hcentered (row : Fin (rank + 1)) :
      Tendsto (fun index => regevCenteredRow (shapes index) row)
        atTop (nhds (tracelessExtend limit row)) := by
    have hextend := (continuous_tracelessExtend_apply row).continuousAt.tendsto.comp
      hpoints
    apply hextend.congr'
    filter_upwards with index
    simpa only [Function.comp_apply] using
      tracelessExtend_generalShapePoint (shapes index) row
  have hlocal := matsumotoLocalNormalizedTableau_tendsto
    sizes shapes (tracelessExtend limit) hsizes hcentered
  simpa [regevLocalIntegrand, regevGaussianKernel,
    regevVandermonde] using hlocal

/-- Uniform Matsumoto local limit on every fixed compact ball, now for every
size rather than only the quadratic mesh. -/
theorem matsumoto_general_local_uniform_on_closedBall
    (rank : ℕ) (radius : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ size : ℕ in atTop,
      ∀ shape : BoundedPartition rank size,
        generalShapePoint shape ∈ Metric.closedBall 0 radius →
        dist (matsumotoLocalNormalizedTableau shape)
          (regevLocalIntegrand rank (generalShapePoint shape)) < ε := by
  by_contra hnot
  rw [Filter.eventually_atTop] at hnot
  have hbad (threshold : ℕ) :
      ∃ size, threshold ≤ size ∧
        ∃ shape : BoundedPartition rank size,
          generalShapePoint shape ∈ Metric.closedBall 0 radius ∧
          ε ≤ dist (matsumotoLocalNormalizedTableau shape)
            (regevLocalIntegrand rank (generalShapePoint shape)) := by
    by_contra hbadNot
    have hall : ∀ size, threshold ≤ size →
        ∀ shape : BoundedPartition rank size,
          generalShapePoint shape ∈ Metric.closedBall 0 radius →
          dist (matsumotoLocalNormalizedTableau shape)
            (regevLocalIntegrand rank (generalShapePoint shape)) < ε := by
      intro size hsize shape hpoint
      by_contra herror
      apply hbadNot
      exact ⟨size, hsize, shape, hpoint, le_of_not_gt herror⟩
    exact hnot ⟨threshold, hall⟩
  choose sizes hsizes shapes hpoints herrors using hbad
  have hsizesTop : Tendsto sizes atTop atTop := by
    apply Filter.tendsto_atTop_mono' atTop
      (Filter.Eventually.of_forall hsizes) tendsto_id
  obtain ⟨limit, hlimitClosure, subsequence, hsubsequence,
      hpointsTendsto⟩ :=
    tendsto_subseq_of_bounded Metric.isBounded_closedBall hpoints
  have hlimit : limit ∈ Metric.closedBall (0 : Fin rank → ℝ) radius := by
    rw [Metric.isClosed_closedBall.closure_eq] at hlimitClosure
    exact hlimitClosure
  let subsizes : ℕ → ℕ := sizes ∘ subsequence
  let subshapes : ∀ index, BoundedPartition rank (subsizes index) :=
    fun index => shapes (subsequence index)
  have hsubsizes : Tendsto subsizes atTop atTop :=
    hsizesTop.comp hsubsequence.tendsto_atTop
  have hsubpoints : Tendsto
      (fun index => generalShapePoint (subshapes index))
      atTop (nhds limit) := by
    simpa [subshapes, subsizes, Function.comp_def] using hpointsTendsto
  have hlocal := matsumotoLocalNormalizedTableau_general_tendsto
    subsizes subshapes limit hsubsizes hsubpoints
  have hintegrand : Tendsto
      (fun index => regevLocalIntegrand rank
        (generalShapePoint (subshapes index)))
      atTop (nhds (regevLocalIntegrand rank limit)) :=
    (continuous_regevLocalIntegrand rank).continuousAt.tendsto.comp hsubpoints
  have hdist : Tendsto
      (fun index => dist
        (matsumotoLocalNormalizedTableau (subshapes index))
        (regevLocalIntegrand rank (generalShapePoint (subshapes index))))
      atTop (nhds 0) := by
    simpa using hlocal.dist hintegrand
  have heventSmall : ∀ᶠ index in atTop,
      dist (matsumotoLocalNormalizedTableau (subshapes index))
        (regevLocalIntegrand rank (generalShapePoint (subshapes index))) < ε := by
    have heventBall := hdist.eventually (Metric.ball_mem_nhds 0 hε)
    filter_upwards [heventBall] with index hball
    simpa [Real.dist_eq, abs_of_nonneg (dist_nonneg :
      0 ≤ dist (matsumotoLocalNormalizedTableau (subshapes index))
        (regevLocalIntegrand rank (generalShapePoint (subshapes index))))]
      using hball
  obtain ⟨index, hsmall⟩ := heventSmall.exists
  exact (not_lt_of_ge (herrors (subsequence index))) hsmall

end FibonacciRibbonKernel
