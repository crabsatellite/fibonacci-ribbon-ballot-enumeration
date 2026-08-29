import FibonacciRibbonKernel.RegevLocalIntegrability

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set
open scoped Classical Topology

noncomputable def regevFullChamberIntegral (rank : ℕ) : ℝ :=
  ∫ coordinates in regevChamber rank,
    regevLocalIntegrand rank coordinates

noncomputable def quadraticTailControl (rank : ℕ) (radius : ℝ) : ℝ :=
  regevCoordinateAbsorptionConstant rank *
    (Real.exp (-((regevCoordinateGaussianCoefficient rank / 2) / 2) *
        radius ^ 2) *
      (2 + 2 * Real.sqrt (Real.pi /
        ((regevCoordinateGaussianCoefficient rank / 2) / 2))) ^ rank)

theorem iUnion_regevTruncatedChamber_nat (rank : ℕ) :
    (⋃ radius : ℕ, regevTruncatedChamber rank (radius : ℝ)) =
      regevChamber rank := by
  ext coordinates
  constructor
  · intro hmembership
    obtain ⟨radius, hcoordinates⟩ := mem_iUnion.mp hmembership
    exact hcoordinates.1
  · intro hcoordinates
    let radius : ℕ := ⌈‖coordinates‖⌉₊
    refine mem_iUnion.2 ⟨radius, hcoordinates, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact Nat.le_ceil ‖coordinates‖

theorem monotone_regevTruncatedChamber_nat (rank : ℕ) :
    Monotone (fun radius : ℕ =>
      regevTruncatedChamber rank (radius : ℝ)) := by
  intro first second hle
  unfold regevTruncatedChamber
  apply inter_subset_inter_right
  exact Metric.closedBall_subset_closedBall (by exact_mod_cast hle)

theorem regev_truncated_integral_nat_tendsto (rank : ℕ) :
    Tendsto
      (fun radius : ℕ =>
        ∫ coordinates in regevTruncatedChamber rank (radius : ℝ),
          regevLocalIntegrand rank coordinates)
      atTop (nhds (regevFullChamberIntegral rank)) := by
  have hlimit := tendsto_setIntegral_of_monotone
    (fun radius : ℕ => regevTruncatedChamber_measurableSet rank radius)
    (monotone_regevTruncatedChamber_nat rank)
    ((integrable_regevLocalIntegrand rank).integrableOn)
  rw [iUnion_regevTruncatedChamber_nat rank] at hlimit
  exact hlimit

theorem quadraticTailControl_tendsto_zero (rank : ℕ) :
    Tendsto (fun radius : ℕ => quadraticTailControl rank radius)
      atTop (nhds 0) := by
  let coefficient := (regevCoordinateGaussianCoefficient rank / 2) / 2
  let amplitude := (2 + 2 * Real.sqrt (Real.pi / coefficient)) ^ rank
  let outer := regevCoordinateAbsorptionConstant rank
  have hcoefficient : 0 < coefficient := by
    dsimp only [coefficient]
    positivity [regevCoordinateGaussianCoefficient_pos rank]
  have hsquare : Tendsto
      (fun radius : ℕ => (radius : ℝ) * (radius : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_atTop₀
      tendsto_natCast_atTop_atTop
  have hnegative : -coefficient < 0 := neg_neg_iff_pos.2 hcoefficient
  have hquadratic : Tendsto
      (fun radius : ℕ => -coefficient * ((radius : ℝ) * (radius : ℝ)))
      atTop atBot := hsquare.const_mul_atTop_of_neg hnegative
  have hexponential : Tendsto
      (fun radius : ℕ => Real.exp (-coefficient * (radius : ℝ) ^ 2))
      atTop (nhds 0) := by
    have := Real.tendsto_exp_atBot.comp hquadratic
    exact this.congr' (Eventually.of_forall fun radius => by
      dsimp only [Function.comp_apply]
      congr 1
      ring)
  have hamplitude : Tendsto
      (fun radius : ℕ =>
        Real.exp (-coefficient * (radius : ℝ) ^ 2) * amplitude)
      atTop (nhds 0) := by
    simpa using hexponential.mul_const amplitude
  have houter : Tendsto
      (fun radius : ℕ => outer *
        (Real.exp (-coefficient * (radius : ℝ) ^ 2) * amplitude))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hamplitude
  simpa [quadraticTailControl, coefficient, amplitude, outer] using houter

/-- Full, untruncated Regev limit on the exact quadratic subsequence
`size=(rank+1)·mesh²`. -/
theorem quadratic_full_normalizedAverage_tendsto (rank : ℕ) :
    Tendsto (fun mesh => quadraticFullNormalizedAverage rank mesh)
      atTop (nhds (regevFullChamberIntegral rank)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  rw [← Filter.eventually_atTop]
  have hthird : 0 < ε / 3 := by positivity
  have htailEventually : ∀ᶠ radius : ℕ in atTop,
      quadraticTailControl rank radius < ε / 3 := by
    exact (quadraticTailControl_tendsto_zero rank).eventually
      (Iio_mem_nhds hthird)
  have hintegralEventually : ∀ᶠ radius : ℕ in atTop,
      dist
        (∫ coordinates in regevTruncatedChamber rank (radius : ℝ),
          regevLocalIntegrand rank coordinates)
        (regevFullChamberIntegral rank) < ε / 3 := by
    exact (regev_truncated_integral_nat_tendsto rank).eventually
      (Metric.ball_mem_nhds _ hthird)
  obtain ⟨radius, htailRadius, hintegralRadius⟩ :=
    (htailEventually.and hintegralEventually).exists
  have htruncated := quadratic_truncated_normalizedAverage_tendsto
    rank (radius : ℝ) (Nat.cast_nonneg radius)
  have htruncatedEventually : ∀ᶠ mesh : ℕ in atTop,
      dist (quadraticTruncatedNormalizedAverage rank mesh radius)
        (∫ coordinates in regevTruncatedChamber rank (radius : ℝ),
          regevLocalIntegrand rank coordinates) < ε / 3 :=
    htruncated.eventually (Metric.ball_mem_nhds _ hthird)
  have hmeshEventually : ∀ᶠ mesh : ℕ in atTop, 1 ≤ mesh :=
    eventually_ge_atTop 1
  filter_upwards [htruncatedEventually, hmeshEventually]
    with mesh htruncatedMesh hmesh
  have htailMesh :
      dist (quadraticFullNormalizedAverage rank mesh)
        (quadraticTruncatedNormalizedAverage rank mesh radius) < ε / 3 := by
    rw [Real.dist_eq]
    exact (abs_quadraticFull_sub_truncated_bound
      rank hmesh radius (Nat.cast_nonneg radius)).trans_lt
      (by simpa [quadraticTailControl] using htailRadius)
  calc
    dist (quadraticFullNormalizedAverage rank mesh)
        (regevFullChamberIntegral rank) ≤
      dist (quadraticFullNormalizedAverage rank mesh)
          (quadraticTruncatedNormalizedAverage rank mesh radius) +
        dist (quadraticTruncatedNormalizedAverage rank mesh radius)
          (regevFullChamberIntegral rank) := dist_triangle _ _ _
    _ ≤ dist (quadraticFullNormalizedAverage rank mesh)
          (quadraticTruncatedNormalizedAverage rank mesh radius) +
        (dist (quadraticTruncatedNormalizedAverage rank mesh radius)
            (∫ coordinates in regevTruncatedChamber rank (radius : ℝ),
              regevLocalIntegrand rank coordinates) +
          dist
            (∫ coordinates in regevTruncatedChamber rank (radius : ℝ),
              regevLocalIntegrand rank coordinates)
            (regevFullChamberIntegral rank)) := by
      gcongr
      exact dist_triangle _ _ _
    _ < ε := by linarith

end FibonacciRibbonKernel
