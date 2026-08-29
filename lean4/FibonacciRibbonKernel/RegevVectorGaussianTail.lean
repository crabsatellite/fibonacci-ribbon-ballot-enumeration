import FibonacciRibbonKernel.RegevVectorGaussian

namespace FibonacciRibbonKernel

open Set
open scoped Classical

noncomputable def regevScaledPiGaussian
    (coefficient : ℝ) (rank mesh : ℕ)
    (point : Fin rank → ℤ) : ℝ :=
  regevPiProduct (regevScaledGaussianLine coefficient mesh) rank point

theorem regevScaledPiGaussian_nonneg
    (coefficient : ℝ) (rank mesh : ℕ) (point : Fin rank → ℤ) :
    0 ≤ regevScaledPiGaussian coefficient rank mesh point :=
  regevPiProduct_nonneg
    (fun index => regevScaledGaussianLine_nonneg coefficient mesh index)
    rank point

theorem summable_regevScaledPiGaussian
    {coefficient : ℝ} (hcoefficient : 0 < coefficient)
    (rank : ℕ) {mesh : ℕ} (hmesh : 1 ≤ mesh) :
    Summable (regevScaledPiGaussian coefficient rank mesh) :=
  summable_regevPiProduct
    (fun index => regevScaledGaussianLine_nonneg coefficient mesh index)
    (summable_regevScaledGaussianLine hcoefficient hmesh) rank

theorem tsum_regevScaledPiGaussian
    {coefficient : ℝ} (hcoefficient : 0 < coefficient)
    (rank : ℕ) {mesh : ℕ} (hmesh : 1 ≤ mesh) :
    (∑' point : Fin rank → ℤ,
      regevScaledPiGaussian coefficient rank mesh point) =
      (∑' index : ℤ,
        regevScaledGaussianLine coefficient mesh index) ^ rank :=
  tsum_regevPiProduct
    (fun index => regevScaledGaussianLine_nonneg coefficient mesh index)
    (summable_regevScaledGaussianLine hcoefficient hmesh) rank

theorem regevScaledPiGaussian_total_bound
    {coefficient : ℝ} (hcoefficient : 0 < coefficient)
    (rank : ℕ) {mesh : ℕ} (hmesh : 1 ≤ mesh) :
    (∑' point : Fin rank → ℤ,
      regevScaledPiGaussian coefficient rank mesh point) / mesh ^ rank ≤
      (2 + 2 * Real.sqrt (Real.pi / coefficient)) ^ rank := by
  rw [tsum_regevScaledPiGaussian hcoefficient rank hmesh]
  rw [← div_pow]
  apply pow_le_pow_left₀
  · exact div_nonneg
      (tsum_nonneg fun index =>
        regevScaledGaussianLine_nonneg coefficient mesh index)
      (Nat.cast_nonneg mesh)
  · exact regevScaledGaussianLine_total_bound hcoefficient hmesh

def regevScaledPiGaussianTailIndex
    (rank mesh : ℕ) (radius : ℝ) : Set (Fin rank → ℤ) :=
  {point | radius < ‖fun row => (point row : ℝ) / mesh‖}

theorem regevScaledPiGaussian_tail_pointwise
    {coefficient radius : ℝ} (hcoefficient : 0 < coefficient)
    (hradius : 0 ≤ radius) {rank mesh : ℕ}
    (point : regevScaledPiGaussianTailIndex rank mesh radius) :
    regevScaledPiGaussian coefficient rank mesh point.1 ≤
      Real.exp (-(coefficient / 2) * radius ^ 2) *
        regevScaledPiGaussian (coefficient / 2) rank mesh point.1 := by
  let coordinates : Fin rank → ℝ :=
    fun row => (point.1 row : ℝ) / mesh
  have hnorm : radius < ‖coordinates‖ := point.2
  have hnotAll : ¬ ∀ row, ‖coordinates row‖ ≤ radius := by
    intro hall
    have := (pi_norm_le_iff_of_nonneg hradius).2 hall
    exact (not_le_of_gt hnorm) this
  obtain ⟨row, hrowNot⟩ := not_forall.mp hnotAll
  have hrow : radius < ‖coordinates row‖ := lt_of_not_ge hrowNot
  have hrowAbs : radius < |coordinates row| := by
    simpa [Real.norm_eq_abs] using hrow
  have hrowSquare : radius ^ 2 ≤ coordinates row ^ 2 := by
    have habsNonneg : 0 ≤ |coordinates row| := abs_nonneg _
    have : radius ^ 2 ≤ |coordinates row| ^ 2 := by
      nlinarith
    simpa only [sq_abs] using this
  have hsquare : radius ^ 2 ≤ regevCoordinateSquaredSum coordinates := by
    unfold regevCoordinateSquaredSum
    exact hrowSquare.trans (Finset.single_le_sum
      (fun index _ => sq_nonneg (coordinates index))
      (Finset.mem_univ row))
  have hfull :
      regevScaledPiGaussian coefficient rank mesh point.1 =
        Real.exp (-coefficient * regevCoordinateSquaredSum coordinates) := by
    unfold regevScaledPiGaussian regevPiProduct
    unfold regevScaledGaussianLine regevScaledGaussianReal
    rw [← Real.exp_sum]
    unfold regevCoordinateSquaredSum
    congr 1
    rw [← Finset.mul_sum]
  have hhalf :
      regevScaledPiGaussian (coefficient / 2) rank mesh point.1 =
        Real.exp (-(coefficient / 2) *
          regevCoordinateSquaredSum coordinates) := by
    unfold regevScaledPiGaussian regevPiProduct
    unfold regevScaledGaussianLine regevScaledGaussianReal
    rw [← Real.exp_sum]
    unfold regevCoordinateSquaredSum
    congr 1
    rw [← Finset.mul_sum]
  rw [hfull, hhalf, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Uniform rank-dimensional Gaussian tail bound outside the closed sup-norm
ball.  The factor is exponentially small in the radius and independent of the
mesh. -/
theorem regevScaledPiGaussian_tail_bound
    {coefficient radius : ℝ} (hcoefficient : 0 < coefficient)
    (hradius : 0 ≤ radius) (rank : ℕ)
    {mesh : ℕ} (hmesh : 1 ≤ mesh) :
    (∑' point : regevScaledPiGaussianTailIndex rank mesh radius,
      regevScaledPiGaussian coefficient rank mesh point.1) / mesh ^ rank ≤
      Real.exp (-(coefficient / 2) * radius ^ 2) *
        (2 + 2 * Real.sqrt (Real.pi / (coefficient / 2))) ^ rank := by
  let factor := Real.exp (-(coefficient / 2) * radius ^ 2)
  have hhalfPositive : 0 < coefficient / 2 := by positivity
  have hfactorNonneg : 0 ≤ factor := (Real.exp_pos _).le
  have hleft := (summable_regevScaledPiGaussian
    hcoefficient rank hmesh).subtype
      (regevScaledPiGaussianTailIndex rank mesh radius)
  have hhalf := summable_regevScaledPiGaussian hhalfPositive rank hmesh
  have hhalfSubtype := hhalf.subtype
    (regevScaledPiGaussianTailIndex rank mesh radius)
  have hsumBound :
      (∑' point : regevScaledPiGaussianTailIndex rank mesh radius,
        regevScaledPiGaussian coefficient rank mesh point.1) ≤
      factor *
        ∑' point : Fin rank → ℤ,
          regevScaledPiGaussian (coefficient / 2) rank mesh point := by
    calc
      (∑' point : regevScaledPiGaussianTailIndex rank mesh radius,
        regevScaledPiGaussian coefficient rank mesh point.1) ≤
        ∑' point : regevScaledPiGaussianTailIndex rank mesh radius,
          factor * regevScaledPiGaussian
            (coefficient / 2) rank mesh point.1 :=
          hleft.tsum_le_tsum
            (fun point => regevScaledPiGaussian_tail_pointwise
              hcoefficient hradius point)
            (hhalfSubtype.mul_left factor)
      _ = factor *
          ∑' point : regevScaledPiGaussianTailIndex rank mesh radius,
            regevScaledPiGaussian (coefficient / 2) rank mesh point.1 :=
        tsum_mul_left
      _ ≤ factor *
          ∑' point : Fin rank → ℤ,
            regevScaledPiGaussian (coefficient / 2) rank mesh point := by
        apply mul_le_mul_of_nonneg_left _ hfactorNonneg
        exact Summable.tsum_subtype_le
          (regevScaledPiGaussian (coefficient / 2) rank mesh)
          (regevScaledPiGaussianTailIndex rank mesh radius)
          (fun point => regevScaledPiGaussian_nonneg _ _ _ point)
          hhalf
  have hmeshPowerNonneg : (0 : ℝ) ≤ mesh ^ rank := by positivity
  have hnormalized := div_le_div_of_nonneg_right hsumBound hmeshPowerNonneg
  calc
    (∑' point : regevScaledPiGaussianTailIndex rank mesh radius,
      regevScaledPiGaussian coefficient rank mesh point.1) / mesh ^ rank ≤
      (factor * ∑' point : Fin rank → ℤ,
        regevScaledPiGaussian (coefficient / 2) rank mesh point) /
          mesh ^ rank := hnormalized
    _ = factor *
        ((∑' point : Fin rank → ℤ,
          regevScaledPiGaussian (coefficient / 2) rank mesh point) /
            mesh ^ rank) := by ring
    _ ≤ factor *
        (2 + 2 * Real.sqrt (Real.pi / (coefficient / 2))) ^ rank :=
      mul_le_mul_of_nonneg_left
        (regevScaledPiGaussian_total_bound hhalfPositive rank hmesh)
        hfactorNonneg

end FibonacciRibbonKernel
