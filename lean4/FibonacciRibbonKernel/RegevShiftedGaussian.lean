import FibonacciRibbonKernel.RegevRealScaleGaussianBase
import FibonacciRibbonKernel.RegevGeneralLattice
import FibonacciRibbonKernel.RegevProductLatticeTsum

namespace FibonacciRibbonKernel

open Set
open scoped Classical

noncomputable def regevShiftedGaussianLine
    (coefficient scale shift : ℝ) (index : ℤ) : ℝ :=
  Real.exp (-coefficient * ((index : ℝ) / scale + shift) ^ 2)

theorem regevShiftedGaussianLine_nonneg
    (coefficient scale shift : ℝ) (index : ℤ) :
    0 ≤ regevShiftedGaussianLine coefficient scale shift index :=
  (Real.exp_pos _).le

theorem regevShiftedGaussianLine_le
    {coefficient scale shift : ℝ} (hcoefficient : 0 < coefficient)
    (hshift : |shift| ≤ 1) (index : ℤ) :
    regevShiftedGaussianLine coefficient scale shift index ≤
      Real.exp coefficient *
        regevRealScaleGaussianLine (coefficient / 2) scale index := by
  let x := (index : ℝ) / scale
  have hshiftSquare : shift ^ 2 ≤ 1 := by
    have hpower := pow_le_pow_left₀ (abs_nonneg shift) hshift 2
    simpa only [sq_abs, one_pow] using hpower
  have hquadratic : x ^ 2 / 2 - shift ^ 2 ≤ (x + shift) ^ 2 := by
    nlinarith [sq_nonneg (x + 2 * shift)]
  unfold regevShiftedGaussianLine
  unfold regevRealScaleGaussianLine regevRealScaleGaussianReal
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp only [x] at hquadratic
  nlinarith

theorem summable_regevShiftedGaussianLine
    {coefficient scale shift : ℝ} (hcoefficient : 0 < coefficient)
    (hscale : 0 < scale) (hshift : |shift| ≤ 1) :
    Summable (regevShiftedGaussianLine coefficient scale shift) := by
  have hhalf : 0 < coefficient / 2 := by positivity
  have hdom := (summable_regevRealScaleGaussianLine hhalf hscale).mul_left
    (Real.exp coefficient)
  exact hdom.of_nonneg_of_le
    (fun index => regevShiftedGaussianLine_nonneg _ _ _ index)
    (fun index => regevShiftedGaussianLine_le hcoefficient hshift index)

theorem regevShiftedGaussianLine_total_bound
    {coefficient scale shift : ℝ} (hcoefficient : 0 < coefficient)
    (hscale : 1 ≤ scale) (hshift : |shift| ≤ 1) :
    (∑' index : ℤ,
      regevShiftedGaussianLine coefficient scale shift index) / scale ≤
      Real.exp coefficient *
        (2 + 2 * Real.sqrt (Real.pi / (coefficient / 2))) := by
  have hscalePos : 0 < scale := zero_lt_one.trans_le hscale
  have hhalf : 0 < coefficient / 2 := by positivity
  have hleft := summable_regevShiftedGaussianLine
    hcoefficient hscalePos hshift
  have hright := (summable_regevRealScaleGaussianLine hhalf hscalePos).mul_left
    (Real.exp coefficient)
  have hsum := hleft.tsum_le_tsum
    (fun index => regevShiftedGaussianLine_le hcoefficient hshift index)
    hright
  have hnormalized := div_le_div_of_nonneg_right hsum hscalePos.le
  calc
    (∑' index : ℤ,
      regevShiftedGaussianLine coefficient scale shift index) / scale ≤
      (∑' index : ℤ, Real.exp coefficient *
        regevRealScaleGaussianLine (coefficient / 2) scale index) / scale :=
      hnormalized
    _ = Real.exp coefficient *
        ((∑' index : ℤ,
          regevRealScaleGaussianLine (coefficient / 2) scale index) / scale) := by
      rw [tsum_mul_left]
      ring
    _ ≤ Real.exp coefficient *
        (2 + 2 * Real.sqrt (Real.pi / (coefficient / 2))) :=
      mul_le_mul_of_nonneg_left
        (regevRealScaleGaussianLine_total_bound hhalf hscale)
        (Real.exp_pos _).le

noncomputable def regevShiftedPiGaussian
    (coefficient scale shift : ℝ) (rank : ℕ)
    (point : Fin rank → ℤ) : ℝ :=
  regevPiProduct
    (regevShiftedGaussianLine coefficient scale shift) rank point

theorem regevShiftedPiGaussian_nonneg
    (coefficient scale shift : ℝ) (rank : ℕ)
    (point : Fin rank → ℤ) :
    0 ≤ regevShiftedPiGaussian coefficient scale shift rank point :=
  regevPiProduct_nonneg
    (fun index => regevShiftedGaussianLine_nonneg coefficient scale shift index)
    rank point

theorem summable_regevShiftedPiGaussian
    {coefficient scale shift : ℝ} (hcoefficient : 0 < coefficient)
    (hscale : 0 < scale) (hshift : |shift| ≤ 1) (rank : ℕ) :
    Summable (regevShiftedPiGaussian coefficient scale shift rank) :=
  summable_regevPiProduct
    (fun index => regevShiftedGaussianLine_nonneg coefficient scale shift index)
    (summable_regevShiftedGaussianLine hcoefficient hscale hshift) rank

theorem regevShiftedPiGaussian_total_bound
    {coefficient scale shift : ℝ} (hcoefficient : 0 < coefficient)
    (hscale : 1 ≤ scale) (hshift : |shift| ≤ 1) (rank : ℕ) :
    (∑' point : Fin rank → ℤ,
      regevShiftedPiGaussian coefficient scale shift rank point) /
        scale ^ rank ≤
      (Real.exp coefficient *
        (2 + 2 * Real.sqrt (Real.pi / (coefficient / 2)))) ^ rank := by
  have hscalePos : 0 < scale := zero_lt_one.trans_le hscale
  rw [show (∑' point : Fin rank → ℤ,
      regevShiftedPiGaussian coefficient scale shift rank point) =
      (∑' index : ℤ,
        regevShiftedGaussianLine coefficient scale shift index) ^ rank by
    exact tsum_regevPiProduct
      (fun index => regevShiftedGaussianLine_nonneg coefficient scale shift index)
      (summable_regevShiftedGaussianLine hcoefficient hscalePos hshift) rank]
  rw [← div_pow]
  apply pow_le_pow_left₀
  · exact div_nonneg
      (tsum_nonneg fun index =>
        regevShiftedGaussianLine_nonneg coefficient scale shift index)
      hscalePos.le
  · exact regevShiftedGaussianLine_total_bound hcoefficient hscale hshift

def regevShiftedPiGaussianTailIndex
    (scale shift radius : ℝ) (rank : ℕ) : Set (Fin rank → ℤ) :=
  {point | radius < ‖fun row => (point row : ℝ) / scale + shift‖}

theorem regevShiftedPiGaussian_tail_pointwise
    {coefficient scale shift radius : ℝ} (hcoefficient : 0 < coefficient)
    (hradius : 0 ≤ radius) {rank : ℕ}
    (point : regevShiftedPiGaussianTailIndex scale shift radius rank) :
    regevShiftedPiGaussian coefficient scale shift rank point.1 ≤
      Real.exp (-(coefficient / 2) * radius ^ 2) *
        regevShiftedPiGaussian (coefficient / 2) scale shift rank point.1 := by
  let coordinates : Fin rank → ℝ :=
    fun row => (point.1 row : ℝ) / scale + shift
  have hnorm : radius < ‖coordinates‖ := point.2
  have hnotAll : ¬ ∀ row, ‖coordinates row‖ ≤ radius := by
    intro hall
    exact (not_le_of_gt hnorm) ((pi_norm_le_iff_of_nonneg hradius).2 hall)
  obtain ⟨row, hrowNot⟩ := not_forall.mp hnotAll
  have hrow : radius < ‖coordinates row‖ := lt_of_not_ge hrowNot
  have hrowAbs : radius < |coordinates row| := by
    simpa [Real.norm_eq_abs] using hrow
  have hrowSquare : radius ^ 2 ≤ coordinates row ^ 2 := by
    have : radius ^ 2 ≤ |coordinates row| ^ 2 := by
      nlinarith [abs_nonneg (coordinates row)]
    simpa only [sq_abs] using this
  have hsquare : radius ^ 2 ≤ regevCoordinateSquaredSum coordinates := by
    unfold regevCoordinateSquaredSum
    exact hrowSquare.trans (Finset.single_le_sum
      (fun index _ => sq_nonneg (coordinates index))
      (Finset.mem_univ row))
  have hfull :
      regevShiftedPiGaussian coefficient scale shift rank point.1 =
        Real.exp (-coefficient * regevCoordinateSquaredSum coordinates) := by
    unfold regevShiftedPiGaussian regevPiProduct
    unfold regevShiftedGaussianLine
    rw [← Real.exp_sum]
    unfold regevCoordinateSquaredSum
    congr 1
    rw [← Finset.mul_sum]
  have hhalf :
      regevShiftedPiGaussian (coefficient / 2) scale shift rank point.1 =
        Real.exp (-(coefficient / 2) *
          regevCoordinateSquaredSum coordinates) := by
    unfold regevShiftedPiGaussian regevPiProduct
    unfold regevShiftedGaussianLine
    rw [← Real.exp_sum]
    unfold regevCoordinateSquaredSum
    congr 1
    rw [← Finset.mul_sum]
  rw [hfull, hhalf, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem regevShiftedPiGaussian_tail_bound
    {coefficient scale shift radius : ℝ} (hcoefficient : 0 < coefficient)
    (hscale : 1 ≤ scale) (hshift : |shift| ≤ 1)
    (hradius : 0 ≤ radius) (rank : ℕ) :
    (∑' point : regevShiftedPiGaussianTailIndex scale shift radius rank,
      regevShiftedPiGaussian coefficient scale shift rank point.1) /
        scale ^ rank ≤
      Real.exp (-(coefficient / 2) * radius ^ 2) *
        (Real.exp (coefficient / 2) *
          (2 + 2 * Real.sqrt (Real.pi / (coefficient / 4)))) ^ rank := by
  let factor := Real.exp (-(coefficient / 2) * radius ^ 2)
  have hscalePos : 0 < scale := zero_lt_one.trans_le hscale
  have hhalf : 0 < coefficient / 2 := by positivity
  have hfactorNonneg : 0 ≤ factor := (Real.exp_pos _).le
  have hleft := (summable_regevShiftedPiGaussian
    hcoefficient hscalePos hshift rank).subtype
      (regevShiftedPiGaussianTailIndex scale shift radius rank)
  have hhalfSum := summable_regevShiftedPiGaussian
    hhalf hscalePos hshift rank
  have hhalfSubtype := hhalfSum.subtype
    (regevShiftedPiGaussianTailIndex scale shift radius rank)
  have hsumBound :
      (∑' point : regevShiftedPiGaussianTailIndex scale shift radius rank,
        regevShiftedPiGaussian coefficient scale shift rank point.1) ≤
      factor * ∑' point : Fin rank → ℤ,
        regevShiftedPiGaussian (coefficient / 2) scale shift rank point := by
    calc
      _ ≤ ∑' point : regevShiftedPiGaussianTailIndex scale shift radius rank,
          factor * regevShiftedPiGaussian
            (coefficient / 2) scale shift rank point.1 :=
        hleft.tsum_le_tsum
          (fun point => regevShiftedPiGaussian_tail_pointwise
            hcoefficient hradius point)
          (hhalfSubtype.mul_left factor)
      _ = factor * ∑' point : regevShiftedPiGaussianTailIndex scale shift radius rank,
          regevShiftedPiGaussian (coefficient / 2) scale shift rank point.1 :=
        tsum_mul_left
      _ ≤ factor * ∑' point : Fin rank → ℤ,
          regevShiftedPiGaussian (coefficient / 2) scale shift rank point := by
        apply mul_le_mul_of_nonneg_left _ hfactorNonneg
        exact Summable.tsum_subtype_le _ _
          (fun point => regevShiftedPiGaussian_nonneg _ _ _ _ point)
          hhalfSum
  have hnormalized := div_le_div_of_nonneg_right hsumBound
    (pow_nonneg hscalePos.le rank)
  calc
    _ ≤ (factor * ∑' point : Fin rank → ℤ,
        regevShiftedPiGaussian (coefficient / 2) scale shift rank point) /
          scale ^ rank := hnormalized
    _ = factor * ((∑' point : Fin rank → ℤ,
        regevShiftedPiGaussian (coefficient / 2) scale shift rank point) /
          scale ^ rank) := by ring
    _ ≤ factor *
        (Real.exp (coefficient / 2) *
          (2 + 2 * Real.sqrt (Real.pi / (coefficient / 4)))) ^ rank := by
      apply mul_le_mul_of_nonneg_left _ hfactorNonneg
      simpa only [show (coefficient / 2) / 2 = coefficient / 4 by ring] using
        regevShiftedPiGaussian_total_bound hhalf hscale hshift rank

end FibonacciRibbonKernel
