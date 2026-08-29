import FibonacciRibbonKernel.RegevCoordinateEnvelopeBound

namespace FibonacciRibbonKernel

open scoped Classical

noncomputable def regevCoordinateSquaredSum
    {rank : ℕ} (coordinates : Fin rank → ℝ) : ℝ :=
  ∑ row, coordinates row ^ 2

noncomputable def regevCoordinateGaussianCoefficient (rank : ℕ) : ℝ :=
  (2 * regevEntropyDenominator rank)⁻¹

theorem regevCoordinateGaussianCoefficient_pos (rank : ℕ) :
    0 < regevCoordinateGaussianCoefficient rank := by
  unfold regevCoordinateGaussianCoefficient regevEntropyDenominator
  positivity

theorem regevCoordinateBase_pow_le_exp
    {rank : ℕ} (coordinates : Fin rank → ℝ) (degree : ℕ) :
    regevCoordinateBase coordinates ^ degree ≤
      Real.exp ((degree : ℝ) * regevCoordinateAbsSum coordinates) := by
  have hsumNonneg : 0 ≤ regevCoordinateAbsSum coordinates := by
    unfold regevCoordinateAbsSum
    positivity
  have hbaseExp : regevCoordinateBase coordinates ≤
      Real.exp (regevCoordinateAbsSum coordinates) := by
    unfold regevCoordinateBase
    simpa only [add_comm] using
      Real.add_one_le_exp (regevCoordinateAbsSum coordinates)
  calc
    regevCoordinateBase coordinates ^ degree ≤
        Real.exp (regevCoordinateAbsSum coordinates) ^ degree :=
      pow_le_pow_left₀ (zero_le_one.trans
        (regevCoordinateBase_one_le coordinates)) hbaseExp degree
    _ = Real.exp ((degree : ℝ) * regevCoordinateAbsSum coordinates) := by
      rw [← Real.exp_nat_mul]

theorem regevCoordinate_linear_quadratic_le
    {rank : ℕ} (coordinates : Fin rank → ℝ)
    {coefficient : ℝ} (hcoefficient : 0 < coefficient)
    (degree : ℕ) :
    (degree : ℝ) * regevCoordinateAbsSum coordinates -
        coefficient * regevCoordinateSquaredSum coordinates ≤
      (rank : ℝ) * (degree : ℝ) ^ 2 / (2 * coefficient) -
        (coefficient / 2) * regevCoordinateSquaredSum coordinates := by
  have hpoint : ∀ row : Fin rank,
      (degree : ℝ) * |coordinates row| -
          coefficient * coordinates row ^ 2 ≤
        (degree : ℝ) ^ 2 / (2 * coefficient) -
          (coefficient / 2) * coordinates row ^ 2 := by
    intro row
    have hidentity :
        ((degree : ℝ) ^ 2 / (2 * coefficient) -
            (coefficient / 2) * coordinates row ^ 2) -
          ((degree : ℝ) * |coordinates row| -
            coefficient * coordinates row ^ 2) =
          (coefficient * |coordinates row| - degree) ^ 2 /
            (2 * coefficient) := by
      field_simp [hcoefficient.ne']
      nlinarith [sq_abs (coordinates row)]
    rw [← sub_nonneg, hidentity]
    positivity
  have hsum :
      (∑ row : Fin rank,
        ((degree : ℝ) * |coordinates row| -
          coefficient * coordinates row ^ 2)) ≤
        ∑ row : Fin rank,
          ((degree : ℝ) ^ 2 / (2 * coefficient) -
            (coefficient / 2) * coordinates row ^ 2) := by
    apply Finset.sum_le_sum
    intro row hrow
    exact hpoint row
  calc
    (degree : ℝ) * regevCoordinateAbsSum coordinates -
        coefficient * regevCoordinateSquaredSum coordinates =
      ∑ row : Fin rank,
        ((degree : ℝ) * |coordinates row| -
          coefficient * coordinates row ^ 2) := by
      unfold regevCoordinateAbsSum regevCoordinateSquaredSum
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ ∑ row : Fin rank,
        ((degree : ℝ) ^ 2 / (2 * coefficient) -
          (coefficient / 2) * coordinates row ^ 2) := hsum
    _ = (rank : ℝ) * (degree : ℝ) ^ 2 / (2 * coefficient) -
        (coefficient / 2) * regevCoordinateSquaredSum coordinates := by
      unfold regevCoordinateSquaredSum
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Finset.mul_sum]
      have hcard : (Finset.univ : Finset (Fin rank)).card = rank := by simp
      rw [hcard]
      ring

theorem regevCoordinateSquaredSum_le_traceless
    {rank : ℕ} (coordinates : Fin rank → ℝ) :
    regevCoordinateSquaredSum coordinates ≤
      ∑ row : Fin (rank + 1), tracelessExtend coordinates row ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  simp only [tracelessExtend_castSucc]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem regevCoordinate_gaussian_le_chart
    {rank : ℕ} (coordinates : Fin rank → ℝ) :
    Real.exp (-(∑ row : Fin (rank + 1),
        tracelessExtend coordinates row ^ 2 /
          (2 * regevEntropyDenominator rank))) ≤
      Real.exp (-(regevCoordinateGaussianCoefficient rank *
        regevCoordinateSquaredSum coordinates)) := by
  apply Real.exp_le_exp.mpr
  have hdenominator : 0 < 2 * regevEntropyDenominator rank := by
    unfold regevEntropyDenominator
    positivity
  have hsquares := regevCoordinateSquaredSum_le_traceless coordinates
  have hsumRewrite :
      (∑ row : Fin (rank + 1),
        tracelessExtend coordinates row ^ 2 /
          (2 * regevEntropyDenominator rank)) =
        regevCoordinateGaussianCoefficient rank *
          ∑ row : Fin (rank + 1), tracelessExtend coordinates row ^ 2 := by
    unfold regevCoordinateGaussianCoefficient
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro row hrow
    field_simp
  rw [hsumRewrite]
  have hcoefficientNonneg :
      0 ≤ regevCoordinateGaussianCoefficient rank :=
    (regevCoordinateGaussianCoefficient_pos rank).le
  nlinarith [mul_le_mul_of_nonneg_left hsquares hcoefficientNonneg]

noncomputable def regevCoordinateAbsorptionConstant (rank : ℕ) : ℝ :=
  Real.exp (regevEntropyOffset rank / regevEntropyDenominator rank) *
    regevCoordinateEnvelopeConstant rank *
    Real.exp ((rank : ℝ) * (regevCoordinateEnvelopeDegree rank : ℝ) ^ 2 /
      (2 * regevCoordinateGaussianCoefficient rank))

noncomputable def regevCoordinateSeparableGaussian
    (rank : ℕ) (coordinates : Fin rank → ℝ) : ℝ :=
  ∏ row, Real.exp (-(regevCoordinateGaussianCoefficient rank / 2) *
    coordinates row ^ 2)

/-- The complete polynomial-times-Gaussian majorant is absorbed into a
constant times a separable Gaussian on the exact traceless chart. -/
theorem regevCoordinateDominatingKernel_le_separableGaussian
    (rank : ℕ) (coordinates : Fin rank → ℝ) :
    regevCoordinateDominatingKernel rank coordinates ≤
      regevCoordinateAbsorptionConstant rank *
        regevCoordinateSeparableGaussian rank coordinates := by
  let coefficient := regevCoordinateGaussianCoefficient rank
  let degree := regevCoordinateEnvelopeDegree rank
  have hcoefficient : 0 < coefficient :=
    regevCoordinateGaussianCoefficient_pos rank
  have henvelope := regevCoordinateEnvelopeProduct_le rank coordinates
  have hbase := regevCoordinateBase_pow_le_exp coordinates degree
  have hgaussian := regevCoordinate_gaussian_le_chart coordinates
  have hlinear := regevCoordinate_linear_quadratic_le
    coordinates hcoefficient degree
  have hprefixNonneg : 0 ≤
      Real.exp (regevEntropyOffset rank / regevEntropyDenominator rank) :=
    (Real.exp_pos _).le
  have henvelopeConstantNonneg :
      0 ≤ regevCoordinateEnvelopeConstant rank := by
    unfold regevCoordinateEnvelopeConstant
    positivity
  have hprefixConstantNonneg : 0 ≤
      Real.exp (regevEntropyOffset rank / regevEntropyDenominator rank) *
        regevCoordinateEnvelopeConstant rank :=
    mul_nonneg hprefixNonneg henvelopeConstantNonneg
  have hgaussianNonneg : 0 ≤
      Real.exp (-(∑ row : Fin (rank + 1),
        tracelessExtend coordinates row ^ 2 /
          (2 * regevEntropyDenominator rank))) := (Real.exp_pos _).le
  have hseparableProduct :
      (∏ row, Real.exp (-(coefficient / 2) * coordinates row ^ 2)) =
        Real.exp (-(coefficient / 2) *
          regevCoordinateSquaredSum coordinates) := by
    rw [← Real.exp_sum]
    unfold regevCoordinateSquaredSum
    congr 1
    rw [← Finset.mul_sum]
  unfold regevCoordinateDominatingKernel
  have henvelopeDegree :
      regevCoordinateRowEnvelope rank coordinates *
          regevCoordinatePairEnvelope rank coordinates ≤
        regevCoordinateEnvelopeConstant rank *
          regevCoordinateBase coordinates ^ degree := by
    simpa only [degree] using henvelope
  have hbaseNonneg : 0 ≤ regevCoordinateBase coordinates :=
    zero_le_one.trans (regevCoordinateBase_one_le coordinates)
  have hupperPrefixNonneg : 0 ≤
      Real.exp (regevEntropyOffset rank / regevEntropyDenominator rank) *
        (regevCoordinateEnvelopeConstant rank *
          regevCoordinateBase coordinates ^ degree) :=
    mul_nonneg hprefixNonneg
      (mul_nonneg henvelopeConstantNonneg (pow_nonneg hbaseNonneg degree))
  calc
    Real.exp (regevEntropyOffset rank / regevEntropyDenominator rank) *
        regevCoordinateRowEnvelope rank coordinates *
        regevCoordinatePairEnvelope rank coordinates *
        Real.exp (-(∑ row : Fin (rank + 1),
          tracelessExtend coordinates row ^ 2 /
            (2 * regevEntropyDenominator rank))) ≤
      Real.exp (regevEntropyOffset rank / regevEntropyDenominator rank) *
        (regevCoordinateEnvelopeConstant rank *
          regevCoordinateBase coordinates ^ degree) *
        Real.exp (-(coefficient *
          regevCoordinateSquaredSum coordinates)) := by
      apply mul_le_mul
      · calc
          Real.exp (regevEntropyOffset rank / regevEntropyDenominator rank) *
              regevCoordinateRowEnvelope rank coordinates *
              regevCoordinatePairEnvelope rank coordinates =
            Real.exp (regevEntropyOffset rank / regevEntropyDenominator rank) *
              (regevCoordinateRowEnvelope rank coordinates *
                regevCoordinatePairEnvelope rank coordinates) := by ring
          _ ≤ Real.exp (regevEntropyOffset rank / regevEntropyDenominator rank) *
              (regevCoordinateEnvelopeConstant rank *
                regevCoordinateBase coordinates ^ degree) :=
            mul_le_mul_of_nonneg_left henvelopeDegree hprefixNonneg
      · exact hgaussian
      · exact hgaussianNonneg
      · exact hupperPrefixNonneg
    _ ≤ Real.exp (regevEntropyOffset rank / regevEntropyDenominator rank) *
        regevCoordinateEnvelopeConstant rank *
        Real.exp ((degree : ℝ) * regevCoordinateAbsSum coordinates -
          coefficient * regevCoordinateSquaredSum coordinates) := by
      have hbaseGaussian := mul_le_mul_of_nonneg_right hbase
        (Real.exp_pos (-(coefficient *
          regevCoordinateSquaredSum coordinates))).le
      calc
        _ ≤ Real.exp (regevEntropyOffset rank / regevEntropyDenominator rank) *
            regevCoordinateEnvelopeConstant rank *
            (Real.exp ((degree : ℝ) * regevCoordinateAbsSum coordinates) *
              Real.exp (-(coefficient *
                regevCoordinateSquaredSum coordinates))) := by
          calc
            _ = (Real.exp (regevEntropyOffset rank /
                  regevEntropyDenominator rank) *
                regevCoordinateEnvelopeConstant rank) *
              (regevCoordinateBase coordinates ^ degree *
                Real.exp (-(coefficient *
                  regevCoordinateSquaredSum coordinates))) := by ring
            _ ≤ (Real.exp (regevEntropyOffset rank /
                  regevEntropyDenominator rank) *
                regevCoordinateEnvelopeConstant rank) *
              (Real.exp ((degree : ℝ) *
                  regevCoordinateAbsSum coordinates) *
                Real.exp (-(coefficient *
                  regevCoordinateSquaredSum coordinates))) :=
              mul_le_mul_of_nonneg_left hbaseGaussian hprefixConstantNonneg
            _ = _ := by ring
        _ = _ := by
          rw [← Real.exp_add]
          ring_nf
    _ ≤ Real.exp (regevEntropyOffset rank / regevEntropyDenominator rank) *
        regevCoordinateEnvelopeConstant rank *
        Real.exp ((rank : ℝ) * (degree : ℝ) ^ 2 /
            (2 * coefficient) -
          (coefficient / 2) * regevCoordinateSquaredSum coordinates) := by
      apply mul_le_mul_of_nonneg_left _ hprefixConstantNonneg
      exact Real.exp_le_exp.mpr hlinear
    _ = regevCoordinateAbsorptionConstant rank *
        regevCoordinateSeparableGaussian rank coordinates := by
      unfold regevCoordinateAbsorptionConstant
      unfold regevCoordinateSeparableGaussian
      change
        Real.exp (regevEntropyOffset rank / regevEntropyDenominator rank) *
            regevCoordinateEnvelopeConstant rank *
            Real.exp ((rank : ℝ) * (degree : ℝ) ^ 2 /
                (2 * coefficient) -
              (coefficient / 2) * regevCoordinateSquaredSum coordinates) =
          Real.exp (regevEntropyOffset rank / regevEntropyDenominator rank) *
            regevCoordinateEnvelopeConstant rank *
            Real.exp ((rank : ℝ) * (degree : ℝ) ^ 2 /
              (2 * coefficient)) *
            (∏ row, Real.exp (-(coefficient / 2) * coordinates row ^ 2))
      rw [hseparableProduct]
      rw [show (rank : ℝ) * (degree : ℝ) ^ 2 / (2 * coefficient) -
          (coefficient / 2) * regevCoordinateSquaredSum coordinates =
        (rank : ℝ) * (degree : ℝ) ^ 2 / (2 * coefficient) +
          (-(coefficient / 2) * regevCoordinateSquaredSum coordinates) by ring]
      rw [Real.exp_add]
      ring

end FibonacciRibbonKernel
