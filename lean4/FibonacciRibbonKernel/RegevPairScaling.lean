import FibonacciRibbonKernel.RegevCenteredLattice

namespace FibonacciRibbonKernel

open scoped Classical

noncomputable def matsumotoPairProduct
    {rank size : ℕ} (shape : BoundedPartition rank size) : ℝ :=
  ∏ row : Fin (rank + 1), ∏ next ∈ Finset.Ioi row,
    (((shape.1 row).val : ℝ) - (shape.1 next).val +
      (next.val : ℝ) - row.val)

theorem pairScale_power_eq_fixedRankExponent
    (rank size : ℕ) (hsize : 1 ≤ size) :
    Real.sqrt ((size : ℝ) / (rank + 1 : ℝ)) ^ staircaseWeight rank =
      ((size : ℝ) / (rank + 1 : ℝ)) ^
        fixedRankExponent (rank + 1) := by
  have hbase : 0 ≤ (size : ℝ) / (rank + 1 : ℝ) := by positivity
  have hbasePos : 0 < (size : ℝ) / (rank + 1 : ℝ) := by positivity
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hbase]
  have hstaircaseNat : 2 * staircaseWeight rank = (rank + 1) * rank := by
    unfold staircaseWeight
    rw [show (∑ row : Fin (rank + 1), row.rev.val) =
        ∑ row : Fin (rank + 1), row.val by
      exact Equiv.sum_comp Fin.revPerm
        (fun row : Fin (rank + 1) => row.val)]
    have hfin : (∑ row : Fin (rank + 1), row.val) =
        ∑ value ∈ Finset.range (rank + 1), value := by
      simpa using (Fin.sum_univ_eq_sum_range (n := rank + 1)
        (fun value : ℕ => value))
    rw [hfin]
    have hsum := Finset.sum_range_id_mul_two (rank + 1)
    calc
      2 * (∑ value ∈ Finset.range (rank + 1), value) =
          (∑ value ∈ Finset.range (rank + 1), value) * 2 := by omega
      _ = (rank + 1) * ((rank + 1) - 1) := hsum
      _ = (rank + 1) * rank := by rw [Nat.add_sub_cancel]
  have hstaircaseReal :
      2 * (staircaseWeight rank : ℝ) =
        ((rank + 1) : ℝ) * rank := by
    exact_mod_cast hstaircaseNat
  unfold fixedRankExponent
  have hcastSub : (((rank + 1) - 1 : ℕ) : ℝ) = rank := by
    norm_num
  rw [hcastSub]
  push_cast
  congr 1
  nlinarith

theorem pairScale_product
    (rank : ℕ) (scale : ℝ) :
    (∏ row : Fin (rank + 1), ∏ _next ∈ Finset.Ioi row, scale) =
      scale ^ staircaseWeight rank := by
  unfold staircaseWeight
  simp only [Finset.prod_const]
  calc
    (∏ row : Fin (rank + 1), scale ^ (Finset.Ioi row).card) =
        ∏ row : Fin (rank + 1), scale ^ row.rev.val := by
      apply Finset.prod_congr rfl
      intro row hrow
      congr 1
      rw [Fin.card_Ioi]
      simp [Fin.rev]
    _ = scale ^ ∑ row : Fin (rank + 1), row.rev.val := by
      exact Finset.prod_pow_eq_pow_sum Finset.univ
        (fun row : Fin (rank + 1) => row.rev.val) scale

noncomputable def regevCorrectedPair
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (row next : Fin (rank + 1)) : ℝ :=
  regevCenteredRow shape row - regevCenteredRow shape next +
    ((next.val : ℝ) - row.val) /
      Real.sqrt ((size : ℝ) / (rank + 1 : ℝ))

theorem matsumoto_pair_product_centered
    {rank size : ℕ} (shape : BoundedPartition rank size)
    (hsize : 1 ≤ size) :
    (∏ row : Fin (rank + 1), ∏ next ∈ Finset.Ioi row,
        (((shape.1 row).val : ℝ) - (shape.1 next).val +
          (next.val : ℝ) - row.val)) =
      Real.sqrt ((size : ℝ) / (rank + 1 : ℝ)) ^
          staircaseWeight rank *
        ∏ row : Fin (rank + 1), ∏ next ∈ Finset.Ioi row,
          regevCorrectedPair shape row next := by
  have hscale : Real.sqrt ((size : ℝ) / (rank + 1 : ℝ)) ≠ 0 := by
    positivity
  calc
    (∏ row : Fin (rank + 1), ∏ next ∈ Finset.Ioi row,
        (((shape.1 row).val : ℝ) - (shape.1 next).val +
          (next.val : ℝ) - row.val)) =
      ∏ row : Fin (rank + 1), ∏ next ∈ Finset.Ioi row,
        Real.sqrt ((size : ℝ) / (rank + 1 : ℝ)) *
          regevCorrectedPair shape row next := by
      apply Finset.prod_congr rfl
      intro row hrow
      apply Finset.prod_congr rfl
      intro next hnext
      rw [matsumoto_pair_factor_centered shape hsize]
      unfold regevCorrectedPair
      field_simp
      ring
    _ = (∏ row : Fin (rank + 1),
          ∏ _next ∈ Finset.Ioi row,
            Real.sqrt ((size : ℝ) / (rank + 1 : ℝ))) *
        ∏ row : Fin (rank + 1), ∏ next ∈ Finset.Ioi row,
          regevCorrectedPair shape row next := by
      simp_rw [Finset.prod_mul_distrib]
    _ = _ := by rw [pairScale_product]

theorem regevCorrectedPair_tendsto
    {rank : ℕ} (sizes : ℕ → ℕ)
    (shapes : ∀ index, BoundedPartition rank (sizes index))
    (limitRows : Fin (rank + 1) → ℝ)
    (hsizes : Filter.Tendsto sizes Filter.atTop Filter.atTop)
    (hcentered : ∀ row,
      Filter.Tendsto (fun index => regevCenteredRow (shapes index) row)
        Filter.atTop (nhds (limitRows row)))
    (row next : Fin (rank + 1)) :
    Filter.Tendsto
        (fun index => regevCorrectedPair (shapes index) row next)
      Filter.atTop (nhds (limitRows row - limitRows next)) := by
  have hsizesReal : Filter.Tendsto (fun index => (sizes index : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hsizes
  have hdimensionPos : (0 : ℝ) < rank + 1 := by positivity
  have hscaled : Filter.Tendsto
      (fun index => (sizes index : ℝ) / (rank + 1 : ℝ))
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const hdimensionPos hsizesReal
  have hsqrt : Filter.Tendsto
      (fun index => Real.sqrt ((sizes index : ℝ) / (rank + 1 : ℝ)))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp hscaled
  have hcorrection : Filter.Tendsto
      (fun index => ((next.val : ℝ) - row.val) /
        Real.sqrt ((sizes index : ℝ) / (rank + 1 : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.comp hsqrt).const_mul
        ((next.val : ℝ) - row.val)
  unfold regevCorrectedPair
  simpa using ((hcentered row).sub (hcentered next)).add hcorrection

theorem regevCorrectedPair_product_tendsto
    {rank : ℕ} (sizes : ℕ → ℕ)
    (shapes : ∀ index, BoundedPartition rank (sizes index))
    (limitRows : Fin (rank + 1) → ℝ)
    (hsizes : Filter.Tendsto sizes Filter.atTop Filter.atTop)
    (hcentered : ∀ row,
      Filter.Tendsto (fun index => regevCenteredRow (shapes index) row)
        Filter.atTop (nhds (limitRows row))) :
    Filter.Tendsto
        (fun index =>
          ∏ row : Fin (rank + 1), ∏ next ∈ Finset.Ioi row,
            regevCorrectedPair (shapes index) row next)
      Filter.atTop
        (nhds (∏ row : Fin (rank + 1),
          ∏ next ∈ Finset.Ioi row,
            (limitRows row - limitRows next))) := by
  apply tendsto_finsetProd Finset.univ
  intro row hrow
  apply tendsto_finsetProd (Finset.Ioi row)
  intro next hnext
  exact regevCorrectedPair_tendsto
    sizes shapes limitRows hsizes hcentered row next

theorem matsumoto_pair_normalized_tendsto
    {rank : ℕ} (sizes : ℕ → ℕ)
    (shapes : ∀ index, BoundedPartition rank (sizes index))
    (limitRows : Fin (rank + 1) → ℝ)
    (hsizes : Filter.Tendsto sizes Filter.atTop Filter.atTop)
    (hcentered : ∀ row,
      Filter.Tendsto (fun index => regevCenteredRow (shapes index) row)
        Filter.atTop (nhds (limitRows row))) :
    Filter.Tendsto
        (fun index =>
          matsumotoPairProduct (shapes index) /
            (((sizes index : ℝ) / (rank + 1 : ℝ)) ^
              fixedRankExponent (rank + 1)))
      Filter.atTop
        (nhds (∏ row : Fin (rank + 1),
          ∏ next ∈ Finset.Ioi row,
            (limitRows row - limitRows next))) := by
  apply (regevCorrectedPair_product_tendsto
    sizes shapes limitRows hsizes hcentered).congr'
  have heventSize : ∀ᶠ index in Filter.atTop, 1 ≤ sizes index :=
    hsizes.eventually (Filter.eventually_ge_atTop 1)
  filter_upwards [heventSize] with index hsize
  unfold matsumotoPairProduct
  rw [matsumoto_pair_product_centered (shapes index) hsize,
    pairScale_power_eq_fixedRankExponent rank (sizes index) hsize]
  have hdenominator :
      ((sizes index : ℝ) / (rank + 1 : ℝ)) ^
          fixedRankExponent (rank + 1) ≠ 0 := by positivity
  field_simp

end FibonacciRibbonKernel
