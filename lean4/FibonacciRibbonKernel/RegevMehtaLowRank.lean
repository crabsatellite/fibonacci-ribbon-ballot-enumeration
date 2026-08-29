import FibonacciRibbonKernel.RegevMehtaGeometry

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set
open scoped Classical

theorem tracelessMehtaChamberIntegral_zero :
    tracelessMehtaChamberIntegral 0 = 1 := by
  unfold tracelessMehtaChamberIntegral regevChamber
  unfold regevGaussianKernel regevVandermonde
  have htrace : ∀ coordinates : Fin 0 → ℝ,
      tracelessExtend coordinates (0 : Fin 1) = 0 := by
    intro coordinates
    rw [show (0 : Fin 1) = Fin.last 0 by rfl]
    rw [tracelessExtend_last]
    simp
  have hchamber : {coordinates : Fin 0 → ℝ |
      Antitone (tracelessExtend coordinates)} = Set.univ := by
    ext coordinates
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    intro first second hle
    rw [Fin.eq_zero first, Fin.eq_zero second]
  rw [hchamber, setIntegral_univ]
  have hfun : (fun coordinates : Fin 0 → ℝ =>
      Real.exp (-(∑ row : Fin 1,
        tracelessExtend coordinates row ^ 2 / 2)) *
        ∏ row : Fin 1, ∏ next ∈ Finset.Ioi row,
          (tracelessExtend coordinates row -
            tracelessExtend coordinates next)) = fun _ => 1 := by
    funext coordinates
    simp [htrace]
  rw [hfun]
  have hvolume : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
    rw [Measure.volume_pi_eq_dirac (fun row : Fin 0 => Fin.elim0 row)]
    simp
  rw [integral_const, measureReal_def, hvolume]
  norm_num

theorem mehtaGammaProduct_one : mehtaGammaProduct 1 = 1 := by
  unfold mehtaGammaProduct
  norm_num
  have hgamma : Real.Gamma (3 / 2 : ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num)).ne'
  field_simp [hgamma]
  exact hgamma

theorem expectedRegevChamberIntegral_zero :
    expectedRegevChamberIntegral 0 =
      (Real.sqrt (2 * Real.pi))⁻¹ := by
  rw [expectedRegevChamberIntegral_formula]
  rw [mehtaGammaProduct_one]
  norm_num

theorem regevMehtaChamberEvaluation_zero :
    RegevMehtaChamberEvaluation 0 := by
  rw [RegevMehtaChamberEvaluation_iff]
  rw [tracelessMehtaChamberIntegral_zero,
    expectedRegevChamberIntegral_zero]
  field_simp
  norm_num

theorem integral_two_mul_exp_neg_sq_Ioi :
    (∫ x in Set.Ioi (0 : ℝ), 2 * x * Real.exp (-x ^ 2)) = 1 := by
  let primitive : ℝ → ℝ := fun x => -Real.exp (-x ^ 2)
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt primitive (2 * x * Real.exp (-x ^ 2)) x := by
    intro x hx
    dsimp only [primitive]
    convert! ((hasDerivAt_pow 2 x).const_mul (-1)).exp.const_mul (-1)
      using 1 <;> ring
  have hlimit : Tendsto primitive atTop (nhds 0) := by
    have hexp : Tendsto (fun x : ℝ => Real.exp (-1 * x ^ 2))
        atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp
        ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by norm_num))
    simpa [primitive] using hexp.neg
  have hintegral := integral_Ioi_of_hasDerivAt_of_nonneg'
    hderiv (fun x hx => by
      have hxpos : 0 < x := hx
      positivity) hlimit
  simpa [primitive] using hintegral

theorem integral_max_mul_exp_neg_sq :
    (∫ x : ℝ, max x 0 * Real.exp (-x ^ 2)) = 1 / 2 := by
  have hindicator : (fun x : ℝ => max x 0 * Real.exp (-x ^ 2)) =
      (Set.Ioi (0 : ℝ)).indicator
        (fun x => x * Real.exp (-x ^ 2)) := by
    funext x
    by_cases hx : 0 < x
    · simp [Set.indicator, hx, max_eq_left hx.le]
    · simp [Set.indicator, hx, max_eq_right (le_of_not_gt hx)]
  rw [hindicator, integral_indicator measurableSet_Ioi]
  have htwo := integral_two_mul_exp_neg_sq_Ioi
  have hrewrite :
      (∫ x in Set.Ioi (0 : ℝ), 2 * x * Real.exp (-x ^ 2)) =
        2 * ∫ x in Set.Ioi (0 : ℝ), x * Real.exp (-x ^ 2) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    ring
  rw [hrewrite] at htwo
  linarith

theorem integral_regevChamberExtension_one :
    (∫ coordinates : Fin 1 → ℝ,
      regevChamberExtension 1 coordinates) = 1 / (2 * Real.pi) := by
  let equivalence := MeasurableEquiv.funUnique (Fin 1) ℝ
  have hpreserving := MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ
  have hchange := hpreserving.integral_comp'
    (fun x : ℝ => regevChamberExtension 1 (equivalence.symm x))
  have hpointwise : (fun x : ℝ =>
      regevChamberExtension 1 (equivalence.symm x)) =
      fun x => (1 / (2 * Real.pi)) *
        (2 * max x 0 * Real.exp (-x ^ 2)) := by
    funext x
    let coordinates := equivalence.symm x
    have hcoordinate (row : Fin 1) : coordinates row = x := by
      rw [Fin.eq_zero row]
      rfl
    have htraceZero : tracelessExtend coordinates (0 : Fin 2) = x := by
      rw [show (0 : Fin 2) = (0 : Fin 1).castSucc by rfl]
      rw [tracelessExtend_castSucc, hcoordinate]
    have htraceOne : tracelessExtend coordinates (1 : Fin 2) = -x := by
      rw [show (1 : Fin 2) = Fin.last 1 by rfl]
      rw [tracelessExtend_last]
      simp [hcoordinate]
    have hgaussian : regevGaussianKernel 1 coordinates = Real.exp (-x ^ 2) := by
      unfold regevGaussianKernel
      rw [Fin.sum_univ_two, htraceZero, htraceOne]
      congr 1
      ring
    have hvandermonde : regevPositiveVandermonde 1 coordinates =
        2 * max x 0 := by
      unfold regevPositiveVandermonde
      have hinnerZero :
          (∏ next ∈ Finset.Ioi (0 : Fin 2),
            max (tracelessExtend coordinates 0 -
              tracelessExtend coordinates next) 0) = max (x - -x) 0 := by
        norm_num [htraceZero, htraceOne]
      have hinnerOne :
          (∏ next ∈ Finset.Ioi (1 : Fin 2),
            max (tracelessExtend coordinates 1 -
              tracelessExtend coordinates next) 0) = 1 := by
        rw [show Finset.Ioi (1 : Fin 2) = ∅ by
          ext next
          fin_cases next <;> simp]
        simp
      rw [Fin.prod_univ_two, hinnerZero, hinnerOne, mul_one]
      by_cases hx : 0 ≤ x
      · have htwox : 0 ≤ x - -x := by linarith
        rw [max_eq_left hx, max_eq_left htwox]
        ring
      · have hx' : x ≤ 0 := le_of_not_ge hx
        have htwox : x - -x ≤ 0 := by linarith
        rw [max_eq_right hx', max_eq_right htwox]
        ring
    unfold regevChamberExtension
    rw [hgaussian, hvandermonde]
    norm_num
    have hsqrtNe : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
    field_simp [hsqrtNe]
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Real.pi)]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [show (∫ coordinates : Fin 1 → ℝ,
      regevChamberExtension 1 coordinates) =
      ∫ coordinates : Fin 1 → ℝ,
        regevChamberExtension 1
          (equivalence.symm (equivalence coordinates)) by
    apply integral_congr_ae
    filter_upwards with coordinates
    rw [equivalence.symm_apply_apply]]
  change (∫ coordinates : Fin 1 → ℝ,
      regevChamberExtension 1
        (equivalence.symm (equivalence coordinates))) =
    (∫ x : ℝ, regevChamberExtension 1 (equivalence.symm x)) at hchange
  rw [hchange]
  rw [hpointwise]
  have hmax := integral_max_mul_exp_neg_sq
  have htwomax : (∫ x : ℝ, 2 * max x 0 * Real.exp (-x ^ 2)) = 1 := by
    rw [show (fun x : ℝ => 2 * max x 0 * Real.exp (-x ^ 2)) =
        fun x => 2 * (max x 0 * Real.exp (-x ^ 2)) by
      funext x
      ring]
    rw [integral_const_mul, hmax]
    norm_num
  calc
    (∫ x : ℝ, 1 / (2 * Real.pi) *
        (2 * max x 0 * Real.exp (-x ^ 2))) =
      1 / (2 * Real.pi) *
        ∫ x : ℝ, 2 * max x 0 * Real.exp (-x ^ 2) :=
      integral_const_mul (μ := volume) _ _
    _ = _ := by rw [htwomax, mul_one]

theorem regevMehtaChamberEvaluation_one :
    RegevMehtaChamberEvaluation 1 := by
  unfold RegevMehtaChamberEvaluation
  rw [← integral_regevChamberExtension]
  rw [integral_regevChamberExtension_one]
  rw [expectedRegevChamberIntegral_formula]
  unfold mehtaGammaProduct
  rw [Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_zero]
  norm_num
  have hgamma : Real.Gamma (3 / 2 : ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hthree : Real.Gamma (3 / 2 : ℝ) =
      (1 / 2 : ℝ) * Real.sqrt Real.pi := by
    have hrec := Real.Gamma_add_one (s := (1 / 2 : ℝ)) (by norm_num)
    rw [show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num] at hrec
    rw [Real.Gamma_one_half_eq] at hrec
    exact hrec
  rw [hthree]
  rw [← Real.sqrt_eq_rpow]
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp [hgamma]
  rw [show Real.sqrt (Real.pi * 2) =
      Real.sqrt Real.pi * Real.sqrt 2 by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Real.pi)]]
  calc
    Real.sqrt Real.pi * (Real.sqrt Real.pi * Real.sqrt 2) *
        Real.sqrt 2 =
      (Real.sqrt Real.pi * Real.sqrt Real.pi) *
        (Real.sqrt 2 * Real.sqrt 2) := by ring
    _ = Real.pi * 2 := by
      rw [Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ Real.pi),
        Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

end FibonacciRibbonKernel
