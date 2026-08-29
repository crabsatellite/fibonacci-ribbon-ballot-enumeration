import FibonacciRibbonKernel.SelbergHalfTarget

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped Classical

theorem selbergHalfWeight_complex_of_mem
    {alpha beta value : ℝ} (hvalue : value ∈ Set.Ioo (0 : ℝ) 1) :
    (value : ℂ) ^ ((alpha : ℂ) - 1) *
        (1 - (value : ℂ)) ^ ((beta : ℂ) - 1) =
      (selbergHalfWeight alpha beta value : ℂ) := by
  have hvaluePos : 0 < value := hvalue.1
  have honeSubPos : 0 < 1 - value := sub_pos.mpr hvalue.2
  unfold selbergHalfWeight
  rw [show (alpha : ℂ) - 1 = ((alpha - 1 : ℝ) : ℂ) by norm_cast,
    show 1 - (value : ℂ) = ((1 - value : ℝ) : ℂ) by norm_cast,
    show (beta : ℂ) - 1 = ((beta - 1 : ℝ) : ℂ) by norm_cast,
    ← Complex.ofReal_cpow hvaluePos.le,
    ← Complex.ofReal_cpow honeSubPos.le,
    ← Complex.ofReal_mul]

theorem integrableOn_selbergHalfWeight_Ioo
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    IntegrableOn (selbergHalfWeight alpha beta) (Set.Ioo (0 : ℝ) 1) := by
  have hcomplex := Complex.betaIntegral_convergent
    (u := (alpha : ℂ)) (v := (beta : ℂ))
    (by simpa using halpha) (by simpa using hbeta)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le
    (by norm_num : (0 : ℝ) ≤ 1)] at hcomplex
  have hcast : IntegrableOn
      (fun value : ℝ => (selbergHalfWeight alpha beta value : ℂ))
      (Set.Ioo 0 1) := by
    apply IntegrableOn.congr_fun hcomplex
    · intro value hvalue
      exact selbergHalfWeight_complex_of_mem hvalue
    · exact measurableSet_Ioo
  have hreal := hcast.re
  change Integrable (fun value : ℝ =>
    selbergHalfWeight alpha beta value) (volume.restrict (Set.Ioo 0 1))
  exact hreal

theorem integral_selbergHalfWeight_Ioo
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    (∫ value in Set.Ioo (0 : ℝ) 1,
      selbergHalfWeight alpha beta value) =
      Real.Gamma alpha * Real.Gamma beta /
        Real.Gamma (alpha + beta) := by
  have hcomplex := Complex.betaIntegral_eq_Gamma_mul_div
    (u := (alpha : ℂ)) (v := (beta : ℂ))
    (by simpa using halpha) (by simpa using hbeta)
  unfold Complex.betaIntegral at hcomplex
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hcomplex
  rw [← Measure.restrict_congr_set
    (Ioo_ae_eq_Ioc : Set.Ioo (0 : ℝ) 1 =ᵐ[volume] Set.Ioc 0 1)] at hcomplex
  have hpointwise :
      (fun value : ℝ =>
        (value : ℂ) ^ ((alpha : ℂ) - 1) *
          (1 - (value : ℂ)) ^ ((beta : ℂ) - 1)) =ᵐ[volume.restrict (Set.Ioo 0 1)]
      fun value : ℝ =>
        (selbergHalfWeight alpha beta value : ℂ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with value hvalue
    exact selbergHalfWeight_complex_of_mem hvalue
  rw [integral_congr_ae hpointwise] at hcomplex
  change (∫ value : ℝ,
      (selbergHalfWeight alpha beta value : ℂ)
        ∂volume.restrict (Set.Ioo 0 1)) = _ at hcomplex
  let realIntegral : ℝ :=
    ∫ value : ℝ, selbergHalfWeight alpha beta value
      ∂volume.restrict (Set.Ioo 0 1)
  have hcast :
      (∫ value : ℝ, (selbergHalfWeight alpha beta value : ℂ)
        ∂volume.restrict (Set.Ioo 0 1)) =
        (realIntegral : ℂ) := by
    dsimp only [realIntegral]
    exact integral_complex_ofReal
  rw [hcast] at hcomplex
  have hsum : (alpha : ℂ) + (beta : ℂ) = ((alpha + beta : ℝ) : ℂ) := by
    norm_cast
  rw [Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    hsum, Complex.Gamma_ofReal] at hcomplex
  have hreal := congrArg Complex.re hcomplex
  simpa [realIntegral] using hreal

theorem selbergUnitBox_one :
    selbergUnitBox 1 =
      (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Set.Ioo 0 1 := by
  ext coordinates
  simp [selbergUnitBox]

theorem standardMehtaChamber_one :
    standardMehtaChamber 1 = Set.univ := by
  ext coordinates
  simp only [standardMehtaChamber, Set.mem_setOf_eq,
    Set.mem_univ, iff_true]
  intro first second hle
  rw [Fin.eq_zero first, Fin.eq_zero second]

theorem orderedSelbergDomain_one :
    orderedSelbergDomain 1 =
      (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Set.Ioo 0 1 := by
  rw [orderedSelbergDomain, selbergUnitBox_one,
    standardMehtaChamber_one, inter_univ]

theorem selbergHalfIntegrand_one
    (alpha beta : ℝ) (coordinates : Fin 1 → ℝ) :
    selbergHalfIntegrand 1 alpha beta coordinates =
      selbergHalfWeight alpha beta (coordinates 0) := by
  unfold selbergHalfIntegrand standardMehtaVandermonde
  simp

theorem orderedSelbergHalfIntegral_one
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    orderedSelbergHalfIntegral 1 alpha beta =
      Real.Gamma alpha * Real.Gamma beta /
        Real.Gamma (alpha + beta) := by
  unfold orderedSelbergHalfIntegral
  rw [orderedSelbergDomain_one]
  have hchange :=
    (volume_preserving_funUnique (Fin 1) ℝ).setIntegral_preimage_emb
        (MeasurableEquiv.measurableEmbedding _)
        (selbergHalfWeight alpha beta) (Set.Ioo 0 1)
  calc
    (∫ coordinates in ⇑(MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹'
        Set.Ioo 0 1, selbergHalfIntegrand 1 alpha beta coordinates) =
      ∫ coordinates in ⇑(MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹'
        Set.Ioo 0 1,
        selbergHalfWeight alpha beta
          (MeasurableEquiv.funUnique (Fin 1) ℝ coordinates) := by
      apply setIntegral_congr_fun
      · exact (MeasurableEquiv.measurableEmbedding
          (MeasurableEquiv.funUnique (Fin 1) ℝ)).measurable measurableSet_Ioo
      · intro coordinates hcoordinates
        change selbergHalfIntegrand 1 alpha beta coordinates =
          selbergHalfWeight alpha beta (coordinates 0)
        exact selbergHalfIntegrand_one alpha beta coordinates
    _ = ∫ value in Set.Ioo (0 : ℝ) 1,
        selbergHalfWeight alpha beta value := hchange
    _ = _ := integral_selbergHalfWeight_Ioo halpha hbeta

theorem expectedOrderedSelbergHalfIntegral_one
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    expectedOrderedSelbergHalfIntegral 1 alpha beta =
      Real.Gamma alpha * Real.Gamma beta /
        Real.Gamma (alpha + beta) := by
  unfold expectedOrderedSelbergHalfIntegral selbergHalfGammaProduct
  rw [Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num
  have hgamma : Real.Gamma (3 / 2 : ℝ) ≠ 0 := by positivity
  field_simp [hgamma]

theorem orderedSelbergHalfEvaluation_one
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    OrderedSelbergHalfEvaluation 1 alpha beta := by
  unfold OrderedSelbergHalfEvaluation
  rw [orderedSelbergHalfIntegral_one halpha hbeta,
    expectedOrderedSelbergHalfIntegral_one halpha hbeta]

end FibonacciRibbonKernel
