import FibonacciRibbonKernel.RegevPairScaling
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace FibonacciRibbonKernel

open Filter

noncomputable def entropyRemainder : ℝ → ℝ :=
  ((fun value : ℝ => 1 + value) *
      (fun value : ℝ => Real.log (1 + value))) - id

theorem hasDerivAt_entropyRemainder
  (value : ℝ) (hvalue : 1 + value ≠ 0) :
    HasDerivAt entropyRemainder (Real.log (1 + value)) value := by
  have hlinear : HasDerivAt (fun current : ℝ => 1 + current) 1 value := by
    simpa using (hasDerivAt_id value).const_add (1 : ℝ)
  have hlog := hlinear.log hvalue
  have hproduct := hlinear.mul hlog
  have hfull := hproduct.sub (hasDerivAt_id value)
  unfold entropyRemainder
  convert! hfull using 1
  field_simp [hvalue]
  ring

theorem tendsto_log_one_add_div_two_mul :
    Tendsto (fun value : ℝ => Real.log (1 + value) / (2 * value))
      (nhdsWithin 0 {0}ᶜ) (nhds (1 / 2 : ℝ)) := by
  have hbound : ∀ᶠ value : ℝ in nhdsWithin 0 {0}ᶜ,
      value ∈ Set.Ioo (-1 / 2 : ℝ) (1 / 2 : ℝ) :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Ioo_mem_nhds (by norm_num : (-1 / 2 : ℝ) < 0)
        (by norm_num : (0 : ℝ) < 1 / 2))
  have hnumeratorDerivative : ∀ᶠ value : ℝ in nhdsWithin 0 {0}ᶜ,
      HasDerivAt (fun current : ℝ => Real.log (1 + current))
        (1 + value)⁻¹ value := by
    filter_upwards [hbound] with value hvalue
    have hlinear : HasDerivAt (fun current : ℝ => 1 + current) 1 value := by
      simpa using (hasDerivAt_id value).const_add (1 : ℝ)
    simpa [one_div] using hlinear.log (by nlinarith [hvalue.1])
  have hdenominatorDerivative : ∀ᶠ value : ℝ in nhdsWithin 0 {0}ᶜ,
      HasDerivAt (fun current : ℝ => 2 * current) 2 value := by
    exact Filter.Eventually.of_forall fun value =>
      by simpa using (hasDerivAt_id value).const_mul 2
  have hdenominatorNonzero : ∀ᶠ _value : ℝ in nhdsWithin 0 {0}ᶜ,
      (2 : ℝ) ≠ 0 := Filter.Eventually.of_forall fun _ => by norm_num
  have hnumeratorZero : Tendsto
      (fun value : ℝ => Real.log (1 + value)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have hadd : Tendsto (fun value : ℝ => 1 + value)
        (nhds 0) (nhds 1) := by
      have hconst : Tendsto (fun _ : ℝ => (1 : ℝ))
          (nhds 0) (nhds 1) := tendsto_const_nhds
      have hid : Tendsto (fun value : ℝ => value)
          (nhds 0) (nhds 0) := tendsto_id
      simpa only [Pi.add_apply, id_eq, add_zero] using hconst.add hid
    have hlog : Tendsto Real.log (nhds 1) (nhds 0) := by
      have hlogAt :=
        (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto
      simpa using hlogAt
    exact (hlog.comp hadd).mono_left nhdsWithin_le_nhds
  have hdenominatorZero : Tendsto (fun value : ℝ => 2 * value)
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have hconst : Tendsto (fun _ : ℝ => (2 : ℝ))
        (nhds 0) (nhds 2) := tendsto_const_nhds
    have hid : Tendsto (fun value : ℝ => value)
        (nhds 0) (nhds 0) := tendsto_id
    convert (hconst.mul hid).mono_left nhdsWithin_le_nhds using 1
    norm_num
  have hderivativeRatio : Tendsto
      (fun value : ℝ => (1 + value)⁻¹ / 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (1 / 2 : ℝ)) := by
    have hadd : Tendsto (fun value : ℝ => 1 + value)
        (nhds 0) (nhds 1) := by
      have hconst : Tendsto (fun _ : ℝ => (1 : ℝ))
          (nhds 0) (nhds 1) := tendsto_const_nhds
      have hid : Tendsto (fun value : ℝ => value)
          (nhds 0) (nhds 0) := tendsto_id
      simpa only [Pi.add_apply, id_eq, add_zero] using hconst.add hid
    have hinv : Tendsto (fun value : ℝ => (1 + value)⁻¹)
        (nhdsWithin 0 {0}ᶜ) (nhds (1 : ℝ)) := by
      have hinvAt : Tendsto (fun value : ℝ => value⁻¹)
          (nhds 1) (nhds (1 : ℝ)) := by
        simpa using (continuousAt_inv₀
          (by norm_num : (1 : ℝ) ≠ 0)).tendsto
      exact (hinvAt.comp hadd).mono_left nhdsWithin_le_nhds
    simpa using hinv.div_const 2
  exact HasDerivAt.lhopital_zero_nhdsNE
    hnumeratorDerivative hdenominatorDerivative hdenominatorNonzero
    hnumeratorZero hdenominatorZero hderivativeRatio

theorem tendsto_entropyRemainder_div_sq :
    Tendsto (fun value : ℝ => entropyRemainder value / value ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (1 / 2 : ℝ)) := by
  have hbound : ∀ᶠ value : ℝ in nhdsWithin 0 {0}ᶜ,
      value ∈ Set.Ioo (-1 / 2 : ℝ) (1 / 2 : ℝ) :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Ioo_mem_nhds (by norm_num : (-1 / 2 : ℝ) < 0)
        (by norm_num : (0 : ℝ) < 1 / 2))
  have hnumeratorDerivative : ∀ᶠ value : ℝ in nhdsWithin 0 {0}ᶜ,
      HasDerivAt entropyRemainder (Real.log (1 + value)) value := by
    filter_upwards [hbound] with value hvalue
    exact hasDerivAt_entropyRemainder value (by nlinarith [hvalue.1])
  have hdenominatorDerivative : ∀ᶠ value : ℝ in nhdsWithin 0 {0}ᶜ,
      HasDerivAt (fun current : ℝ => current ^ 2) (2 * value) value := by
    exact Filter.Eventually.of_forall fun value => by
      simpa using (hasDerivAt_pow 2 value)
  have hdenominatorNonzero : ∀ᶠ value : ℝ in nhdsWithin 0 {0}ᶜ,
      (2 * value : ℝ) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with value hvalue
    exact mul_ne_zero (by norm_num) (by simpa using hvalue)
  have hnumeratorZero : Tendsto entropyRemainder
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have hadd : Tendsto (fun value : ℝ => 1 + value)
        (nhds 0) (nhds 1) := by
      have hconst : Tendsto (fun _ : ℝ => (1 : ℝ))
          (nhds 0) (nhds 1) := tendsto_const_nhds
      have hid : Tendsto (fun value : ℝ => value)
          (nhds 0) (nhds 0) := tendsto_id
      simpa only [Pi.add_apply, id_eq, add_zero] using hconst.add hid
    have hlog : Tendsto Real.log (nhds 1) (nhds 0) := by
      simpa using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto
    have hid : Tendsto (fun value : ℝ => value)
        (nhds 0) (nhds 0) := tendsto_id
    have hfull := (hadd.mul (hlog.comp hadd)).sub hid
    unfold entropyRemainder
    convert hfull.mono_left nhdsWithin_le_nhds using 1
    · funext current
      rfl
    · norm_num
  have hdenominatorZero : Tendsto (fun value : ℝ => value ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have hid : Tendsto (fun value : ℝ => value)
        (nhds 0) (nhds 0) := tendsto_id
    convert (hid.pow 2).mono_left nhdsWithin_le_nhds using 1
    norm_num
  exact HasDerivAt.lhopital_zero_nhdsNE
    hnumeratorDerivative hdenominatorDerivative hdenominatorNonzero
    hnumeratorZero hdenominatorZero tendsto_log_one_add_div_two_mul

noncomputable def entropyQuadratic (value : ℝ) : ℝ :=
  if value = 0 then 1 / 2 else entropyRemainder value / value ^ 2

theorem tendsto_entropyQuadratic :
    Tendsto entropyQuadratic (nhds 0) (nhds (1 / 2 : ℝ)) := by
  rw [← pure_sup_nhdsNE (0 : ℝ), tendsto_sup]
  constructor
  · convert tendsto_pure_nhds entropyQuadratic (0 : ℝ) using 1
    simp [entropyQuadratic]
  · apply tendsto_entropyRemainder_div_sq.congr'
    filter_upwards [self_mem_nhdsWithin] with value hvalue
    simp [entropyQuadratic, by simpa using hvalue]

theorem tendsto_scaled_entropyRemainder
    {scale deviation : ℕ → ℝ} {limit : ℝ}
    (hdeviation : Tendsto deviation atTop (nhds 0))
    (hscaledSquare : Tendsto
      (fun index => scale index * deviation index ^ 2)
      atTop (nhds (limit ^ 2))) :
    Tendsto (fun index => scale index * entropyRemainder (deviation index))
      atTop (nhds (limit ^ 2 / 2)) := by
  have hquadratic := tendsto_entropyQuadratic.comp hdeviation
  have hproduct := hscaledSquare.mul hquadratic
  have hproduct' : Tendsto
      (fun index => scale index * deviation index ^ 2 *
        (entropyQuadratic ∘ deviation) index)
      atTop (nhds (limit ^ 2 / 2)) := by
    convert hproduct using 1
    norm_num [div_eq_mul_inv]
  apply hproduct'.congr'
  filter_upwards [] with index
  by_cases hzero : deviation index = 0
  · simp [hzero, entropyQuadratic, entropyRemainder]
  · simp [entropyQuadratic, hzero]
    field_simp

end FibonacciRibbonKernel
