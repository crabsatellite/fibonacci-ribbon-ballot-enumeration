import FibonacciRibbonKernel.StableInvolutions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.Field

namespace FibonacciRibbonKernel

theorem involutionNumber_pos (size : ℕ) : 0 < involutionNumber size := by
  induction size with
  | zero => simp [involutionNumber_zero]
  | succ size ih =>
      rw [involutionNumber_succ]
      omega

noncomputable def involutionRatio (size : ℕ) : ℝ :=
  (involutionNumber size : ℝ) / involutionNumber (size - 1)

theorem involutionRatio_pos (size : ℕ) : 0 < involutionRatio size := by
  unfold involutionRatio
  apply div_pos
  · exact_mod_cast involutionNumber_pos size
  · exact_mod_cast involutionNumber_pos (size - 1)

theorem involutionRatio_succ (size : ℕ) (hsize : 1 ≤ size) :
    involutionRatio (size + 1) = 1 + size / involutionRatio size := by
  unfold involutionRatio
  rw [involutionNumber_succ]
  have hprev : (involutionNumber (size - 1) : ℝ) ≠ 0 := by
    exact_mod_cast (involutionNumber_pos (size - 1)).ne'
  have hcurrent : (involutionNumber size : ℝ) ≠ 0 := by
    exact_mod_cast (involutionNumber_pos size).ne'
  push_cast
  field_simp

theorem sqrt_nat_pos {size : ℕ} (hsize : 0 < size) :
    0 < Real.sqrt (size : ℝ) := by
  positivity

theorem involutionRatio_bounds
    (size : ℕ) (hsize : 1 ≤ size) :
    Real.sqrt (size : ℝ) ≤ involutionRatio size ∧
      involutionRatio size ≤ Real.sqrt (size : ℝ) + 1 := by
  induction size using Nat.strong_induction_on with
  | h size ih =>
      cases size with
      | zero => omega
      | succ previous =>
          by_cases hprevious : previous = 0
          · subst previous
            norm_num [involutionRatio, involutionNumber_zero, involutionNumber_one]
          · have hpreviousPos : 0 < previous := Nat.pos_of_ne_zero hprevious
            have hpreviousOne : 1 ≤ previous := hpreviousPos
            have hbounds := ih previous (by omega) hpreviousOne
            have hrec := involutionRatio_succ previous hpreviousOne
            let x := Real.sqrt (previous : ℝ)
            let y := Real.sqrt ((previous + 1 : ℕ) : ℝ)
            have hxpos : 0 < x := sqrt_nat_pos hpreviousPos
            have hypos : 0 < y := by
              dsimp [y]
              exact sqrt_nat_pos (size := previous + 1) (by omega)
            have hxSq : x ^ 2 = (previous : ℝ) := by
              dsimp [x]
              rw [Real.sq_sqrt]
              positivity
            have hySq : y ^ 2 = ((previous + 1 : ℕ) : ℝ) := by
              dsimp [y]
              rw [Real.sq_sqrt]
              positivity
            norm_num at hySq
            have hratioPos := involutionRatio_pos previous
            have hupperFraction :
                (previous : ℝ) / involutionRatio previous ≤ x := by
              apply (div_le_iff₀ hratioPos).mpr
              have hlower := hbounds.1
              dsimp [x] at hlower ⊢
              nlinarith
            have hlowerFraction :
                (previous : ℝ) / (x + 1) ≤
                  (previous : ℝ) / involutionRatio previous := by
              apply div_le_div_of_nonneg_left (by positivity) hratioPos
              exact hbounds.2
            have hrootStep : x ≤ y := by
              apply Real.sqrt_le_sqrt
              norm_num
            have hlowerRoot : y ≤ 1 + (previous : ℝ) / (x + 1) := by
              have hrightPos : 0 ≤ 1 + (previous : ℝ) / (x + 1) := by positivity
              have hsquare : y ^ 2 ≤
                  (1 + (previous : ℝ) / (x + 1)) ^ 2 := by
                rw [hySq, ← hxSq]
                field_simp
                nlinarith [sq_nonneg x]
              nlinarith
            constructor
            · rw [hrec]
              exact hlowerRoot.trans (by
                simpa [add_comm] using add_le_add_left hlowerFraction 1)
            · rw [hrec]
              have h := (add_le_add_left hupperFraction 1).trans
                (add_le_add_left hrootStep 1)
              simpa [add_comm, y] using h

noncomputable def involutionFixedPointProbability (size : ℕ) : ℝ :=
  (involutionNumber (size - 1) : ℝ) / involutionNumber size

theorem involutionFixedPointProbability_eq_inv_ratio
    (size : ℕ) :
    involutionFixedPointProbability size = (involutionRatio size)⁻¹ := by
  unfold involutionFixedPointProbability involutionRatio
  have hcurrent : (involutionNumber size : ℝ) ≠ 0 := by
    exact_mod_cast (involutionNumber_pos size).ne'
  have hprevious : (involutionNumber (size - 1) : ℝ) ≠ 0 := by
    exact_mod_cast (involutionNumber_pos (size - 1)).ne'
  field_simp

theorem tendsto_involutionFixedPointProbability_zero :
    Filter.Tendsto involutionFixedPointProbability Filter.atTop (nhds 0) := by
  have hsqrtTop : Filter.Tendsto
      (fun size : ℕ => Real.sqrt (size : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinvSqrt : Filter.Tendsto
      (fun size : ℕ => (Real.sqrt (size : ℝ))⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hsqrtTop
  apply squeeze_zero'
    (f := involutionFixedPointProbability)
    (g := fun size : ℕ => (Real.sqrt (size : ℝ))⁻¹)
  · exact Filter.Eventually.of_forall fun size => by
      unfold involutionFixedPointProbability
      positivity
  · filter_upwards [Filter.eventually_atTop.2 ⟨1, fun _ h => h⟩] with size hsize
    rw [involutionFixedPointProbability_eq_inv_ratio size]
    have hbound := (involutionRatio_bounds size hsize).1
    have hsqrtPos := sqrt_nat_pos (show 0 < size by omega)
    simpa [one_div] using one_div_le_one_div_of_le hsqrtPos hbound
  · exact hinvSqrt

noncomputable def scaledTwoStepInvolutionRatio (size : ℕ) : ℝ :=
  (size : ℝ) * involutionNumber (size - 2) / involutionNumber size

theorem scaledTwoStepInvolutionRatio_eq
    (size : ℕ) (hsize : 2 ≤ size) :
    scaledTwoStepInvolutionRatio size =
      ((size : ℝ) / ((size : ℝ) - 1)) *
        (1 - involutionFixedPointProbability size) := by
  unfold scaledTwoStepInvolutionRatio involutionFixedPointProbability
  have hrec := involutionNumber_succ (size - 1)
  have hsizeEq : size - 1 + 1 = size := by omega
  have hsub : size - 1 - 1 = size - 2 := by omega
  rw [hsizeEq, hsub] at hrec
  have hcurrent : (involutionNumber size : ℝ) ≠ 0 := by
    exact_mod_cast (involutionNumber_pos size).ne'
  have hdenom : (size : ℝ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (show size ≠ 1 by omega))
  have hrecR : (involutionNumber size : ℝ) =
      involutionNumber (size - 1) +
        ((size : ℝ) - 1) * involutionNumber (size - 2) := by
    have hcast : (involutionNumber size : ℝ) =
        involutionNumber (size - 1) +
          (size - 1 : ℕ) * involutionNumber (size - 2) := by
      exact_mod_cast hrec
    simpa [Nat.cast_sub (show 1 ≤ size by omega)] using hcast
  field_simp
  linear_combination -hrecR

theorem tendsto_scaledTwoStepInvolutionRatio_one :
    Filter.Tendsto scaledTwoStepInvolutionRatio Filter.atTop (nhds 1) := by
  have hlinear : Filter.Tendsto
      (fun size : ℕ => (size : ℝ) / ((size : ℝ) - 1))
      Filter.atTop (nhds 1) := by
    simpa [sub_eq_add_neg] using
      (tendsto_natCast_div_add_atTop (-1 : ℝ))
  have hfixed : Filter.Tendsto
      (fun size : ℕ => 1 - involutionFixedPointProbability size)
      Filter.atTop (nhds 1) := by
    convert tendsto_const_nhds.sub tendsto_involutionFixedPointProbability_zero using 1
    norm_num
  have hproduct := hlinear.mul hfixed
  have hproduct' : Filter.Tendsto
      (fun size : ℕ => ((size : ℝ) / ((size : ℝ) - 1)) *
        (1 - involutionFixedPointProbability size))
      Filter.atTop (nhds 1) := by
    simpa using hproduct
  apply Filter.Tendsto.congr' _ hproduct'
  filter_upwards [Filter.eventually_atTop.2 ⟨2, fun _ h => h⟩] with size hsize
  exact (scaledTwoStepInvolutionRatio_eq size hsize).symm

end FibonacciRibbonKernel
