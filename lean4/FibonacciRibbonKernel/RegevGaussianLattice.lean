import FibonacciRibbonKernel.RegevQuadraticSum
import FibonacciRibbonKernel.RegevGaussianInteger

namespace FibonacciRibbonKernel

open Filter MeasureTheory Set
open scoped Classical Topology

/-- A mesh-independent bound for the normalized total mass of the sampled
one-dimensional Gaussian.  This is the quantitative input used later to make
the polynomial-times-Gaussian lattice tails uniformly small. -/
theorem regevScaledGaussianLine_total_bound
    {coefficient : ℝ} (hcoefficient : 0 < coefficient)
    {mesh : ℕ} (hmesh : 1 ≤ mesh) :
    (∑' index : ℤ, regevScaledGaussianLine coefficient mesh index) /
        mesh ≤
      2 + 2 * Real.sqrt (Real.pi / coefficient) := by
  let sampled : ℝ → ℝ := regevScaledGaussianReal coefficient mesh
  have hmeshReal : (0 : ℝ) < mesh := by exact_mod_cast hmesh
  have hanti : AntitoneOn sampled (Ici 0) :=
    antitoneOn_regevScaledGaussianReal hcoefficient hmesh
  have hintegrable : Integrable sampled :=
    integrable_regevScaledGaussianReal hcoefficient hmesh
  have hnat : Summable (fun index : ℕ => sampled index) :=
    summable_nat_regevScaledGaussianReal hcoefficient hmesh
  have hnatBound := hanti.tsum_le_integral hintegrable.integrableOn
    (fun _ _ => (Real.exp_pos _).le)
  have hwholeIntegral :
      (∫ x : ℝ, sampled x) =
        (mesh : ℝ) * Real.sqrt (Real.pi / coefficient) := by
    have hscale := Measure.integral_comp_div
      (fun x : ℝ => Real.exp (-coefficient * x ^ 2)) (mesh : ℝ)
    rw [integral_gaussian coefficient] at hscale
    simpa [sampled, regevScaledGaussianReal, abs_of_pos hmeshReal,
      smul_eq_mul] using hscale
  have hhalfIntegral :
      (∫ x in Ioi (0 : ℝ), sampled x) ≤
        (mesh : ℝ) * Real.sqrt (Real.pi / coefficient) := by
    rw [← hwholeIntegral]
    exact setIntegral_le_integral hintegrable
      (Eventually.of_forall fun _ => (Real.exp_pos _).le)
  have hnatCoarse :
      (∑' index : ℕ, sampled index) ≤
        1 + (mesh : ℝ) * Real.sqrt (Real.pi / coefficient) := by
    calc
      (∑' index : ℕ, sampled index) ≤
          sampled 0 + ∫ x in Ioi (0 : ℝ), sampled x := hnatBound
      _ ≤ 1 + (mesh : ℝ) * Real.sqrt (Real.pi / coefficient) := by
        simpa [sampled, regevScaledGaussianReal] using
          add_le_add_left hhalfIntegral 1
  have hnegative : Summable (fun index : ℕ =>
      regevScaledGaussianLine coefficient mesh (-index)) := by
    refine hnat.congr (fun index => ?_)
    simpa [regevScaledGaussianLine, sampled] using
      (regevScaledGaussianReal_neg coefficient mesh (index : ℝ)).symm
  have hintEq := Summable.tsum_of_nat_of_neg hnat hnegative
  have hpositiveFunction :
      (fun index : ℕ =>
        regevScaledGaussianLine coefficient mesh index) =
        (fun index : ℕ => sampled index) := by
    rfl
  have hnegativeFunction :
      (fun index : ℕ =>
        regevScaledGaussianLine coefficient mesh (-index)) =
        (fun index : ℕ => sampled index) := by
    funext index
    simpa [regevScaledGaussianLine, sampled] using
      regevScaledGaussianReal_neg coefficient mesh (index : ℝ)
  have hlineEq :
      (∑' index : ℤ, regevScaledGaussianLine coefficient mesh index) =
        2 * ∑' index : ℕ, sampled index - 1 := by
    rw [hpositiveFunction, hnegativeFunction] at hintEq
    calc
      (∑' index : ℤ, regevScaledGaussianLine coefficient mesh index) =
          (∑' index : ℕ, sampled index) +
            (∑' index : ℕ, sampled index) -
              regevScaledGaussianLine coefficient mesh 0 := hintEq
      _ = 2 * ∑' index : ℕ, sampled index - 1 := by
        rw [show regevScaledGaussianLine coefficient mesh 0 = 1 by
          simp [regevScaledGaussianLine, regevScaledGaussianReal]]
        ring
  have hlineCoarse :
      (∑' index : ℤ, regevScaledGaussianLine coefficient mesh index) ≤
        2 * (1 + (mesh : ℝ) *
          Real.sqrt (Real.pi / coefficient)) := by
    rw [hlineEq]
    nlinarith
  rw [div_le_iff₀ hmeshReal]
  calc
    (∑' index : ℤ, regevScaledGaussianLine coefficient mesh index) ≤
        2 * (1 + (mesh : ℝ) *
          Real.sqrt (Real.pi / coefficient)) := hlineCoarse
    _ ≤ (2 + 2 * Real.sqrt (Real.pi / coefficient)) * mesh := by
      have hmeshOne : (1 : ℝ) ≤ mesh := by exact_mod_cast hmesh
      nlinarith [Real.sqrt_nonneg (Real.pi / coefficient)]

end FibonacciRibbonKernel
