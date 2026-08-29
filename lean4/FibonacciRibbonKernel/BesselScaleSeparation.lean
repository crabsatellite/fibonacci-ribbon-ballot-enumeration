import FibonacciRibbonKernel.BesselSpectralRecurrence

namespace FibonacciRibbonKernel

def besselPositiveScaleIndex (degree : ℕ) : Fin (degree + 1) :=
  ⟨0, by omega⟩

def besselNegativeScaleIndex (degree : ℕ) : Fin (degree + 1) :=
  ⟨degree, by omega⟩

@[simp] theorem besselScaleEigenvalue_positiveIndex (degree : ℕ) :
    besselScaleEigenvalue degree (besselPositiveScaleIndex degree) = 2 * degree := by
  unfold besselScaleEigenvalue besselPositiveScaleIndex
  simp

@[simp] theorem besselScaleEigenvalue_negativeIndex (degree : ℕ) :
    besselScaleEigenvalue degree (besselNegativeScaleIndex degree) = -(2 * degree) := by
  unfold besselScaleEigenvalue besselNegativeScaleIndex
  push_cast
  ring

@[simp] theorem oddBesselScaleEigenvalue_positiveIndex (degree : ℕ) :
    oddBesselScaleEigenvalue degree (besselPositiveScaleIndex degree) =
      2 * degree + 1 := by
  unfold oddBesselScaleEigenvalue besselPositiveScaleIndex
  simp

@[simp] theorem oddBesselScaleEigenvalue_negativeIndex (degree : ℕ) :
    oddBesselScaleEigenvalue degree (besselNegativeScaleIndex degree) =
      1 - 2 * degree := by
  unfold oddBesselScaleEigenvalue besselNegativeScaleIndex
  push_cast
  ring

theorem abs_besselScaleEigenvalue_le
    (degree : ℕ) (scaleIndex : Fin (degree + 1)) :
    |besselScaleEigenvalue degree scaleIndex| ≤ (2 * degree : ℚ) := by
  rw [abs_le]
  unfold besselScaleEigenvalue
  have hindex : (scaleIndex.val : ℚ) ≤ degree := by
    exact_mod_cast (Nat.le_of_lt_succ scaleIndex.isLt)
  have hindexNonneg : (0 : ℚ) ≤ scaleIndex.val := by positivity
  constructor <;> linarith

theorem abs_besselScaleEigenvalue_lt_of_internal
    (degree : ℕ) (scaleIndex : Fin (degree + 1))
    (hpositive : 0 < scaleIndex.val) (hbelow : scaleIndex.val < degree) :
    |besselScaleEigenvalue degree scaleIndex| < (2 * degree : ℚ) := by
  rw [abs_lt]
  unfold besselScaleEigenvalue
  have hpositiveQ : (0 : ℚ) < scaleIndex.val := by exact_mod_cast hpositive
  have hbelowQ : (scaleIndex.val : ℚ) < degree := by exact_mod_cast hbelow
  constructor <;> linarith

theorem abs_besselScaleEigenvalue_eq_top_iff
    (degree : ℕ) (scaleIndex : Fin (degree + 1)) :
    |besselScaleEigenvalue degree scaleIndex| = (2 * degree : ℚ) ↔
      scaleIndex.val = 0 ∨ scaleIndex.val = degree := by
  constructor
  · intro heq
    by_contra hends
    push Not at hends
    have hinterior : scaleIndex.val < degree := by omega
    have hlt := abs_besselScaleEigenvalue_lt_of_internal degree scaleIndex
      (Nat.zero_lt_of_ne_zero hends.1) hinterior
    linarith
  · rintro (hzero | htop)
    · have hindex : scaleIndex = besselPositiveScaleIndex degree := by
        apply Fin.ext
        exact hzero
      rw [hindex, besselScaleEigenvalue_positiveIndex]
      simp
    · have hindex : scaleIndex = besselNegativeScaleIndex degree := by
        apply Fin.ext
        exact htop
      rw [hindex, besselScaleEigenvalue_negativeIndex]
      simp

theorem abs_oddBesselScaleEigenvalue_lt_positive_of_nonzero
    (degree : ℕ) (scaleIndex : Fin (degree + 1))
    (hscale : scaleIndex.val ≠ 0) :
    |oddBesselScaleEigenvalue degree scaleIndex| < (2 * degree + 1 : ℚ) := by
  rw [abs_lt]
  unfold oddBesselScaleEigenvalue
  have hpositive : 0 < scaleIndex.val := Nat.zero_lt_of_ne_zero hscale
  have hpositiveQ : (0 : ℚ) < scaleIndex.val := by exact_mod_cast hpositive
  have hindexQ : (scaleIndex.val : ℚ) ≤ degree := by
    exact_mod_cast (Nat.le_of_lt_succ scaleIndex.isLt)
  constructor <;> linarith

theorem abs_oddBesselScaleEigenvalue_le
    (degree : ℕ) (scaleIndex : Fin (degree + 1)) :
    |oddBesselScaleEigenvalue degree scaleIndex| ≤ (2 * degree + 1 : ℚ) := by
  by_cases hscale : scaleIndex.val = 0
  · have hindex : scaleIndex = besselPositiveScaleIndex degree := by
      apply Fin.ext
      exact hscale
    rw [hindex, oddBesselScaleEigenvalue_positiveIndex]
    rw [abs_of_pos (by positivity)]
  · exact (abs_oddBesselScaleEigenvalue_lt_positive_of_nonzero
      degree scaleIndex hscale).le

theorem abs_oddBesselScaleEigenvalue_eq_top_iff
    (degree : ℕ) (scaleIndex : Fin (degree + 1)) :
    |oddBesselScaleEigenvalue degree scaleIndex| = (2 * degree + 1 : ℚ) ↔
      scaleIndex.val = 0 := by
  constructor
  · intro heq
    by_contra hscale
    have hlt := abs_oddBesselScaleEigenvalue_lt_positive_of_nonzero
      degree scaleIndex hscale
    linarith
  · intro hzero
    have hindex : scaleIndex = besselPositiveScaleIndex degree := by
      apply Fin.ext
      exact hzero
    rw [hindex, oddBesselScaleEigenvalue_positiveIndex]
    rw [abs_of_pos (by positivity)]

end FibonacciRibbonKernel
