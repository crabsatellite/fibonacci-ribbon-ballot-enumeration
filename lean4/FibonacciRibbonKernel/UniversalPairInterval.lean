import FibonacciRibbonKernel.GeneralPairCoordinates

namespace FibonacciRibbonKernel

open PowerSeries

noncomputable def factorialConvolutionTerm (degree low : ℕ) : ℚ :=
  reciprocalFactorialInt (low : ℤ) *
    reciprocalFactorialInt ((degree : ℤ) - (low : ℤ))

noncomputable def universalPairLower (gap degree : ℕ) : ℕ :=
  max ((degree + gap) / 2 + 1) gap - gap

noncomputable def universalPairUpper (gap degree : ℕ) : ℕ :=
  min ((degree + gap) / 2 + 1) (degree + 1)

theorem universalPairQ_coeff_interval
    (gap degree : ℕ) (hgap : 1 ≤ gap) :
    PowerSeries.coeff degree (universalPairQ gap) =
      ∑ low ∈ Finset.Ico (universalPairLower gap degree)
          (universalPairUpper gap degree),
        factorialConvolutionTerm degree low := by
  rw [universalPairQ_coeff_boundary_sum]
  let start := (degree + gap) / 2 + 1
  let upper := min (start + gap) (degree + gap + 1)
  let clipped := max start gap
  have hstartUpper : start ≤ upper := by
    dsimp only [upper]
    apply le_min
    · omega
    · dsimp only [start]
      omega
  have hgapUpper : gap ≤ upper := by
    dsimp only [upper]
    apply le_min
    · omega
    · omega
  have hclipUpper : clipped ≤ upper :=
    max_le hstartUpper hgapUpper
  have hstartClip : start ≤ clipped := le_max_left _ _
  have hprefix :
      (∑ high ∈ Finset.Ico start clipped,
        generalPairBoundary gap (degree + gap) high) = 0 := by
    apply Finset.sum_eq_zero
    intro high hhigh
    unfold generalPairBoundary
    rw [reciprocalFactorialInt_nat_sub_eq_zero]
    · exact zero_mul _
    · have hhighClip := (Finset.mem_Ico.mp hhigh).2
      dsimp only [clipped] at hhighClip
      by_cases horder : start ≤ gap
      · rw [max_eq_right horder] at hhighClip
        exact hhighClip
      · rw [max_eq_left (by omega : gap ≤ start)] at hhighClip
        have hhighStart := (Finset.mem_Ico.mp hhigh).1
        omega
  have hsplit := Finset.sum_Ico_consecutive
    (generalPairBoundary gap (degree + gap)) hstartClip hclipUpper
  rw [hprefix, zero_add] at hsplit
  rw [← hsplit]
  let lower := clipped - gap
  let reducedUpper := upper - gap
  have hlowerAdd : lower + gap = clipped := by
    dsimp only [lower]
    omega
  have hupperAdd : reducedUpper + gap = upper := by
    dsimp only [reducedUpper]
    omega
  have hshift := Finset.sum_Ico_add'
    (generalPairBoundary gap (degree + gap)) lower reducedUpper gap
  rw [hlowerAdd, hupperAdd] at hshift
  rw [← hshift]
  have hlowerDef : lower = universalPairLower gap degree := by
    unfold lower clipped start universalPairLower
    rfl
  have hupperDef : reducedUpper = universalPairUpper gap degree := by
    unfold reducedUpper upper start universalPairUpper
    by_cases horder : (degree + gap) / 2 + 1 ≤ degree + 1
    · rw [min_eq_left (by omega), min_eq_left horder]
      omega
    · rw [min_eq_right (by omega), min_eq_right (by omega)]
      omega
  rw [hlowerDef, hupperDef]
  apply Finset.sum_congr rfl
  intro low hlow
  unfold generalPairBoundary factorialConvolutionTerm
  have hlowUpper := (Finset.mem_Ico.mp hlow).2
  have hUpperLe : universalPairUpper gap degree ≤ degree + 1 := by
    exact min_le_right _ _
  have hlowDegree : low ≤ degree := by omega
  have hleft : (((low + gap : ℕ) : ℤ) - (gap : ℤ)) =
      (low : ℤ) := by push_cast; ring
  have hright : ((degree + gap : ℕ) : ℤ) -
      ((low + gap : ℕ) : ℤ) =
        (degree : ℤ) - (low : ℤ) := by push_cast; ring
  rw [hleft, hright]

end FibonacciRibbonKernel
