import FibonacciRibbonKernel.NearStablePolynomial
import FibonacciRibbonKernel.InvolutionRatios
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.Polynomial.BigOperators

namespace FibonacciRibbonKernel

open scoped Classical

noncomputable def descFactorialPolynomial (order : ℕ) : Polynomial ℚ :=
  ∏ index ∈ Finset.range order,
    (Polynomial.X - Polynomial.C (index : ℚ))

theorem descFactorialPolynomial_eval
    (order value : ℕ) (hvalue : order ≤ value) :
    (descFactorialPolynomial order).eval (value : ℚ) =
      (value.descFactorial order : ℚ) := by
  unfold descFactorialPolynomial
  rw [Polynomial.eval_prod, Nat.descFactorial_eq_prod_range]
  push_cast
  apply Finset.prod_congr rfl
  intro index hindex
  simp only [Finset.mem_range] at hindex
  simp [Polynomial.eval_sub, Polynomial.eval_X,
    Nat.cast_sub (by omega : index ≤ value)]

noncomputable def matchingChoosePolynomial (edges : ℕ) : Polynomial ℚ :=
  Polynomial.C ((edges.factorial : ℚ)⁻¹) *
    (descFactorialPolynomial edges).comp
      (Polynomial.X - Polynomial.C (edges : ℚ))

theorem matchingChoosePolynomial_eval
    (edges size : ℕ) (hsize : 2 * edges ≤ size) :
    (matchingChoosePolynomial edges).eval (size : ℚ) =
      (Nat.choose (size - edges) edges : ℚ) := by
  unfold matchingChoosePolynomial
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hcast : (size : ℚ) - edges = (size - edges : ℕ) := by
    rw [Nat.cast_sub (R := ℚ) (by omega : edges ≤ size)]
  rw [hcast, descFactorialPolynomial_eval edges (size - edges) (by omega)]
  have hfactorial : (edges.factorial : ℚ) ≠ 0 := by positivity
  have hdesc := Nat.descFactorial_eq_factorial_mul_choose (size - edges) edges
  have hdescQ :
      ((size - edges).descFactorial edges : ℚ) =
        edges.factorial * Nat.choose (size - edges) edges := by
    exact_mod_cast hdesc
  rw [hdescQ]
  field_simp

theorem descFactorialPolynomial_monic (order : ℕ) :
    (descFactorialPolynomial order).Monic := by
  unfold descFactorialPolynomial
  exact Polynomial.monic_prod_of_monic _ _
    (by intro index hindex; exact Polynomial.monic_X_sub_C _)

@[simp] theorem descFactorialPolynomial_natDegree (order : ℕ) :
    (descFactorialPolynomial order).natDegree = order := by
  unfold descFactorialPolynomial
  rw [Polynomial.natDegree_prod]
  · calc
      (∑ index ∈ Finset.range order,
          (Polynomial.X - Polynomial.C (index : ℚ)).natDegree) =
          ∑ _index ∈ Finset.range order, 1 := by
        apply Finset.sum_congr rfl
        intro index hindex
        rw [Polynomial.natDegree_X_sub_C]
      _ = order := by simp
  · intro index hindex
    exact (Polynomial.monic_X_sub_C _).ne_zero

theorem matchingChoosePolynomial_natDegree_le (edges : ℕ) :
    (matchingChoosePolynomial edges).natDegree ≤ edges := by
  unfold matchingChoosePolynomial
  calc
    (Polynomial.C ((edges.factorial : ℚ)⁻¹) *
        (descFactorialPolynomial edges).comp
          (Polynomial.X - Polynomial.C (edges : ℚ))).natDegree ≤
      (Polynomial.C ((edges.factorial : ℚ)⁻¹)).natDegree +
        ((descFactorialPolynomial edges).comp
          (Polynomial.X - Polynomial.C (edges : ℚ))).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 0 + edges * 1 := by
      gcongr
      · rw [Polynomial.natDegree_C]
      · exact Polynomial.natDegree_comp_le.trans (by
          rw [descFactorialPolynomial_natDegree,
            Polynomial.natDegree_X_sub_C])
    _ = edges := by omega

theorem matchingChoosePolynomial_coeff_top (edges : ℕ) :
    (matchingChoosePolynomial edges).coeff edges =
      (edges.factorial : ℚ)⁻¹ := by
  have hshiftMonic :
      ((descFactorialPolynomial edges).comp
        (Polynomial.X - Polynomial.C (edges : ℚ))).Monic := by
    exact (descFactorialPolynomial_monic edges).comp
      (Polynomial.monic_X_sub_C _) (by
        rw [Polynomial.natDegree_X_sub_C]
        omega)
  have hdegree :
      ((descFactorialPolynomial edges).comp
        (Polynomial.X - Polynomial.C (edges : ℚ))).natDegree = edges := by
    rw [Polynomial.natDegree_comp,
      descFactorialPolynomial_natDegree, Polynomial.natDegree_X_sub_C]
    omega
  have hcoeff :
      ((descFactorialPolynomial edges).comp
        (Polynomial.X - Polynomial.C (edges : ℚ))).coeff edges = 1 := by
    let shifted := (descFactorialPolynomial edges).comp
      (Polynomial.X - Polynomial.C (edges : ℚ))
    calc
      shifted.coeff edges = shifted.coeff shifted.natDegree := by
        exact congrArg shifted.coeff hdegree.symm
      _ = shifted.leadingCoeff := Polynomial.coeff_natDegree
      _ = 1 := hshiftMonic.leadingCoeff
  unfold matchingChoosePolynomial
  rw [Polynomial.coeff_C_mul, hcoeff, mul_one]

noncomputable def shiftedTailTableauPolynomial
    (tail shift : ℕ) : Polynomial ℚ :=
  (tailTableauPolynomial tail).comp
    (Polynomial.X - Polynomial.C (shift : ℚ))

theorem shiftedTailTableauPolynomial_eval
    (tail shift size : ℕ)
    (hshift : shift ≤ size)
    (hlarge : 2 * tail + 2 ≤ size - shift) :
    (shiftedTailTableauPolynomial tail shift).eval (size : ℚ) =
      (tailTableauSum tail (size - shift) : ℚ) := by
  unfold shiftedTailTableauPolynomial
  rw [Polynomial.eval_comp, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  have hcast : (size : ℚ) - shift = (size - shift : ℕ) := by
    rw [Nat.cast_sub (R := ℚ) hshift]
  rw [hcast]
  exact tailTableauPolynomial_eventually_eval tail (size - shift) hlarge

theorem shiftedTailTableauPolynomial_natDegree_le
    (tail shift : ℕ) :
    (shiftedTailTableauPolynomial tail shift).natDegree ≤ tail := by
  unfold shiftedTailTableauPolynomial
  exact Polynomial.natDegree_comp_le.trans (by
    rw [Polynomial.natDegree_X_sub_C]
    simpa using tailTableauPolynomial_natDegree_le tail)

theorem coeff_comp_X_sub_C_of_natDegree_le
    (polynomial : Polynomial ℚ) (degree : ℕ)
    (hdegree : polynomial.natDegree ≤ degree) (shift : ℚ) :
    (polynomial.comp (Polynomial.X - Polynomial.C shift)).coeff degree =
      polynomial.coeff degree := by
  by_cases heq : polynomial.natDegree = degree
  · have hq : (Polynomial.X - Polynomial.C shift).natDegree ≠ 0 := by
      rw [Polynomial.natDegree_X_sub_C]
      omega
    have hcompDegree :
        (polynomial.comp (Polynomial.X - Polynomial.C shift)).natDegree = degree := by
      rw [Polynomial.natDegree_comp, heq, Polynomial.natDegree_X_sub_C]
      omega
    calc
      (polynomial.comp (Polynomial.X - Polynomial.C shift)).coeff degree =
          (polynomial.comp (Polynomial.X - Polynomial.C shift)).leadingCoeff := by
        rw [← hcompDegree, Polynomial.coeff_natDegree]
      _ = polynomial.leadingCoeff *
          (Polynomial.X - Polynomial.C shift).leadingCoeff ^ polynomial.natDegree :=
        Polynomial.leadingCoeff_comp hq
      _ = polynomial.leadingCoeff := by
        rw [(Polynomial.monic_X_sub_C shift).leadingCoeff]
        simp
      _ = polynomial.coeff degree := by
        rw [← heq, Polynomial.coeff_natDegree]
  · have hlt : polynomial.natDegree < degree := lt_of_le_of_ne hdegree heq
    have hcompDegree :
        (polynomial.comp (Polynomial.X - Polynomial.C shift)).natDegree < degree :=
      lt_of_le_of_lt (Polynomial.natDegree_comp_le.trans (by
        rw [Polynomial.natDegree_X_sub_C]
        omega)) hlt
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hcompDegree,
      Polynomial.coeff_eq_zero_of_natDegree_lt hlt]

theorem shiftedTailTableauPolynomial_coeff_top
    (tail shift : ℕ) :
    (shiftedTailTableauPolynomial tail shift).coeff tail =
      (involutionNumber tail : ℚ) / tail.factorial := by
  unfold shiftedTailTableauPolynomial
  rw [coeff_comp_X_sub_C_of_natDegree_le _ tail
    (tailTableauPolynomial_natDegree_le tail),
    tailTableauPolynomial_coeff_top]

noncomputable def nearStableDefectPolynomial (defect : ℕ) : Polynomial ℚ :=
  ∑ edges ∈ Finset.range ((defect + 1) / 2),
    Polynomial.C ((-1 : ℚ) ^ edges) *
      matchingChoosePolynomial edges *
      shiftedTailTableauPolynomial (defect - 2 * edges - 1) (2 * edges)

noncomputable def nearStableDefectTerm
    (defect edges : ℕ) : Polynomial ℚ :=
  Polynomial.C ((-1 : ℚ) ^ edges) *
    matchingChoosePolynomial edges *
    shiftedTailTableauPolynomial (defect - 2 * edges - 1) (2 * edges)

theorem nearStableDefectTerm_natDegree_le
    (defect edges : ℕ) :
    (nearStableDefectTerm defect edges).natDegree ≤
      edges + (defect - 2 * edges - 1) := by
  unfold nearStableDefectTerm
  calc
    (Polynomial.C ((-1 : ℚ) ^ edges) *
        matchingChoosePolynomial edges *
        shiftedTailTableauPolynomial (defect - 2 * edges - 1)
          (2 * edges)).natDegree ≤
      (Polynomial.C ((-1 : ℚ) ^ edges) *
        matchingChoosePolynomial edges).natDegree +
          (shiftedTailTableauPolynomial (defect - 2 * edges - 1)
            (2 * edges)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ ((Polynomial.C ((-1 : ℚ) ^ edges)).natDegree +
        (matchingChoosePolynomial edges).natDegree) +
          (defect - 2 * edges - 1) := by
      gcongr
      · exact Polynomial.natDegree_mul_le
      · exact shiftedTailTableauPolynomial_natDegree_le _ _
    _ ≤ (0 + edges) + (defect - 2 * edges - 1) := by
      gcongr
      · rw [Polynomial.natDegree_C]
      · exact matchingChoosePolynomial_natDegree_le edges
    _ = edges + (defect - 2 * edges - 1) := by omega

theorem nearStableDefectPolynomial_natDegree_le
    (defect : ℕ) (hdefect : 1 ≤ defect) :
    (nearStableDefectPolynomial defect).natDegree ≤ defect - 1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro exponent hexponent
  unfold nearStableDefectPolynomial
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro edges hedges
  simp only [Finset.mem_range] at hedges
  change (nearStableDefectTerm defect edges).coeff exponent = 0
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt (nearStableDefectTerm_natDegree_le defect edges) (by
    have htwice := (Nat.lt_div_iff_mul_lt (k := 2) (x := edges)
      (y := defect + 1) (by omega)).mp hedges
    omega)

theorem nearStableDefectTerm_zero (defect : ℕ) :
    nearStableDefectTerm defect 0 =
      shiftedTailTableauPolynomial (defect - 1) 0 := by
  simp [nearStableDefectTerm, matchingChoosePolynomial,
    descFactorialPolynomial]

theorem nearStableDefectPolynomial_coeff_top
    (defect : ℕ) (hdefect : 1 ≤ defect) :
    (nearStableDefectPolynomial defect).coeff (defect - 1) =
      (involutionNumber (defect - 1) : ℚ) / (defect - 1).factorial := by
  unfold nearStableDefectPolynomial
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single 0]
  · change (nearStableDefectTerm defect 0).coeff (defect - 1) = _
    rw [nearStableDefectTerm_zero,
      shiftedTailTableauPolynomial_coeff_top]
  · intro edges hedges hne
    simp only [Finset.mem_range] at hedges
    change (nearStableDefectTerm defect edges).coeff (defect - 1) = 0
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    refine lt_of_le_of_lt (nearStableDefectTerm_natDegree_le defect edges) ?_
    have htwice := (Nat.lt_div_iff_mul_lt (k := 2) (x := edges)
      (y := defect + 1) (by omega)).mp hedges
    omega
  · intro hnot
    exfalso
    apply hnot
    simp
    omega

theorem nearStableDefectPolynomial_natDegree_eq
    (defect : ℕ) (hdefect : 1 ≤ defect) :
    (nearStableDefectPolynomial defect).natDegree = defect - 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (nearStableDefectPolynomial_natDegree_le defect hdefect)
  rw [nearStableDefectPolynomial_coeff_top defect hdefect]
  have hinvolution : (involutionNumber (defect - 1) : ℚ) ≠ 0 := by
    exact_mod_cast (involutionNumber_pos (defect - 1)).ne'
  have hfactorial : ((defect - 1).factorial : ℚ) ≠ 0 := by positivity
  exact div_ne_zero hinvolution hfactorial

theorem nearStableDefectPolynomial_eventually_eval
    (defect size : ℕ) (hlarge : 2 * defect + 2 ≤ size) :
    (nearStableDefectPolynomial defect).eval (size : ℚ) =
      (stableActualInvolutionNumber size : ℚ) -
        (ribbonCount (size - defect - 1) size : ℚ) := by
  unfold nearStableDefectPolynomial
  rw [Polynomial.eval_finsetSum]
  have hdefect := stableActualInvolutionNumber_sub_ribbonCount_tail
    defect size (by omega)
  have hdefectQ :
      (stableActualInvolutionNumber size : ℚ) -
          (ribbonCount (size - defect - 1) size : ℚ) =
        ∑ edges ∈ Finset.range ((defect + 1) / 2),
          (-1 : ℚ) ^ edges *
            Nat.choose (size - edges) edges *
            tailTableauSum (defect - 2 * edges - 1)
              (size - 2 * edges) := by
    exact_mod_cast hdefect
  rw [hdefectQ]
  apply Finset.sum_congr rfl
  intro edges hedges
  simp only [Finset.mem_range] at hedges
  have htwice := (Nat.lt_div_iff_mul_lt (k := 2) (x := edges)
    (y := defect + 1) (by omega)).mp hedges
  rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
    matchingChoosePolynomial_eval edges size (by omega),
    shiftedTailTableauPolynomial_eval]
  · omega
  · omega

def EventuallyPolynomial (sequence : ℕ → ℚ) (degreeBound : ℕ) : Prop :=
  ∃ polynomial : Polynomial ℚ,
    polynomial.natDegree ≤ degreeBound ∧
      ∀ᶠ size : ℕ in Filter.atTop,
        polynomial.eval (size : ℚ) = sequence size

theorem nearStableDefect_isEventuallyPolynomial (defect : ℕ) :
    ∃ polynomial : Polynomial ℚ,
      ∀ᶠ size : ℕ in Filter.atTop,
        polynomial.eval (size : ℚ) =
          (stableActualInvolutionNumber size : ℚ) -
            (ribbonCount (size - defect - 1) size : ℚ) := by
  refine ⟨nearStableDefectPolynomial defect, ?_⟩
  filter_upwards [Filter.eventually_atTop.2
    ⟨2 * defect + 2, fun _ h => h⟩] with size hsize
  exact nearStableDefectPolynomial_eventually_eval defect size hsize

theorem nearStablePolynomiality_with_leading_coefficient
    (defect : ℕ) (hdefect : 1 ≤ defect) :
    (nearStableDefectPolynomial defect).natDegree = defect - 1 ∧
      (nearStableDefectPolynomial defect).coeff (defect - 1) =
        (involutionNumber (defect - 1) : ℚ) / (defect - 1).factorial ∧
      ∀ᶠ size : ℕ in Filter.atTop,
        (nearStableDefectPolynomial defect).eval (size : ℚ) =
          (stableActualInvolutionNumber size : ℚ) -
            (ribbonCount (size - defect - 1) size : ℚ) := by
  refine ⟨nearStableDefectPolynomial_natDegree_eq defect hdefect,
    nearStableDefectPolynomial_coeff_top defect hdefect, ?_⟩
  filter_upwards [Filter.eventually_atTop.2
    ⟨2 * defect + 2, fun _ h => h⟩] with size hsize
  exact nearStableDefectPolynomial_eventually_eval defect size hsize

end FibonacciRibbonKernel
