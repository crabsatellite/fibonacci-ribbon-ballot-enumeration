import FibonacciRibbonKernel.ActualFactorialHomogeneous

namespace FibonacciRibbonKernel

open PowerSeries

structure HomogeneousBesselTerm (degree : ℕ) where
  coefficient : Polynomial ℚ
  index : ℕ
  index_le : index ≤ degree

noncomputable def HomogeneousBesselTerm.eval
    {degree : ℕ} (term : HomogeneousBesselTerm degree) : ℚ⟦X⟧ :=
  (term.coefficient : ℚ⟦X⟧) * besselMonomial degree term.index

def HomogeneousBesselNormalForm (degree : ℕ) (value : ℚ⟦X⟧) : Prop :=
  ∃ terms : List (HomogeneousBesselTerm degree),
    value = (terms.map HomogeneousBesselTerm.eval).sum

noncomputable def HomogeneousBesselTerm.neg
    {degree : ℕ} (term : HomogeneousBesselTerm degree) :
    HomogeneousBesselTerm degree where
  coefficient := -term.coefficient
  index := term.index
  index_le := term.index_le

noncomputable def HomogeneousBesselTerm.mul
    {leftDegree rightDegree : ℕ}
    (left : HomogeneousBesselTerm leftDegree)
    (right : HomogeneousBesselTerm rightDegree) :
    HomogeneousBesselTerm (leftDegree + rightDegree) where
  coefficient := left.coefficient * right.coefficient
  index := left.index + right.index
  index_le := Nat.add_le_add left.index_le right.index_le

theorem besselMonomial_mul
    {leftDegree rightDegree leftIndex rightIndex : ℕ}
    (hleft : leftIndex ≤ leftDegree) (hright : rightIndex ≤ rightDegree) :
    besselMonomial leftDegree leftIndex *
        besselMonomial rightDegree rightIndex =
      besselMonomial (leftDegree + rightDegree) (leftIndex + rightIndex) := by
  unfold besselMonomial
  rw [show leftDegree + rightDegree - (leftIndex + rightIndex) =
      (leftDegree - leftIndex) + (rightDegree - rightIndex) by omega]
  rw [pow_add, pow_add]
  ring

theorem HomogeneousBesselTerm.eval_neg
    {degree : ℕ} (term : HomogeneousBesselTerm degree) :
    term.neg.eval = -term.eval := by
  unfold HomogeneousBesselTerm.neg HomogeneousBesselTerm.eval
  simp

theorem HomogeneousBesselTerm.eval_mul
    {leftDegree rightDegree : ℕ}
    (left : HomogeneousBesselTerm leftDegree)
    (right : HomogeneousBesselTerm rightDegree) :
    (left.mul right).eval = left.eval * right.eval := by
  unfold HomogeneousBesselTerm.mul HomogeneousBesselTerm.eval
  change (((left.coefficient * right.coefficient : Polynomial ℚ) : ℚ⟦X⟧) *
      besselMonomial (leftDegree + rightDegree) (left.index + right.index)) =
    ((left.coefficient : ℚ⟦X⟧) * besselMonomial leftDegree left.index) *
      ((right.coefficient : ℚ⟦X⟧) * besselMonomial rightDegree right.index)
  have hcoe : (((left.coefficient * right.coefficient : Polynomial ℚ) : ℚ⟦X⟧)) =
      (left.coefficient : ℚ⟦X⟧) * (right.coefficient : ℚ⟦X⟧) := by
    exact Polynomial.coe_mul left.coefficient right.coefficient
  rw [hcoe, ← besselMonomial_mul left.index_le right.index_le]
  ring

noncomputable def homogeneousBesselTermProduct
    {leftDegree rightDegree : ℕ}
    (left : List (HomogeneousBesselTerm leftDegree))
    (right : List (HomogeneousBesselTerm rightDegree)) :
    List (HomogeneousBesselTerm (leftDegree + rightDegree)) :=
  left.flatMap fun leftTerm => right.map (leftTerm.mul ·)

theorem homogeneousBesselTerm_mul_map_eval_sum
    {leftDegree rightDegree : ℕ}
    (head : HomogeneousBesselTerm leftDegree)
    (right : List (HomogeneousBesselTerm rightDegree)) :
    ((right.map (head.mul ·)).map HomogeneousBesselTerm.eval).sum =
      head.eval * (right.map HomogeneousBesselTerm.eval).sum := by
  induction right with
  | nil => simp
  | cons rightHead rightTail ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [HomogeneousBesselTerm.eval_mul, ih]
      ring

theorem list_sum_map_neg (values : List ℚ⟦X⟧) :
    (values.map Neg.neg).sum = -values.sum := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

theorem homogeneousBesselTerm_map_neg_eval
    {degree : ℕ} (terms : List (HomogeneousBesselTerm degree)) :
    (terms.map HomogeneousBesselTerm.neg).map
        HomogeneousBesselTerm.eval =
      (terms.map HomogeneousBesselTerm.eval).map Neg.neg := by
  induction terms with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons]
      rw [HomogeneousBesselTerm.eval_neg, ih]

theorem homogeneousBesselTermProduct_eval_sum
    {leftDegree rightDegree : ℕ}
    (left : List (HomogeneousBesselTerm leftDegree))
    (right : List (HomogeneousBesselTerm rightDegree)) :
    ((homogeneousBesselTermProduct left right).map
        HomogeneousBesselTerm.eval).sum =
      (left.map HomogeneousBesselTerm.eval).sum *
        (right.map HomogeneousBesselTerm.eval).sum := by
  induction left with
  | nil => simp [homogeneousBesselTermProduct]
  | cons head tail ih =>
      simp only [homogeneousBesselTermProduct, List.flatMap_cons,
        List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      change ((right.map (head.mul ·)).map
          HomogeneousBesselTerm.eval).sum +
        ((homogeneousBesselTermProduct tail right).map
          HomogeneousBesselTerm.eval).sum = _
      rw [ih]
      rw [homogeneousBesselTerm_mul_map_eval_sum]
      ring

theorem HomogeneousBesselGenerated.normalForm
    {degree : ℕ} {value : ℚ⟦X⟧}
    (hvalue : HomogeneousBesselGenerated degree value) :
    HomogeneousBesselNormalForm degree value := by
  induction hvalue with
  | zero degree =>
      exact ⟨[], by simp⟩
  | term degree index hindex coefficient =>
      let term : HomogeneousBesselTerm degree :=
        ⟨coefficient, index, hindex⟩
      exact ⟨[term], by simp [term, HomogeneousBesselTerm.eval]⟩
  | add hleft hright ihleft ihrigh =>
      obtain ⟨leftTerms, hleftTerms⟩ := ihleft
      obtain ⟨rightTerms, hrightTerms⟩ := ihrigh
      refine ⟨leftTerms ++ rightTerms, ?_⟩
      rw [List.map_append, List.sum_append, ← hleftTerms, ← hrightTerms]
  | neg hvalue ih =>
      obtain ⟨terms, hterms⟩ := ih
      refine ⟨terms.map HomogeneousBesselTerm.neg, ?_⟩
      rw [homogeneousBesselTerm_map_neg_eval]
      rw [list_sum_map_neg, ← hterms]
  | mul hleft hright ihleft ihrigh =>
      obtain ⟨leftTerms, hleftTerms⟩ := ihleft
      obtain ⟨rightTerms, hrightTerms⟩ := ihrigh
      refine ⟨homogeneousBesselTermProduct leftTerms rightTerms, ?_⟩
      rw [homogeneousBesselTermProduct_eval_sum,
        ← hleftTerms, ← hrightTerms]

end FibonacciRibbonKernel
