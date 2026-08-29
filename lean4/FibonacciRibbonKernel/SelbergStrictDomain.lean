import FibonacciRibbonKernel.DixonAndersonGeneralEvaluation

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped Classical BigOperators

def strictMehtaChamber (dimension : ℕ) :
    Set (Fin dimension → ℝ) :=
  {coordinates | StrictAnti coordinates}

def strictOrderedSelbergDomain (dimension : ℕ) :
    Set (Fin dimension → ℝ) :=
  selbergUnitBox dimension ∩ strictMehtaChamber dimension

theorem selbergUnitBox_measurableSet (dimension : ℕ) :
    MeasurableSet (selbergUnitBox dimension) := by
  unfold selbergUnitBox
  exact MeasurableSet.univ_pi fun index => measurableSet_Ioo

theorem strictMehtaChamber_measurableSet (dimension : ℕ) :
    MeasurableSet (strictMehtaChamber dimension) := by
  have hrepresentation : strictMehtaChamber dimension =
      ⋂ first : Fin dimension, ⋂ next : Fin dimension,
        ⋂ (_h : first < next),
          {coordinates : Fin dimension → ℝ |
            coordinates next < coordinates first} := by
    ext coordinates
    simp only [strictMehtaChamber, Set.mem_setOf_eq,
      Set.mem_iInter]
    exact Iff.rfl
  rw [hrepresentation]
  exact MeasurableSet.iInter fun first =>
    MeasurableSet.iInter fun next =>
      MeasurableSet.iInter fun h =>
        measurableSet_lt (measurable_pi_apply next)
          (measurable_pi_apply first)

theorem strictOrderedSelbergDomain_measurableSet (dimension : ℕ) :
    MeasurableSet (strictOrderedSelbergDomain dimension) :=
  (selbergUnitBox_measurableSet dimension).inter
    (strictMehtaChamber_measurableSet dimension)

theorem orderedSelbergDomain_measurableSet (dimension : ℕ) :
    MeasurableSet (orderedSelbergDomain dimension) :=
  (selbergUnitBox_measurableSet dimension).inter
    (standardMehtaChamber_isClosed dimension).measurableSet

theorem strictOrderedSelbergDomain_subset_ordered (dimension : ℕ) :
    strictOrderedSelbergDomain dimension ⊆
      orderedSelbergDomain dimension := by
  rintro coordinates ⟨hbox, hstrict⟩
  exact ⟨hbox, hstrict.antitone⟩

theorem standardMehtaVandermonde_eq_zero_of_not_strictAnti
    {dimension : ℕ} {coordinates : Fin dimension → ℝ}
    (hantitone : Antitone coordinates)
    (hnotStrict : ¬ StrictAnti coordinates) :
    standardMehtaVandermonde dimension coordinates = 0 := by
  by_cases hzero : dimension = 0
  · subst dimension
    exact (hnotStrict fun first => Fin.elim0 first).elim
  obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hzero
  have hnotAdjacent : ¬ ∀ index : Fin predecessor,
      coordinates index.succ < coordinates index.castSucc := by
    rw [← Fin.strictAnti_iff_succ_lt]
    exact hnotStrict
  rcases not_forall.mp hnotAdjacent with ⟨index, hnotLt⟩
  have hreverse : coordinates index.castSucc ≤ coordinates index.succ :=
    le_of_not_gt hnotLt
  have hforward : coordinates index.succ ≤ coordinates index.castSucc :=
    hantitone (Fin.castSucc_le_succ index)
  have hequal : coordinates index.castSucc = coordinates index.succ :=
    le_antisymm hreverse hforward
  unfold standardMehtaVandermonde
  apply Finset.prod_eq_zero (i := index.castSucc)
  · simp
  · apply Finset.prod_eq_zero (i := index.succ)
    · exact Finset.mem_Ioi.mpr index.castSucc_lt_succ
    · rw [hequal, sub_self, abs_zero]

theorem selbergHalfIntegrand_eq_zero_of_ordered_not_strict
    {dimension : ℕ} {alpha beta : ℝ}
    {coordinates : Fin dimension → ℝ}
    (hordered : coordinates ∈ orderedSelbergDomain dimension)
    (hnotStrict : coordinates ∉ strictOrderedSelbergDomain dimension) :
    selbergHalfIntegrand dimension alpha beta coordinates = 0 := by
  have hnot : ¬ StrictAnti coordinates := by
    intro hstrict
    exact hnotStrict ⟨hordered.1, hstrict⟩
  unfold selbergHalfIntegrand
  rw [standardMehtaVandermonde_eq_zero_of_not_strictAnti
    hordered.2 hnot, mul_zero]

theorem orderedSelbergHalfIntegral_eq_strict
    (dimension : ℕ) (alpha beta : ℝ) :
    orderedSelbergHalfIntegral dimension alpha beta =
      ∫ coordinates in strictOrderedSelbergDomain dimension,
        selbergHalfIntegrand dimension alpha beta coordinates := by
  unfold orderedSelbergHalfIntegral
  exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (orderedSelbergDomain_measurableSet dimension)
    (strictOrderedSelbergDomain_subset_ordered dimension)
    (fun coordinates hcoordinates =>
      selbergHalfIntegrand_eq_zero_of_ordered_not_strict
        hcoordinates.1 hcoordinates.2)

end FibonacciRibbonKernel
