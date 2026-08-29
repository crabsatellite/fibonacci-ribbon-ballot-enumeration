import FibonacciRibbonKernel.SelbergStrictDomain

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped Classical BigOperators

noncomputable def selbergExtendedAnchors (rank : ℕ)
    (roots : Fin (rank + 1) → ℝ) : Fin (rank + 3) → ℝ :=
  Fin.cons 1 (Fin.lastCases 0 roots)

noncomputable def selbergAndersonParameters (rank : ℕ)
    (alpha beta : ℝ) : Fin (rank + 3) → ℝ :=
  Fin.cons beta (Fin.lastCases alpha
    (fun _ : Fin (rank + 1) => (1 / 2 : ℝ)))

@[simp] theorem selbergExtendedAnchors_zero (rank : ℕ)
    (roots : Fin (rank + 1) → ℝ) :
    selbergExtendedAnchors rank roots 0 = 1 := by
  simp [selbergExtendedAnchors]

@[simp] theorem selbergExtendedAnchors_root (rank : ℕ)
    (roots : Fin (rank + 1) → ℝ) (index : Fin (rank + 1)) :
    selbergExtendedAnchors rank roots index.castSucc.succ =
      roots index := by
  simp [selbergExtendedAnchors]

@[simp] theorem selbergExtendedAnchors_last (rank : ℕ)
    (roots : Fin (rank + 1) → ℝ) :
    selbergExtendedAnchors rank roots (Fin.last (rank + 2)) = 0 := by
  simp [selbergExtendedAnchors]

@[simp] theorem selbergExtendedAnchors_one (rank : ℕ)
    (roots : Fin (rank + 1) → ℝ) :
    selbergExtendedAnchors rank roots (1 : Fin (rank + 3)) = roots 0 := by
  have hindex : (1 : Fin (rank + 3)) =
      (0 : Fin (rank + 1)).castSucc.succ := by
    apply Fin.ext
    rfl
  rw [hindex, selbergExtendedAnchors_root]

@[simp] theorem selbergExtendedAnchors_castSucc_zero (rank : ℕ)
    (roots : Fin (rank + 1) → ℝ) :
    selbergExtendedAnchors rank roots
      (Fin.castSucc (0 : Fin (rank + 2))) = 1 := by
  have hindex : Fin.castSucc (0 : Fin (rank + 2)) =
      (0 : Fin (rank + 3)) := by
    apply Fin.ext
    rfl
  rw [hindex, selbergExtendedAnchors_zero]

@[simp] theorem selbergExtendedAnchors_succ_zero (rank : ℕ)
    (roots : Fin (rank + 1) → ℝ) :
    selbergExtendedAnchors rank roots
      (Fin.succ (0 : Fin (rank + 2))) = roots 0 := by
  have hindex : Fin.succ (0 : Fin (rank + 2)) =
      (1 : Fin (rank + 3)) := by
    apply Fin.ext
    rfl
  rw [hindex, selbergExtendedAnchors_one]

@[simp] theorem selbergExtendedAnchors_succ_castSucc (rank : ℕ)
    (roots : Fin (rank + 1) → ℝ) (index : Fin (rank + 1)) :
    selbergExtendedAnchors rank roots index.succ.castSucc =
      roots index := by
  have hindex : index.succ.castSucc = index.castSucc.succ := by
    apply Fin.ext
    rfl
  rw [hindex, selbergExtendedAnchors_root]

@[simp] theorem selbergExtendedAnchors_castSucc_succ_succ (rank : ℕ)
    (roots : Fin (rank + 1) → ℝ) (index : Fin rank) :
    selbergExtendedAnchors rank roots index.castSucc.succ.succ =
      roots index.succ := by
  have hindex : index.castSucc.succ.succ =
      index.succ.castSucc.succ := by
    apply Fin.ext
    rfl
  rw [hindex, selbergExtendedAnchors_root]

@[simp] theorem selbergExtendedAnchors_last_succ_succ (rank : ℕ)
    (roots : Fin (rank + 1) → ℝ) :
    selbergExtendedAnchors rank roots (Fin.last rank).succ.succ = 0 := by
  have hindex : (Fin.last rank).succ.succ = Fin.last (rank + 2) := by
    apply Fin.ext
    rfl
  rw [hindex, selbergExtendedAnchors_last]

@[simp] theorem selbergAndersonParameters_zero (rank : ℕ)
    (alpha beta : ℝ) :
    selbergAndersonParameters rank alpha beta 0 = beta := by
  simp [selbergAndersonParameters]

@[simp] theorem selbergAndersonParameters_root (rank : ℕ)
    (alpha beta : ℝ) (index : Fin (rank + 1)) :
    selbergAndersonParameters rank alpha beta index.castSucc.succ =
      1 / 2 := by
  simp [selbergAndersonParameters]

@[simp] theorem selbergAndersonParameters_last (rank : ℕ)
    (alpha beta : ℝ) :
    selbergAndersonParameters rank alpha beta (Fin.last (rank + 2)) =
      alpha := by
  simp [selbergAndersonParameters]

@[simp] theorem selbergExtendedAnchors_last_succ (rank : ℕ)
    (roots : Fin (rank + 1) → ℝ) :
    selbergExtendedAnchors rank roots (Fin.last (rank + 1)).succ = 0 := by
  have hindex : (Fin.last (rank + 1)).succ = Fin.last (rank + 2) := by
    apply Fin.ext
    rfl
  rw [hindex, selbergExtendedAnchors_last]

@[simp] theorem selbergAndersonParameters_last_succ (rank : ℕ)
    (alpha beta : ℝ) :
    selbergAndersonParameters rank alpha beta
      (Fin.last (rank + 1)).succ = alpha := by
  have hindex : (Fin.last (rank + 1)).succ = Fin.last (rank + 2) := by
    apply Fin.ext
    rfl
  rw [hindex, selbergAndersonParameters_last]

theorem selbergExtendedAnchors_strictAnti (rank : ℕ)
    (roots : Fin (rank + 1) → ℝ)
    (hroots : roots ∈ strictOrderedSelbergDomain (rank + 1)) :
    StrictAnti (selbergExtendedAnchors rank roots) := by
  rw [Fin.strictAnti_iff_succ_lt]
  intro index
  cases index using Fin.cases with
  | zero =>
      rw [selbergExtendedAnchors_succ_zero,
        selbergExtendedAnchors_castSucc_zero]
      exact (hroots.1 0 (Set.mem_univ 0)).2
  | succ index =>
      cases index using Fin.lastCases with
      | last =>
          rw [selbergExtendedAnchors_last_succ_succ,
            selbergExtendedAnchors_succ_castSucc]
          exact (hroots.1 (Fin.last rank) (Set.mem_univ _)).1
      | cast previous =>
          have hlt : previous.castSucc < previous.succ :=
            previous.castSucc_lt_succ
          rw [selbergExtendedAnchors_castSucc_succ_succ,
            selbergExtendedAnchors_succ_castSucc]
          exact hroots.2 hlt

theorem selbergAndersonParameters_pos (rank : ℕ)
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    ∀ anchor, 0 < selbergAndersonParameters rank alpha beta anchor := by
  intro anchor
  cases anchor using Fin.cases with
  | zero => simpa using hbeta
  | succ anchor =>
      cases anchor using Fin.lastCases with
      | last => simpa using halpha
      | cast index => norm_num

theorem selbergExtendedAnchors_le_one (rank : ℕ)
    (roots : Fin (rank + 1) → ℝ)
    (hroots : roots ∈ strictOrderedSelbergDomain (rank + 1))
    (anchor : Fin (rank + 3)) :
    selbergExtendedAnchors rank roots anchor ≤ 1 := by
  cases anchor using Fin.cases with
  | zero => simp
  | succ anchor =>
      cases anchor using Fin.lastCases with
      | last => simp
      | cast index =>
          rw [selbergExtendedAnchors_root]
          exact (hroots.1 index (Set.mem_univ _)).2.le

theorem selbergExtendedAnchors_nonneg (rank : ℕ)
    (roots : Fin (rank + 1) → ℝ)
    (hroots : roots ∈ strictOrderedSelbergDomain (rank + 1))
    (anchor : Fin (rank + 3)) :
    0 ≤ selbergExtendedAnchors rank roots anchor := by
  cases anchor using Fin.cases with
  | zero => norm_num
  | succ anchor =>
      cases anchor using Fin.lastCases with
      | last => simp
      | cast index =>
          rw [selbergExtendedAnchors_root]
          exact (hroots.1 index (Set.mem_univ _)).1.le

theorem selbergJointDomain_iff (rank : ℕ)
    (upper : Fin (rank + 2) → ℝ)
    (lower : Fin (rank + 1) → ℝ) :
    (upper ∈ strictOrderedSelbergDomain (rank + 2) ∧
        DixonAndersonInterlacing upper lower) ↔
      (lower ∈ strictOrderedSelbergDomain (rank + 1) ∧
        DixonAndersonInterlacing
          (selbergExtendedAnchors rank lower) upper) := by
  constructor
  · rintro ⟨hupper, hinterlace⟩
    have hlowerStrict : StrictAnti lower :=
      roots_strictAnti_of_interlacing hupper.2 hinterlace
    have hlowerBox : lower ∈ selbergUnitBox (rank + 1) := by
      intro index hindex
      have hleft := (hinterlace index).1
      have hright := (hinterlace index).2
      have hupperLeft := hupper.1 index.castSucc (Set.mem_univ _)
      have hupperRight := hupper.1 index.succ (Set.mem_univ _)
      exact ⟨lt_trans hupperRight.1 hright,
        lt_trans hleft hupperLeft.2⟩
    refine ⟨⟨hlowerBox, hlowerStrict⟩, ?_⟩
    intro index
    cases index using Fin.cases with
    | zero =>
        simpa only [selbergExtendedAnchors_castSucc_zero,
          selbergExtendedAnchors_succ_zero] using
          (show 1 > upper 0 ∧ upper 0 > lower 0 from
            ⟨(hupper.1 0 (Set.mem_univ 0)).2,
              (hinterlace 0).1⟩)
    | succ index =>
        cases index using Fin.lastCases with
        | last =>
            simpa only [selbergExtendedAnchors_last_succ_succ,
              selbergExtendedAnchors_succ_castSucc] using
              (show lower (Fin.last rank) > upper (Fin.last rank).succ ∧
                  upper (Fin.last rank).succ > 0 from
                ⟨(hinterlace (Fin.last rank)).2,
                  (hupper.1 (Fin.last rank).succ
                    (Set.mem_univ _)).1⟩)
        | cast previous =>
            simpa only [selbergExtendedAnchors_succ_castSucc,
              selbergExtendedAnchors_castSucc_succ_succ] using
              (show lower previous.castSucc >
                    upper previous.castSucc.succ ∧
                  upper previous.castSucc.succ > lower previous.succ from
                ⟨(hinterlace previous.castSucc).2,
                  (hinterlace previous.succ).1⟩)
  · rintro ⟨hlower, hinterlace⟩
    have hextended : StrictAnti (selbergExtendedAnchors rank lower) :=
      selbergExtendedAnchors_strictAnti rank lower hlower
    have hupperStrict : StrictAnti upper :=
      roots_strictAnti_of_interlacing hextended hinterlace
    have hupperBox : upper ∈ selbergUnitBox (rank + 2) := by
      intro index hindex
      have hleft := (hinterlace index).1
      have hright := (hinterlace index).2
      exact ⟨lt_of_le_of_lt
          (selbergExtendedAnchors_nonneg rank lower hlower index.succ)
          hright,
        lt_of_lt_of_le hleft
          (selbergExtendedAnchors_le_one rank lower hlower
            index.castSucc)⟩
    refine ⟨⟨hupperBox, hupperStrict⟩, ?_⟩
    intro index
    constructor
    · have h := (hinterlace index.castSucc).2
      simpa only [selbergExtendedAnchors_root] using h
    · have h := (hinterlace index.succ).1
      simpa only [selbergExtendedAnchors_succ_castSucc] using h

theorem dixonAndersonGeneralAnchorFactor_cons (rank : ℕ)
    (firstAnchor firstParameter : ℝ)
    (anchors : Fin (rank + 1) → ℝ)
    (parameters : Fin (rank + 1) → ℝ) :
    dixonAndersonGeneralAnchorFactor
        (Fin.cons firstAnchor anchors)
        (Fin.cons firstParameter parameters) =
      (∏ anchor : Fin (rank + 1),
        (firstAnchor - anchors anchor) ^
          (firstParameter + parameters anchor - 1)) *
        dixonAndersonGeneralAnchorFactor anchors parameters := by
  unfold dixonAndersonGeneralAnchorFactor
  rw [Fin.prod_univ_succ]
  rw [Fin.prod_Ioi_zero]
  congr 1
  apply Finset.prod_congr rfl
  intro first hfirst
  rw [Fin.prod_Ioi_succ]
  apply Finset.prod_congr rfl
  intro next hnext
  rfl

theorem fin_prod_Ioi_castSucc_factor
    {n : ℕ} (f : Fin (n + 1) → ℝ) (index : Fin n) :
    (∏ next ∈ Finset.Ioi index.castSucc, f next) =
      (∏ next ∈ Finset.Ioi index, f next.castSucc) *
        f (Fin.last n) := by
  change (∏ next ∈ Finset.Ioc index.castSucc (⊤ : Fin (n + 1)),
    f next) = _
  have htop : (⊤ : Fin (n + 1)) = Fin.last n := by rfl
  rw [htop]
  rw [← Finset.prod_Ioo_mul_eq_prod_Ioc index.castSucc_lt_last]
  congr 1
  rw [← Fin.map_castSuccEmb_Ioi]
  rw [Finset.prod_map]
  rfl

theorem dixonAndersonGeneralAnchorFactor_lastCases (rank : ℕ)
    (lastAnchor lastParameter : ℝ)
    (anchors : Fin (rank + 1) → ℝ)
    (parameters : Fin (rank + 1) → ℝ) :
    dixonAndersonGeneralAnchorFactor
        (Fin.lastCases lastAnchor anchors)
        (Fin.lastCases lastParameter parameters) =
      dixonAndersonGeneralAnchorFactor anchors parameters *
        ∏ anchor : Fin (rank + 1),
          (anchors anchor - lastAnchor) ^
            (parameters anchor + lastParameter - 1) := by
  unfold dixonAndersonGeneralAnchorFactor
  rw [Fin.prod_univ_castSucc]
  have hlast :
      (∏ next ∈ Finset.Ioi (Fin.last (rank + 1)),
        ((Fin.lastCases lastAnchor anchors : Fin (rank + 2) → ℝ)
            (Fin.last (rank + 1)) -
          (Fin.lastCases lastAnchor anchors : Fin (rank + 2) → ℝ) next) ^
          ((Fin.lastCases lastParameter parameters : Fin (rank + 2) → ℝ)
              (Fin.last (rank + 1)) +
            (Fin.lastCases lastParameter parameters : Fin (rank + 2) → ℝ)
              next - 1)) = 1 := by
    apply Finset.prod_eq_one
    intro next hnext
    exact (not_lt_of_ge next.le_last (Finset.mem_Ioi.mp hnext)).elim
  rw [hlast, mul_one]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro anchor hanchor
  rw [fin_prod_Ioi_castSucc_factor]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last]

theorem dixonAndersonGeneralAnchorFactor_constant_half
    (rank : ℕ) (anchors : Fin (rank + 1) → ℝ) :
    dixonAndersonGeneralAnchorFactor anchors
      (fun _ => (1 / 2 : ℝ)) = 1 := by
  unfold dixonAndersonGeneralAnchorFactor
  apply Finset.prod_eq_one
  intro first hfirst
  apply Finset.prod_eq_one
  intro next hnext
  norm_num

theorem selbergExtendedAnchorFactor_eq_weights
    (rank : ℕ) (roots : Fin (rank + 1) → ℝ)
    (alpha beta : ℝ) :
    dixonAndersonGeneralAnchorFactor
        (selbergExtendedAnchors rank roots)
        (selbergAndersonParameters rank alpha beta) =
      ∏ root : Fin (rank + 1),
        selbergHalfWeight (alpha + 1 / 2) (beta + 1 / 2)
          (roots root) := by
  change dixonAndersonGeneralAnchorFactor
      (Fin.cons 1 (Fin.lastCases 0 roots))
      (Fin.cons beta (Fin.lastCases alpha
        (fun _ : Fin (rank + 1) => (1 / 2 : ℝ)))) = _
  rw [dixonAndersonGeneralAnchorFactor_cons (rank + 1)]
  rw [dixonAndersonGeneralAnchorFactor_lastCases rank]
  rw [dixonAndersonGeneralAnchorFactor_constant_half]
  rw [one_mul]
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  norm_num
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro root hroot
  unfold selbergHalfWeight
  have halpha :
      (1 / 2 : ℝ) + alpha - 1 = (alpha + 1 / 2) - 1 := by ring
  have hbeta :
      beta + 1 / 2 - 1 = (beta + 1 / 2) - 1 := by ring
  rw [halpha, hbeta]
  ring

noncomputable def selbergHalfCrossProduct (rank : ℕ)
    (upper : Fin (rank + 2) → ℝ)
    (lower : Fin (rank + 1) → ℝ) : ℝ :=
  ∏ upperIndex, ∏ lowerIndex,
    |upper upperIndex - lower lowerIndex| ^ (-1 / 2 : ℝ)

theorem selbergExtendedCrossProduct_row
    (rank : ℕ) (lower : Fin (rank + 1) → ℝ)
    (alpha beta value : ℝ) (hvalue : value ∈ Set.Ioo (0 : ℝ) 1) :
    (∏ anchor : Fin (rank + 3),
      |value - selbergExtendedAnchors rank lower anchor| ^
        (selbergAndersonParameters rank alpha beta anchor - 1)) =
      selbergHalfWeight alpha beta value *
        ∏ lowerIndex : Fin (rank + 1),
          |value - lower lowerIndex| ^ (-1 / 2 : ℝ) := by
  rw [Fin.prod_univ_succ]
  rw [Fin.prod_univ_castSucc]
  simp only [selbergExtendedAnchors_zero,
    selbergAndersonParameters_zero,
    selbergExtendedAnchors_root,
    selbergAndersonParameters_root,
    selbergExtendedAnchors_last_succ,
    selbergAndersonParameters_last_succ]
  have habsOne : |value - 1| = 1 - value := by
    rw [abs_of_nonpos (sub_nonpos.mpr hvalue.2.le)]
    ring
  have habsZero : |value - 0| = value := by
    rw [sub_zero, abs_of_pos hvalue.1]
  rw [habsOne, habsZero]
  unfold selbergHalfWeight
  have hhalf : (1 / 2 : ℝ) - 1 = -1 / 2 := by ring
  rw [hhalf]
  ring

theorem selbergExtendedCrossProduct_eq
    (rank : ℕ) (upper : Fin (rank + 2) → ℝ)
    (lower : Fin (rank + 1) → ℝ)
    (alpha beta : ℝ)
    (hupper : upper ∈ strictOrderedSelbergDomain (rank + 2)) :
    dixonAndersonGeneralCrossProduct
        (selbergExtendedAnchors rank lower)
        (selbergAndersonParameters rank alpha beta) upper =
      (∏ upperIndex,
        selbergHalfWeight alpha beta (upper upperIndex)) *
        selbergHalfCrossProduct rank upper lower := by
  unfold dixonAndersonGeneralCrossProduct
  unfold selbergHalfCrossProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro upperIndex hindex
  exact selbergExtendedCrossProduct_row rank lower alpha beta
    (upper upperIndex) (hupper.1 upperIndex (Set.mem_univ _))

theorem standardMehtaVandermonde_eq_ordered_of_strictAnti
    {dimension : ℕ} (coordinates : Fin dimension → ℝ)
    (hcoordinates : StrictAnti coordinates) :
    standardMehtaVandermonde dimension coordinates =
      ∏ first, ∏ next ∈ Finset.Ioi first,
        (coordinates first - coordinates next) := by
  rw [standardMehtaVandermonde_eq_abs_det]
  rw [abs_det_vandermonde_eq_cauchyAbsoluteVandermonde]
  exact cauchyAbsoluteVandermonde_eq_orderedVandermonde
    coordinates hcoordinates

theorem dixonAndersonGeneralIntegrand_extended_eq
    (rank : ℕ) (upper : Fin (rank + 2) → ℝ)
    (lower : Fin (rank + 1) → ℝ)
    (alpha beta : ℝ)
    (hupper : upper ∈ strictOrderedSelbergDomain (rank + 2)) :
    dixonAndersonGeneralIntegrand
        (selbergExtendedAnchors rank lower)
        (selbergAndersonParameters rank alpha beta) upper =
      selbergHalfIntegrand (rank + 2) alpha beta upper *
        selbergHalfCrossProduct rank upper lower := by
  unfold dixonAndersonGeneralIntegrand
  rw [selbergExtendedCrossProduct_eq
    rank upper lower alpha beta hupper]
  unfold selbergHalfIntegrand
  rw [standardMehtaVandermonde_eq_ordered_of_strictAnti
    upper hupper.2]
  ring

end FibonacciRibbonKernel
