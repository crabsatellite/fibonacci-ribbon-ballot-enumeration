import FibonacciRibbonKernel.StableTransform
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Finite

namespace FibonacciRibbonKernel

open Equiv

@[reducible] noncomputable def classicalSubtypeFintype
    {α : Type*} [Fintype α] (predicate : α → Prop) :
    Fintype {value : α // predicate value} := by
  classical
  let filtered := Finset.univ.filter predicate
  let filteredType := {value : α // value ∈ filtered}
  let equivalence : filteredType ≃ {value : α // predicate value} :=
    { toFun := fun value => ⟨value.1, (Finset.mem_filter.mp value.2).2⟩
      invFun := fun value =>
        ⟨value.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, value.2⟩⟩
      left_inv := fun value => by apply Subtype.ext; rfl
      right_inv := fun value => by apply Subtype.ext; rfl }
  exact Fintype.ofEquiv filteredType equivalence

/-- Literal involutive permutations of `Fin size`. -/
def ActualInvolution (size : ℕ) :=
  {permutation : Equiv.Perm (Fin size) // Function.Involutive permutation}

def ActualInvolutionOn (α : Type*) :=
  {permutation : Equiv.Perm α // Function.Involutive permutation}

noncomputable instance actualInvolutionFintype (size : ℕ) :
    Fintype (ActualInvolution size) :=
  classicalSubtypeFintype _

noncomputable instance actualInvolutionOnFintype
    (α : Type*) [Fintype α] : Fintype (ActualInvolutionOn α) := by
  classical
  exact classicalSubtypeFintype _

def actualInvolutionOnEquivOfEquiv
    {α β : Type*} (equivalence : α ≃ β) :
    ActualInvolutionOn α ≃ ActualInvolutionOn β where
  toFun permutation :=
    ⟨Equiv.permCongr equivalence permutation.1, by
      intro point
      simpa [Equiv.permCongr_apply] using
        congrArg equivalence (permutation.2 (equivalence.symm point))⟩
  invFun permutation :=
    ⟨Equiv.permCongr equivalence.symm permutation.1, by
      intro point
      simpa [Equiv.permCongr_apply] using
        congrArg equivalence.symm (permutation.2 (equivalence point))⟩
  left_inv permutation := by
    apply Subtype.ext
    ext point
    simp [Equiv.permCongr_apply]
  right_inv permutation := by
    apply Subtype.ext
    ext point
    simp [Equiv.permCongr_apply]

noncomputable def actualInvolutionOnFinEquiv
    (α : Type*) [Fintype α] :
    ActualInvolutionOn α ≃ ActualInvolution (Fintype.card α) :=
  actualInvolutionOnEquivOfEquiv (Fintype.equivFin α)

noncomputable instance decomposeFiberFintype
    (size : ℕ) (pivot : Fin (size + 1)) :
    Fintype {remaining : Equiv.Perm (Fin size) //
      Function.Involutive
        (Equiv.Perm.decomposeFin.symm (pivot, remaining))} :=
  classicalSubtypeFintype _

noncomputable instance fixedActualInvolutionFintype
    (size : ℕ) (pivot : Fin size) :
    Fintype {remaining : ActualInvolution size // remaining.1 pivot = pivot} :=
  classicalSubtypeFintype _

theorem decomposeFin_zero_involutive_iff
    {size : ℕ} (remaining : Equiv.Perm (Fin size)) :
    Function.Involutive
        (Equiv.Perm.decomposeFin.symm ((0 : Fin (size + 1)), remaining)) ↔
      Function.Involutive remaining := by
  constructor
  · intro hinvolution label
    have h := hinvolution label.succ
    simpa using h
  · intro hinvolution label
    refine Fin.cases ?_ (fun smaller => ?_) label
    · simp
    · simpa using congrArg Fin.succ (hinvolution smaller)

theorem decomposeFin_succ_involutive_iff
    {size : ℕ} (partner : Fin size) (remaining : Equiv.Perm (Fin size)) :
    Function.Involutive
        (Equiv.Perm.decomposeFin.symm (partner.succ, remaining)) ↔
      Function.Involutive remaining ∧ remaining partner = partner := by
  constructor
  · intro hinvolution
    have hzero := hinvolution (0 : Fin (size + 1))
    have hpartner : remaining partner = partner := by
      have hvalue := congrArg Fin.val hzero
      simp only [Equiv.Perm.decomposeFin_symm_apply_zero,
        Equiv.Perm.decomposeFin_symm_apply_succ, Fin.val_zero] at hvalue
      by_contra hne
      simp [Equiv.swap_apply_def, hne] at hvalue
    refine ⟨?_, hpartner⟩
    intro label
    by_cases hlabel : label = partner
    · simp [hlabel, hpartner]
    · have hremainingNe : remaining label ≠ partner := by
        intro heq
        have := remaining.injective (heq.trans hpartner.symm)
        exact hlabel this
      have h := hinvolution label.succ
      have hfirst :
          Equiv.Perm.decomposeFin.symm (partner.succ, remaining) label.succ =
            (remaining label).succ := by
        rw [Equiv.Perm.decomposeFin_symm_apply_succ]
        simp [Equiv.swap_apply_def, hremainingNe]
      rw [hfirst, Equiv.Perm.decomposeFin_symm_apply_succ] at h
      have hsecondNe : remaining (remaining label) ≠ partner := by
        intro heq
        have := remaining.injective (heq.trans hpartner.symm)
        exact hremainingNe this
      simp [Equiv.swap_apply_def, hsecondNe] at h
      exact h
  · rintro ⟨hinvolution, hpartner⟩
    intro label
    refine Fin.cases ?_ (fun smaller => ?_) label
    · simp [hpartner]
    · by_cases hlabel : smaller = partner
      · subst smaller
        simp [hpartner]
      · have hremainingNe : remaining smaller ≠ partner := by
          intro heq
          have := remaining.injective (heq.trans hpartner.symm)
          exact hlabel this
        simp [Equiv.Perm.decomposeFin_symm_apply_succ,
          Equiv.swap_apply_def, hremainingNe, hinvolution smaller, hlabel]

theorem perm_involutive_iff_sq_eq_one
    {α : Type*} (permutation : Equiv.Perm α) :
    Function.Involutive permutation ↔ permutation * permutation = 1 := by
  constructor
  · intro hinvolution
    ext point
    exact hinvolution point
  · intro hsquare point
    exact congrArg (fun value : Equiv.Perm α => value point) hsquare

theorem perm_conjugate_involutive
    {α : Type*} (conjugator permutation : Equiv.Perm α)
    (hinvolution : Function.Involutive permutation) :
    Function.Involutive (conjugator * permutation * conjugator⁻¹) := by
  rw [perm_involutive_iff_sq_eq_one] at hinvolution ⊢
  calc
    (conjugator * permutation * conjugator⁻¹) *
        (conjugator * permutation * conjugator⁻¹) =
      conjugator * (permutation * permutation) * conjugator⁻¹ := by group
    _ = 1 := by rw [hinvolution]; simp

/-- Involutions fixing zero are equivalent to involutions on the remaining labels. -/
noncomputable def actualInvolutionFixZeroEquiv (size : ℕ) :
    {permutation : ActualInvolution (size + 1) // permutation.1 0 = 0} ≃
      ActualInvolution size where
  toFun permutation := by
    let pair := Equiv.Perm.decomposeFin permutation.1.1
    have hpairZero : pair.1 = 0 := by
      have hreconstruct := Equiv.Perm.decomposeFin.symm_apply_apply permutation.1.1
      calc
        pair.1 = Equiv.Perm.decomposeFin.symm pair 0 := by
          rw [Equiv.Perm.decomposeFin_symm_apply_zero]
        _ = permutation.1.1 0 := congrArg
          (fun value : Equiv.Perm (Fin (size + 1)) => value 0) hreconstruct
        _ = 0 := permutation.2
    refine ⟨pair.2, ?_⟩
    apply (decomposeFin_zero_involutive_iff pair.2).mp
    have hreconstruct := Equiv.Perm.decomposeFin.symm_apply_apply permutation.1.1
    have heq : Equiv.Perm.decomposeFin.symm ((0 : Fin (size + 1)), pair.2) =
        permutation.1.1 := by
      calc
        Equiv.Perm.decomposeFin.symm ((0 : Fin (size + 1)), pair.2) =
            Equiv.Perm.decomposeFin.symm pair := by
          apply congrArg Equiv.Perm.decomposeFin.symm
          exact Prod.ext hpairZero.symm rfl
        _ = permutation.1.1 := hreconstruct
    rw [heq]
    exact permutation.1.2
  invFun remaining := by
    let permutation := Equiv.Perm.decomposeFin.symm
      ((0 : Fin (size + 1)), remaining.1)
    refine ⟨⟨permutation,
      (decomposeFin_zero_involutive_iff remaining.1).mpr remaining.2⟩, ?_⟩
    simp [permutation]
  left_inv permutation := by
    apply Subtype.ext
    apply Subtype.ext
    let pair := Equiv.Perm.decomposeFin permutation.1.1
    have hpairZero : pair.1 = 0 := by
      have hreconstruct := Equiv.Perm.decomposeFin.symm_apply_apply permutation.1.1
      calc
        pair.1 = Equiv.Perm.decomposeFin.symm pair 0 := by
          rw [Equiv.Perm.decomposeFin_symm_apply_zero]
        _ = permutation.1.1 0 := congrArg
          (fun value : Equiv.Perm (Fin (size + 1)) => value 0) hreconstruct
        _ = 0 := permutation.2
    have hreconstruct := Equiv.Perm.decomposeFin.symm_apply_apply permutation.1.1
    change Equiv.Perm.decomposeFin.symm ((0 : Fin (size + 1)), pair.2) =
      permutation.1.1
    calc
      Equiv.Perm.decomposeFin.symm ((0 : Fin (size + 1)), pair.2) =
          Equiv.Perm.decomposeFin.symm pair := by
        apply congrArg Equiv.Perm.decomposeFin.symm
        exact Prod.ext hpairZero.symm rfl
      _ = permutation.1.1 := hreconstruct
  right_inv remaining := by
    apply Subtype.ext
    change (Equiv.Perm.decomposeFin
      (Equiv.Perm.decomposeFin.symm ((0 : Fin (size + 1)), remaining.1))).2 =
        remaining.1
    rw [Equiv.Perm.decomposeFin.apply_symm_apply]

/-- Conjugation specialized to `Fin`, swapping zero with a chosen label. -/
def conjugateFinZero {size : ℕ} (pivot : Fin (size + 1))
    (permutation : Equiv.Perm (Fin (size + 1))) :
    Equiv.Perm (Fin (size + 1)) :=
  Equiv.swap 0 pivot * permutation * Equiv.swap 0 pivot

theorem conjugateFinZero_involutive
    {size : ℕ} (pivot : Fin (size + 1))
    (permutation : Equiv.Perm (Fin (size + 1)))
    (hinvolution : Function.Involutive permutation) :
    Function.Involutive (conjugateFinZero pivot permutation) := by
  have h := perm_conjugate_involutive (Equiv.swap 0 pivot) permutation hinvolution
  simpa [conjugateFinZero] using h

theorem conjugateFinZero_apply_zero_iff
    {size : ℕ} (pivot : Fin (size + 1))
    (permutation : Equiv.Perm (Fin (size + 1))) :
    conjugateFinZero pivot permutation 0 = 0 ↔ permutation pivot = pivot := by
  constructor
  · intro h
    apply (Equiv.swap 0 pivot).injective
    simpa [conjugateFinZero, Equiv.Perm.mul_apply] using h
  · intro h
    simp [conjugateFinZero, Equiv.Perm.mul_apply, h]

theorem conjugateFinZero_involutive_self
    {size : ℕ} (pivot : Fin (size + 1))
    (permutation : Equiv.Perm (Fin (size + 1))) :
    conjugateFinZero pivot (conjugateFinZero pivot permutation) = permutation := by
  unfold conjugateFinZero
  let swap := Equiv.swap (0 : Fin (size + 1)) pivot
  have hswap : swap * swap = 1 := by
    ext point
    simp [swap]
  change swap * swap * permutation * swap * swap = permutation
  rw [show swap * swap * permutation * swap * swap =
      (swap * swap) * permutation * (swap * swap) by group,
    hswap]
  simp

/-- Involutions fixing any chosen label are equivalent to the smaller involutions. -/
noncomputable def actualInvolutionFixEquiv
    (size : ℕ) (pivot : Fin (size + 1)) :
    {permutation : ActualInvolution (size + 1) //
      permutation.1 pivot = pivot} ≃ ActualInvolution size :=
  let conjugation :
      {permutation : ActualInvolution (size + 1) //
        permutation.1 pivot = pivot} ≃
      {permutation : ActualInvolution (size + 1) //
        permutation.1 0 = 0} :=
    { toFun := fun permutation =>
        ⟨⟨conjugateFinZero pivot permutation.1.1,
          conjugateFinZero_involutive pivot permutation.1.1 permutation.1.2⟩,
          (conjugateFinZero_apply_zero_iff pivot permutation.1.1).mpr permutation.2⟩
      invFun := fun permutation =>
        ⟨⟨conjugateFinZero pivot permutation.1.1,
          conjugateFinZero_involutive pivot permutation.1.1 permutation.1.2⟩,
          (conjugateFinZero_apply_zero_iff pivot
            (conjugateFinZero pivot permutation.1.1)).mp (by
              rw [conjugateFinZero_involutive_self]
              exact permutation.2)⟩
      left_inv := fun permutation => by
        apply Subtype.ext
        apply Subtype.ext
        exact conjugateFinZero_involutive_self pivot permutation.1.1
      right_inv := fun permutation => by
        apply Subtype.ext
        apply Subtype.ext
        exact conjugateFinZero_involutive_self pivot permutation.1.1 }
  conjugation.trans (actualInvolutionFixZeroEquiv size)

noncomputable def actualInvolutionNumber (size : ℕ) : ℕ :=
  Fintype.card (ActualInvolution size)

theorem actualInvolutionNumber_zero : actualInvolutionNumber 0 = 1 := by
  unfold actualInvolutionNumber
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨⟨1, fun point => Fin.elim0 point⟩, ?_⟩
  intro permutation
  apply Subtype.ext
  exact Subsingleton.elim _ _

theorem actualInvolutionNumber_one : actualInvolutionNumber 1 = 1 := by
  unfold actualInvolutionNumber
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨⟨1, fun _ => rfl⟩, ?_⟩
  intro permutation
  apply Subtype.ext
  exact Subsingleton.elim _ _

noncomputable def actualInvolutionDecomposeSigmaEquiv (size : ℕ) :
    ActualInvolution (size + 1) ≃
      (Σ pivot : Fin (size + 1),
        {remaining : Equiv.Perm (Fin size) //
          Function.Involutive
            (Equiv.Perm.decomposeFin.symm (pivot, remaining))}) :=
  let first : ActualInvolution (size + 1) ≃
      {pair : Fin (size + 1) × Equiv.Perm (Fin size) //
        Function.Involutive (Equiv.Perm.decomposeFin.symm pair)} :=
    Equiv.subtypeEquiv Equiv.Perm.decomposeFin (fun permutation => by
      rw [Equiv.Perm.decomposeFin.symm_apply_apply])
  first.trans (Equiv.subtypeProdEquivSigmaSubtype fun pivot remaining =>
    Function.Involutive (Equiv.Perm.decomposeFin.symm (pivot, remaining)))

noncomputable def zeroDecomposeFiberEquiv (size : ℕ) :
    {remaining : Equiv.Perm (Fin size) //
      Function.Involutive
        (Equiv.Perm.decomposeFin.symm ((0 : Fin (size + 1)), remaining))} ≃
      ActualInvolution size :=
  Equiv.subtypeEquivRight fun remaining =>
    decomposeFin_zero_involutive_iff remaining

noncomputable def succDecomposeFiberEquiv
    {size : ℕ} (partner : Fin size) :
    {remaining : Equiv.Perm (Fin size) //
      Function.Involutive
        (Equiv.Perm.decomposeFin.symm (partner.succ, remaining))} ≃
      {remaining : ActualInvolution size // remaining.1 partner = partner} where
  toFun remaining := by
    have hdata := (decomposeFin_succ_involutive_iff partner remaining.1).mp remaining.2
    exact ⟨⟨remaining.1, hdata.1⟩, hdata.2⟩
  invFun remaining :=
    ⟨remaining.1.1,
      (decomposeFin_succ_involutive_iff partner remaining.1.1).mpr
        ⟨remaining.1.2, remaining.2⟩⟩
  left_inv remaining := by apply Subtype.ext; rfl
  right_inv remaining := by apply Subtype.ext; apply Subtype.ext; rfl

theorem actualInvolutionNumber_succ (size : ℕ) :
    actualInvolutionNumber (size + 1) =
      actualInvolutionNumber size + size * actualInvolutionNumber (size - 1) := by
  unfold actualInvolutionNumber
  rw [Fintype.card_congr (actualInvolutionDecomposeSigmaEquiv size),
    Fintype.card_sigma, Fin.sum_univ_succ]
  rw [Fintype.card_congr (zeroDecomposeFiberEquiv size)]
  congr 1
  cases size with
  | zero => simp
  | succ smaller =>
      have hfiber : ∀ partner : Fin (smaller + 1),
          Fintype.card
              {remaining : Equiv.Perm (Fin (smaller + 1)) //
                Function.Involutive
                  (Equiv.Perm.decomposeFin.symm (partner.succ, remaining))} =
            Fintype.card (ActualInvolution smaller) := by
        intro partner
        calc
          _ = Fintype.card
              {remaining : ActualInvolution (smaller + 1) //
                remaining.1 partner = partner} :=
            Fintype.card_congr (succDecomposeFiberEquiv partner)
          _ = Fintype.card (ActualInvolution smaller) :=
            Fintype.card_congr (actualInvolutionFixEquiv smaller partner)
      simp_rw [hfiber]
      simp

theorem actualInvolutionNumber_eq_involutionNumber (size : ℕ) :
    actualInvolutionNumber size = involutionNumber size := by
  induction size using Nat.twoStepInduction with
  | zero => rw [actualInvolutionNumber_zero, involutionNumber_zero]
  | one => rw [actualInvolutionNumber_one, involutionNumber_one]
  | more size ih ihSucc =>
      rw [show size + 2 = (size + 1) + 1 by omega,
        actualInvolutionNumber_succ, involutionNumber_succ,
        ihSucc]
      have hsub : size + 1 - 1 = size := by omega
      rw [hsub, ih]

theorem fixedPair_preserves_swapFixedPoints
    {α : Type*} [DecidableEq α] {left right : α} (hne : left ≠ right)
    (permutation : ActualInvolutionOn α) (hpair : permutation.1 left = right) :
    ∀ point,
      point ∈ Function.fixedPoints (Equiv.swap left right) ↔
        permutation.1 point ∈ Function.fixedPoints (Equiv.swap left right) := by
  have hreverse : permutation.1 right = left := by
    have h := permutation.2 left
    rw [hpair] at h
    exact h
  have hforward : ∀ point,
      point ∈ Function.fixedPoints (Equiv.swap left right) →
        permutation.1 point ∈ Function.fixedPoints (Equiv.swap left right) := by
    intro point hpoint
    have hneLeft : point ≠ left := by
      intro heq
      subst point
      change Equiv.swap left right left = left at hpoint
      have hswap : Equiv.swap left right left = right := by simp
      have : right = left := hswap.symm.trans hpoint
      exact hne this.symm
    have hneRight : point ≠ right := by
      intro heq
      subst point
      change Equiv.swap left right right = right at hpoint
      have hswap : Equiv.swap left right right = left := by simp
      have : left = right := hswap.symm.trans hpoint
      exact hne this
    rw [Function.mem_fixedPoints_iff]
    simp only [Equiv.swap_apply_def]
    split_ifs with hleft hright
    · have hsigma := congrArg permutation.1 hleft
      rw [permutation.2 point, hpair] at hsigma
      exact (hneRight hsigma).elim
    · have hsigma := congrArg permutation.1 hright
      rw [permutation.2 point, hreverse] at hsigma
      exact (hneLeft hsigma).elim
    · rfl
  intro point
  constructor
  · exact hforward point
  · intro himage
    have htwice := hforward (permutation.1 point) himage
    simpa [permutation.2 point] using htwice

/-- Removing one prescribed transposition leaves an arbitrary smaller involution. -/
noncomputable def actualInvolutionFixedPairEquiv
    {α : Type*} [Fintype α] [DecidableEq α]
    (left right : α) (hne : left ≠ right) :
    {permutation : ActualInvolutionOn α // permutation.1 left = right} ≃
      ActualInvolutionOn (Function.fixedPoints (Equiv.swap left right)) where
  toFun permutation := by
    let preservation := fixedPair_preserves_swapFixedPoints hne permutation.1 permutation.2
    let restricted := permutation.1.1.subtypePerm fun point => (preservation point).symm
    refine ⟨restricted, ?_⟩
    intro point
    apply Subtype.ext
    change permutation.1.1 (permutation.1.1 point.1) = point.1
    exact permutation.1.2 point.1
  invFun remaining := by
    let extended := Equiv.Perm.ofSubtype remaining.1
    let swap := Equiv.swap left right
    let permutation := extended * swap
    have hdisjoint : Equiv.Perm.Disjoint extended swap := by
      exact Equiv.Perm.disjoint_ofSubtype_of_memFixedPoints_self remaining.1
    have hinvolution : Function.Involutive permutation := by
      rw [perm_involutive_iff_sq_eq_one]
      have hextended : extended * extended = 1 := by
        dsimp [extended]
        rw [← map_mul,
          (perm_involutive_iff_sq_eq_one remaining.1).mp remaining.2,
          map_one]
      have hswap : swap * swap = 1 := by
        ext point
        simp [swap]
      have hcommute := Equiv.Perm.Disjoint.commute hdisjoint
      calc
        permutation * permutation =
            (extended * extended) * (swap * swap) := by
          dsimp [permutation]
          calc
            (extended * swap) * (extended * swap) =
                extended * (swap * extended) * swap := by group
            _ = extended * (extended * swap) * swap := by
              rw [← hcommute.eq]
            _ = (extended * extended) * (swap * swap) := by group
        _ = 1 := by rw [hextended, hswap, one_mul]
    refine ⟨⟨permutation, hinvolution⟩, ?_⟩
    dsimp [permutation, extended, swap]
    rw [show Equiv.swap left right left = right by simp]
    have hrightNot : right ∉ Function.fixedPoints (Equiv.swap left right) := by
      change Equiv.swap left right right ≠ right
      have hswap : Equiv.swap left right right = left := by simp
      rw [hswap]
      exact hne
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem remaining.1 hrightNot]
  left_inv permutation := by
    apply Subtype.ext
    apply Subtype.ext
    ext point
    by_cases hfixed : point ∈ Function.fixedPoints (Equiv.swap left right)
    · let preservation := fun value =>
        (fixedPair_preserves_swapFixedPoints hne permutation.1 permutation.2 value).symm
      change Equiv.Perm.ofSubtype
          (permutation.1.1.subtypePerm preservation)
          (Equiv.swap left right point) = permutation.1.1 point
      have hswap : Equiv.swap left right point = point := hfixed
      rw [hswap, Equiv.Perm.ofSubtype_apply_of_mem _ hfixed,
        Equiv.Perm.subtypePerm_apply]
    · have hor : point = left ∨ point = right := by
        rw [Function.mem_fixedPoints_iff] at hfixed
        simp only [Equiv.swap_apply_def] at hfixed
        by_cases hleft : point = left
        · exact Or.inl hleft
        · by_cases hright : point = right
          · exact Or.inr hright
          · simp [hleft, hright] at hfixed
      rcases hor with hleft | hright
      · subst point
        let preservation := fun value =>
          (fixedPair_preserves_swapFixedPoints hne permutation.1 permutation.2 value).symm
        change Equiv.Perm.ofSubtype
            (permutation.1.1.subtypePerm preservation)
            (Equiv.swap left right left) = permutation.1.1 left
        rw [show Equiv.swap left right left = right by simp, permutation.2]
        have hrightNot : right ∉ Function.fixedPoints (Equiv.swap left right) := by
          change Equiv.swap left right right ≠ right
          have hswap : Equiv.swap left right right = left := by simp
          rw [hswap]
          exact hne
        rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hrightNot]
      · subst point
        have hreverse : permutation.1.1 right = left := by
          have h := permutation.1.2 left
          rw [permutation.2] at h
          exact h
        let preservation := fun value =>
          (fixedPair_preserves_swapFixedPoints hne permutation.1 permutation.2 value).symm
        change Equiv.Perm.ofSubtype
            (permutation.1.1.subtypePerm preservation)
            (Equiv.swap left right right) = permutation.1.1 right
        rw [show Equiv.swap left right right = left by simp, hreverse]
        have hleftNot : left ∉ Function.fixedPoints (Equiv.swap left right) := by
          change Equiv.swap left right left ≠ left
          have hswap : Equiv.swap left right left = right := by simp
          rw [hswap]
          exact hne.symm
        rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hleftNot]
  right_inv remaining := by
    apply Subtype.ext
    ext point
    change (Equiv.Perm.ofSubtype remaining.1 * Equiv.swap left right) point.1 =
      remaining.1 point
    have hswap : Equiv.swap left right point.1 = point.1 := point.2
    rw [Equiv.Perm.mul_apply, hswap,
      Equiv.Perm.ofSubtype_apply_of_mem remaining.1 point.2]

@[simp] theorem actualInvolutionFixedPairEquiv_apply
    {α : Type*} [Fintype α] [DecidableEq α]
    (left right : α) (hne : left ≠ right)
    (permutation : {permutation : ActualInvolutionOn α //
      permutation.1 left = right})
    (point : Function.fixedPoints (Equiv.swap left right)) :
    ((actualInvolutionFixedPairEquiv left right hne permutation).1 point).1 =
      permutation.1.1 point.1 := by
  rfl

end FibonacciRibbonKernel
