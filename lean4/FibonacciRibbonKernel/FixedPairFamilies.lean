import FibonacciRibbonKernel.ActualInvolutions

namespace FibonacciRibbonKernel

open Equiv

universe u v w

/-- An ordered family of disjoint prescribed transpositions. -/
def FixedPairFamily (α : Type u) [DecidableEq α] : ℕ → Type u
  | 0 => PUnit
  | pairCount + 1 =>
      Σ left : α, Σ right : α,
        PLift (left ≠ right) ×
          FixedPairFamily (Function.fixedPoints (Equiv.swap left right)) pairCount

noncomputable instance fixedPairFamilyFintype
    (α : Type*) [Fintype α] [DecidableEq α] (pairCount : ℕ) :
    Fintype (FixedPairFamily α pairCount) := by
  induction pairCount generalizing α with
  | zero => simp [FixedPairFamily]; infer_instance
  | succ pairCount ih =>
      classical
      simp only [FixedPairFamily]
      letI (left right : α) (hne : PLift (left ≠ right)) :
          Fintype (FixedPairFamily
            (Function.fixedPoints (Equiv.swap left right)) pairCount) :=
        ih _
      infer_instance

/-- Type of labels left after deleting every prescribed pair. -/
def FixedPairFamily.RemainingType :
    {α : Type u} → [DecidableEq α] → {pairCount : ℕ} →
      FixedPairFamily α pairCount → Type u
  | α, _, 0, _ => α
  | _, _, _ + 1, ⟨_, _, _, tail⟩ => tail.RemainingType

noncomputable instance fixedPairFamilyRemainingFintype
    {α : Type*} [Fintype α] [DecidableEq α] {pairCount : ℕ}
    (family : FixedPairFamily α pairCount) :
    Fintype family.RemainingType := by
  induction pairCount generalizing α with
  | zero => simpa [FixedPairFamily.RemainingType]
  | succ pairCount ih =>
      obtain ⟨left, right, hne, tail⟩ := family
      simpa [FixedPairFamily.RemainingType] using ih tail

/-- An involution contains every transposition in the family. -/
def FixedPairFamily.Contains :
    {α : Type u} → [Fintype α] → [DecidableEq α] → {pairCount : ℕ} →
      (family : FixedPairFamily α pairCount) → ActualInvolutionOn α → Type u
  | _, _, _, 0, _, _ => PUnit
  | _, _, _, _ + 1, ⟨left, right, hne, tail⟩, permutation =>
      Σ hpair : PLift (permutation.1 left = right),
        tail.Contains
          ((actualInvolutionFixedPairEquiv left right hne.down)
            ⟨permutation, hpair.down⟩)

/-- Delete all prescribed pairs, retaining the arbitrary involution on the complement. -/
noncomputable def FixedPairFamily.containsEquivRemaining
    {α : Type*} [Fintype α] [DecidableEq α] {pairCount : ℕ}
    (family : FixedPairFamily α pairCount) :
    (Σ permutation : ActualInvolutionOn α, family.Contains permutation) ≃
      ActualInvolutionOn family.RemainingType := by
  induction pairCount generalizing α with
  | zero =>
      exact
        { toFun := fun permutation => permutation.1
          invFun := fun permutation => ⟨permutation, PUnit.unit⟩
          left_inv := fun permutation => by cases permutation.2; rfl
          right_inv := fun _ => rfl }
  | succ pairCount ih =>
      obtain ⟨left, right, hne, tail⟩ := family
      change (Σ permutation : ActualInvolutionOn α,
          Σ hpair : PLift (permutation.1 left = right),
            tail.Contains
              ((actualInvolutionFixedPairEquiv left right hne.down)
                ⟨permutation, hpair.down⟩)) ≃
        ActualInvolutionOn tail.RemainingType
      let pairedType :=
        {permutation : ActualInvolutionOn α // permutation.1 left = right}
      let first :
          (Σ permutation : ActualInvolutionOn α,
            Σ hpair : PLift (permutation.1 left = right),
              tail.Contains
                ((actualInvolutionFixedPairEquiv left right hne.down)
                  ⟨permutation, hpair.down⟩)) ≃
          (Σ paired : pairedType,
            tail.Contains
              ((actualInvolutionFixedPairEquiv left right hne.down) paired)) :=
        { toFun := fun permutation => by
            exact ⟨⟨permutation.1, permutation.2.1.down⟩, permutation.2.2⟩
          invFun := fun paired =>
            ⟨paired.1.1, ⟨PLift.up paired.1.2, paired.2⟩⟩
          left_inv := fun permutation => by
            apply Sigma.ext rfl
            apply heq_of_eq
            apply Sigma.ext
            · exact Subsingleton.elim _ _
            · rfl
          right_inv := fun paired => by
            apply Sigma.ext
            · apply Subtype.ext; rfl
            · rfl }
      let second :
          (Σ paired : pairedType,
            tail.Contains ((actualInvolutionFixedPairEquiv left right hne.down) paired)) ≃
          (Σ remaining : ActualInvolutionOn
              (Function.fixedPoints (Equiv.swap left right)),
            tail.Contains remaining) :=
        Equiv.sigmaCongr (actualInvolutionFixedPairEquiv left right hne.down)
          (fun _ => Equiv.refl _)
      exact first.trans (second.trans (ih tail))

noncomputable instance fixedPairFamilyCarrierFintype
    {α : Type u} [Fintype α] [DecidableEq α] {pairCount : ℕ}
    (family : FixedPairFamily α pairCount) :
    Fintype (Σ permutation : ActualInvolutionOn α, family.Contains permutation) :=
  Fintype.ofEquiv (ActualInvolutionOn family.RemainingType)
    family.containsEquivRemaining.symm

theorem card_fixedPoints_swap
    {α : Type*} [Fintype α] [DecidableEq α]
    (left right : α) (hne : left ≠ right) :
    Fintype.card (Function.fixedPoints (Equiv.swap left right)) =
      Fintype.card α - 2 := by
  rw [Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType,
    Equiv.Perm.card_support_swap hne]

theorem FixedPairFamily.card_remaining
    {α : Type*} [Fintype α] [DecidableEq α] {pairCount : ℕ}
    (family : FixedPairFamily α pairCount) :
    Fintype.card family.RemainingType = Fintype.card α - 2 * pairCount := by
  induction pairCount generalizing α with
  | zero => rfl
  | succ pairCount ih =>
      obtain ⟨left, right, hne, tail⟩ := family
      change Fintype.card tail.RemainingType = _
      rw [ih tail, card_fixedPoints_swap left right hne.down]
      omega

theorem FixedPairFamily.card_containing
    {α : Type*} [Fintype α] [DecidableEq α] {pairCount : ℕ}
    (family : FixedPairFamily α pairCount) :
    Fintype.card
        (Σ permutation : ActualInvolutionOn α, family.Contains permutation) =
      involutionNumber (Fintype.card α - 2 * pairCount) := by
  calc
    Fintype.card (Σ permutation : ActualInvolutionOn α, family.Contains permutation) =
        Fintype.card (ActualInvolutionOn family.RemainingType) :=
      Fintype.card_congr family.containsEquivRemaining
    _ = Fintype.card (ActualInvolution (Fintype.card family.RemainingType)) :=
      Fintype.card_congr (actualInvolutionOnFinEquiv family.RemainingType)
    _ = actualInvolutionNumber (Fintype.card family.RemainingType) := rfl
    _ = involutionNumber (Fintype.card family.RemainingType) :=
      actualInvolutionNumber_eq_involutionNumber _
    _ = involutionNumber (Fintype.card α - 2 * pairCount) := by
      rw [family.card_remaining]

/-- The literal pair equations after embedding a family in an ambient label type. -/
def FixedPairFamily.HoldsUnder :
    {α : Type u} → [DecidableEq α] → {pairCount : ℕ} →
      (family : FixedPairFamily α pairCount) →
      {β : Type*} → (α ↪ β) → Equiv.Perm β → Prop
  | _, _, 0, _, _, _, _ => True
  | _, _, _ + 1, ⟨left, right, _, tail⟩, _, embedding, permutation =>
      permutation (embedding left) = embedding right ∧
        tail.HoldsUnder
          ((Function.Embedding.subtype _).trans embedding) permutation

theorem FixedPairFamily.holdsUnder_iff_of_rel
    {α : Type u} [DecidableEq α] {pairCount : ℕ}
    (family : FixedPairFamily α pairCount)
    {β : Type v} {γ : Type w} (leftEmbedding : α ↪ β) (leftPermutation : Equiv.Perm β)
    (rightEmbedding : α ↪ γ) (rightPermutation : Equiv.Perm γ)
    (hrel : ∀ first second,
      leftPermutation (leftEmbedding first) = leftEmbedding second ↔
        rightPermutation (rightEmbedding first) = rightEmbedding second) :
    family.HoldsUnder leftEmbedding leftPermutation ↔
      family.HoldsUnder rightEmbedding rightPermutation := by
  induction pairCount generalizing α β γ with
  | zero => simp [FixedPairFamily.HoldsUnder]
  | succ pairCount ih =>
      obtain ⟨left, right, hne, tail⟩ := family
      change (_ ∧ tail.HoldsUnder _ leftPermutation) ↔
        (_ ∧ tail.HoldsUnder _ rightPermutation)
      apply and_congr (hrel left right)
      apply ih tail
      intro first second
      exact hrel first.1 second.1

theorem FixedPairFamily.contains_nonempty_iff_holds
    {α : Type u} [Fintype α] [DecidableEq α] {pairCount : ℕ}
    (family : FixedPairFamily α pairCount) (permutation : ActualInvolutionOn α) :
    Nonempty (family.Contains permutation) ↔
      family.HoldsUnder (Function.Embedding.refl α) permutation.1 := by
  induction pairCount generalizing α with
  | zero =>
      constructor
      · intro _; trivial
      · intro _; exact ⟨PUnit.unit⟩
  | succ pairCount ih =>
      obtain ⟨left, right, hne, tail⟩ := family
      change Nonempty
          (Σ hpair : PLift (permutation.1 left = right),
            tail.Contains
              ((actualInvolutionFixedPairEquiv left right hne.down)
                ⟨permutation, hpair.down⟩)) ↔
        permutation.1 left = right ∧
          tail.HoldsUnder (Function.Embedding.subtype _) permutation.1
      constructor
      · rintro ⟨hpair, htail⟩
        refine ⟨hpair.down, ?_⟩
        let paired : {permutation : ActualInvolutionOn α //
            permutation.1 left = right} := ⟨permutation, hpair.down⟩
        let restricted := actualInvolutionFixedPairEquiv left right hne.down paired
        have hrestricted := (ih tail restricted).mp ⟨htail⟩
        apply (tail.holdsUnder_iff_of_rel
          (Function.Embedding.refl _) restricted.1
          (Function.Embedding.subtype _) permutation.1 ?_).mp hrestricted
        intro first second
        constructor <;> intro heq
        · have hvalue := congrArg Subtype.val heq
          simpa [restricted, paired] using hvalue
        · apply Subtype.ext
          simpa [restricted, paired] using heq
      · rintro ⟨hpair, htail⟩
        let paired : {permutation : ActualInvolutionOn α //
            permutation.1 left = right} := ⟨permutation, hpair⟩
        let restricted := actualInvolutionFixedPairEquiv left right hne.down paired
        have hrestricted : tail.HoldsUnder (Function.Embedding.refl _) restricted.1 := by
          apply (tail.holdsUnder_iff_of_rel
            (Function.Embedding.refl _) restricted.1
            (Function.Embedding.subtype _) permutation.1 ?_).mpr htail
          intro first second
          constructor <;> intro heq
          · have hvalue := congrArg Subtype.val heq
            simpa [restricted, paired] using hvalue
          · apply Subtype.ext
            simpa [restricted, paired] using heq
        obtain ⟨witness⟩ := (ih tail restricted).mpr hrestricted
        exact ⟨⟨PLift.up hpair, witness⟩⟩

instance FixedPairFamily.containsSubsingleton
    {α : Type u} [Fintype α] [DecidableEq α] {pairCount : ℕ}
    (family : FixedPairFamily α pairCount) (permutation : ActualInvolutionOn α) :
    Subsingleton (family.Contains permutation) := by
  induction pairCount generalizing α with
  | zero =>
      change Subsingleton PUnit
      infer_instance
  | succ pairCount ih =>
      obtain ⟨left, right, hne, tail⟩ := family
      change Subsingleton
        (Σ hpair : PLift (permutation.1 left = right),
          tail.Contains
            ((actualInvolutionFixedPairEquiv left right hne.down)
              ⟨permutation, hpair.down⟩))
      constructor
      intro first second
      cases first with
      | mk firstProof firstTail =>
        cases second with
        | mk secondProof secondTail =>
          have hproof : firstProof = secondProof := Subsingleton.elim _ _
          subst secondProof
          let restricted :=
            (actualInvolutionFixedPairEquiv left right hne.down)
              ⟨permutation, firstProof.down⟩
          letI : Subsingleton (tail.Contains restricted) := ih tail restricted
          exact Sigma.ext rfl (heq_of_eq (Subsingleton.elim _ _))

noncomputable def FixedPairFamily.holdsCarrierEquivContains
    {α : Type u} [Fintype α] [DecidableEq α] {pairCount : ℕ}
    (family : FixedPairFamily α pairCount) :
    {permutation : ActualInvolutionOn α //
      family.HoldsUnder (Function.Embedding.refl α) permutation.1} ≃
      (Σ permutation : ActualInvolutionOn α, family.Contains permutation) where
  toFun permutation :=
    ⟨permutation.1,
      Classical.choice ((family.contains_nonempty_iff_holds permutation.1).mpr permutation.2)⟩
  invFun permutation :=
    ⟨permutation.1,
      (family.contains_nonempty_iff_holds permutation.1).mp ⟨permutation.2⟩⟩
  left_inv permutation := by apply Subtype.ext; rfl
  right_inv permutation := by
    letI : Subsingleton (family.Contains permutation.1) :=
      family.containsSubsingleton permutation.1
    exact Sigma.ext rfl (heq_of_eq (Subsingleton.elim _ _))

/-- Transport a prescribed family through an injective relabelling. -/
def FixedPairFamily.mapEmbedding
    {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
    (embedding : α ↪ β) :
    {pairCount : ℕ} → FixedPairFamily α pairCount → FixedPairFamily β pairCount
  | 0, _ => PUnit.unit
  | _ + 1, ⟨left, right, hne, tail⟩ => by
      let tailEmbedding :
          Function.fixedPoints (Equiv.swap left right) ↪
            Function.fixedPoints (Equiv.swap (embedding left) (embedding right)) :=
        ⟨fun point => ⟨embedding point.1, by
            have hleft : point.1 ≠ left := by
              intro heq
              have hfixed := point.2
              change Equiv.swap left right point.1 = point.1 at hfixed
              rw [heq] at hfixed
              have hswap : Equiv.swap left right left = right := by simp
              exact hne.down (hswap.symm.trans hfixed).symm
            have hright : point.1 ≠ right := by
              intro heq
              have hfixed := point.2
              change Equiv.swap left right point.1 = point.1 at hfixed
              rw [heq] at hfixed
              have hswap : Equiv.swap left right right = left := by simp
              exact hne.down (hswap.symm.trans hfixed)
            have hleftEmbedding : embedding point.1 ≠ embedding left :=
              fun heq => hleft (embedding.injective heq)
            have hrightEmbedding : embedding point.1 ≠ embedding right :=
              fun heq => hright (embedding.injective heq)
            change Equiv.swap (embedding left) (embedding right) (embedding point.1) =
              embedding point.1
            simp [Equiv.swap_apply_def, hleftEmbedding, hrightEmbedding]⟩,
          fun leftPoint rightPoint heq => by
            apply Subtype.ext
            exact embedding.injective (congrArg Subtype.val heq)⟩
      exact ⟨embedding left, embedding right,
        PLift.up (fun heq => hne.down (embedding.injective heq)),
        tail.mapEmbedding tailEmbedding⟩

theorem FixedPairFamily.mapEmbedding_holdsUnder
    {α : Type u} {β : Type v} {γ : Type w} [DecidableEq α] [DecidableEq β]
    (embedding : α ↪ β) {pairCount : ℕ}
    (family : FixedPairFamily α pairCount)
    (ambient : β ↪ γ) (permutation : Equiv.Perm γ) :
    (family.mapEmbedding embedding).HoldsUnder ambient permutation ↔
      family.HoldsUnder (embedding.trans ambient) permutation := by
  induction pairCount generalizing α β γ with
  | zero => simp [FixedPairFamily.HoldsUnder]
  | succ pairCount ih =>
      obtain ⟨left, right, hne, tail⟩ := family
      change (_ ∧
          (tail.mapEmbedding _).HoldsUnder _ permutation) ↔
        (_ ∧ tail.HoldsUnder _ permutation)
      apply and_congr Iff.rfl
      rw [ih]
      apply tail.holdsUnder_iff_of_rel _ permutation _ permutation
      intro first second
      rfl

/-- Each canonical path matching supplies its ordered family of adjacent transpositions. -/
def PathMatching.fixedPairFamily :
    {vertices edges : ℕ} → PathMatching vertices edges →
      FixedPairFamily (Fin vertices) edges
  | 0, 0, _ => PUnit.unit
  | 0, _ + 1, matching => nomatch matching
  | 1, 0, _ => PUnit.unit
  | 1, _ + 1, matching => nomatch matching
  | _ + 2, 0, _ => PUnit.unit
  | vertices + 2, edges + 1, Sum.inl matching =>
      matching.fixedPairFamily.mapEmbedding Fin.castSuccEmb
  | vertices + 2, edges + 1, Sum.inr matching => by
      let left : Fin (vertices + 2) := ⟨vertices, by omega⟩
      let right : Fin (vertices + 2) := Fin.last (vertices + 1)
      let frontEmbedding : Fin vertices ↪
          Function.fixedPoints (Equiv.swap left right) :=
        ⟨fun point => ⟨point.castSucc.castSucc, by
            change Equiv.swap left right point.castSucc.castSucc =
              point.castSucc.castSucc
            simp only [Equiv.swap_apply_def]
            split_ifs with hleft hright
            · have hvalue := congrArg Fin.val hleft
              simp [left] at hvalue
              omega
            · have hvalue := congrArg Fin.val hright
              simp [right] at hvalue
              omega
            · rfl⟩,
          fun first second heq => by
            apply Fin.ext
            have hvalue := congrArg (fun point => point.1.val) heq
            simpa using hvalue⟩
      exact ⟨left, right, PLift.up (by
          intro heq
          have hvalue := congrArg Fin.val heq
          simp [left, right] at hvalue),
        matching.fixedPairFamily.mapEmbedding frontEmbedding⟩

def PathMatching.edgeLeft
    {vertices edges : ℕ} (matching : PathMatching vertices edges)
    (location : ℕ) (hlocation : location ∈ matching.edgePositions) : Fin vertices :=
  ⟨location, by
    have hbound := matching.edgePositions_subset hlocation
    simp only [Finset.mem_range] at hbound
    omega⟩

def PathMatching.edgeRight
    {vertices edges : ℕ} (matching : PathMatching vertices edges)
    (location : ℕ) (hlocation : location ∈ matching.edgePositions) : Fin vertices :=
  ⟨location + 1, by
    have hbound := matching.edgePositions_subset hlocation
    simp only [Finset.mem_range] at hbound
    omega⟩

def PathMatching.HoldsUnder
    {vertices edges : ℕ} (matching : PathMatching vertices edges)
    {β : Type*} (embedding : Fin vertices ↪ β) (permutation : Equiv.Perm β) : Prop :=
  ∀ location, ∀ hlocation : location ∈ matching.edgePositions,
    permutation (embedding (matching.edgeLeft location hlocation)) =
      embedding (matching.edgeRight location hlocation)

theorem PathMatching.fixedPairFamily_holdsUnder
    {vertices edges : ℕ} (matching : PathMatching vertices edges)
    {β : Type*} (embedding : Fin vertices ↪ β) (permutation : Equiv.Perm β) :
    matching.fixedPairFamily.HoldsUnder embedding permutation ↔
      matching.HoldsUnder embedding permutation := by
  induction vertices using Nat.twoStepInduction generalizing edges β with
  | zero =>
      cases edges with
      | zero => simp [PathMatching.HoldsUnder, PathMatching.edgePositions,
          FixedPairFamily.HoldsUnder]
      | succ edges => exact PEmpty.elim matching
  | one =>
      cases edges with
      | zero => simp [PathMatching.HoldsUnder, PathMatching.edgePositions,
          FixedPairFamily.HoldsUnder]
      | succ edges => exact PEmpty.elim matching
  | more vertices ih ihSucc =>
      cases edges with
      | zero => simp [PathMatching.HoldsUnder, PathMatching.edgePositions,
          FixedPairFamily.HoldsUnder]
      | succ edges =>
          cases matching with
          | inl matching =>
              rw [show @PathMatching.fixedPairFamily (vertices + 2) (edges + 1)
                  (Sum.inl matching) =
                matching.fixedPairFamily.mapEmbedding Fin.castSuccEmb by rfl]
              change (matching.fixedPairFamily.mapEmbedding Fin.castSuccEmb).HoldsUnder
                  embedding permutation ↔
                matching.HoldsUnder (Fin.castSuccEmb.trans embedding) permutation
              rw [FixedPairFamily.mapEmbedding_holdsUnder, ihSucc matching]
          | inr matching =>
              let left : Fin (vertices + 2) := ⟨vertices, by omega⟩
              let right : Fin (vertices + 2) := Fin.last (vertices + 1)
              let frontEmbedding : Fin vertices ↪
                  Function.fixedPoints (Equiv.swap left right) :=
                ⟨fun point => ⟨point.castSucc.castSucc, by
                    change Equiv.swap left right point.castSucc.castSucc =
                      point.castSucc.castSucc
                    simp only [Equiv.swap_apply_def]
                    split_ifs with hleft hright
                    · have hvalue := congrArg Fin.val hleft
                      simp [left] at hvalue
                      omega
                    · have hvalue := congrArg Fin.val hright
                      simp [right] at hvalue
                      omega
                    · rfl⟩,
                  fun first second heq => by
                    apply Fin.ext
                    have hvalue := congrArg (fun point => point.1.val) heq
                    simpa using hvalue⟩
              let remainingEmbedding : Fin vertices ↪ β :=
                frontEmbedding.trans
                  ((Function.Embedding.subtype _).trans embedding)
              rw [show @PathMatching.fixedPairFamily (vertices + 2) (edges + 1)
                  (Sum.inr matching) =
                  (⟨left, right, PLift.up (by
                    intro heq
                    have hvalue := congrArg Fin.val heq
                    simp [left, right] at hvalue),
                    matching.fixedPairFamily.mapEmbedding frontEmbedding⟩ :
                    FixedPairFamily (Fin (vertices + 2)) (edges + 1)) by rfl]
              change (permutation (embedding left) = embedding right ∧
                  (matching.fixedPairFamily.mapEmbedding frontEmbedding).HoldsUnder
                    ((Function.Embedding.subtype _).trans embedding) permutation) ↔
                @PathMatching.HoldsUnder (vertices + 2) (edges + 1)
                  (Sum.inr matching) β embedding permutation
              rw [FixedPairFamily.mapEmbedding_holdsUnder, ih matching]
              constructor
              · rintro ⟨hlast, htail⟩ location hlocation
                simp only [PathMatching.edgePositions, Finset.mem_insert] at hlocation
                rcases hlocation with rfl | hlocation
                · calc
                    permutation (embedding
                        (@PathMatching.edgeLeft (location + 2) (edges + 1)
                          (Sum.inr matching) location
                          (by simp [PathMatching.edgePositions]))) =
                        permutation (embedding left) := by
                      apply congrArg permutation
                      apply congrArg embedding
                      apply Fin.ext
                      rfl
                    _ = embedding right := hlast
                    _ = embedding
                        (@PathMatching.edgeRight (location + 2) (edges + 1)
                          (Sum.inr matching) location
                          (by simp [PathMatching.edgePositions])) := by
                      apply congrArg embedding
                      apply Fin.ext
                      rfl
                · have := htail location hlocation
                  simpa [PathMatching.edgeLeft, PathMatching.edgeRight,
                    Function.Embedding.trans_apply, remainingEmbedding,
                    frontEmbedding] using this
              · intro hall
                constructor
                · have := hall vertices (by simp [PathMatching.edgePositions])
                  calc
                    permutation (embedding left) =
                        permutation (embedding
                          (@PathMatching.edgeLeft (vertices + 2) (edges + 1)
                            (Sum.inr matching) vertices
                            (by simp [PathMatching.edgePositions]))) := by
                      apply congrArg permutation
                      apply congrArg embedding
                      apply Fin.ext
                      rfl
                    _ = embedding
                        (@PathMatching.edgeRight (vertices + 2) (edges + 1)
                          (Sum.inr matching) vertices
                          (by simp [PathMatching.edgePositions])) := this
                    _ = embedding right := by
                      apply congrArg embedding
                      apply Fin.ext
                      rfl
                · intro location hlocation
                  have := hall location (by
                    simp [PathMatching.edgePositions, hlocation])
                  simpa [PathMatching.edgeLeft, PathMatching.edgeRight,
                    Function.Embedding.trans_apply, remainingEmbedding,
                    frontEmbedding] using this

theorem PathMatching.card_involutions_containing_family
    {vertices edges : ℕ} (matching : PathMatching vertices edges) :
    Fintype.card
        (Σ permutation : ActualInvolutionOn (Fin vertices),
          matching.fixedPairFamily.Contains permutation) =
      involutionNumber (vertices - 2 * edges) := by
  simpa using matching.fixedPairFamily.card_containing

def ActualInvolutionMatchingIntersection
    {vertices edges : ℕ} (matching : PathMatching vertices edges) :=
  {permutation : ActualInvolutionOn (Fin vertices) //
    matching.HoldsUnder (Function.Embedding.refl _) permutation.1}

noncomputable instance actualInvolutionMatchingIntersectionFintype
    {vertices edges : ℕ} (matching : PathMatching vertices edges) :
    Fintype (ActualInvolutionMatchingIntersection matching) :=
  classicalSubtypeFintype _

theorem actualInvolutionMatchingIntersection_card
    {vertices edges : ℕ} (matching : PathMatching vertices edges) :
    Fintype.card (ActualInvolutionMatchingIntersection matching) =
      involutionNumber (vertices - 2 * edges) := by
  unfold ActualInvolutionMatchingIntersection
  letI : Fintype
      {permutation : ActualInvolutionOn (Fin vertices) //
        matching.HoldsUnder (Function.Embedding.refl _) permutation.1} :=
    classicalSubtypeFintype _
  letI : Fintype
      {permutation : ActualInvolutionOn (Fin vertices) //
        matching.fixedPairFamily.HoldsUnder
          (Function.Embedding.refl _) permutation.1} :=
    classicalSubtypeFintype _
  let semanticEquiv :
      {permutation : ActualInvolutionOn (Fin vertices) //
        matching.HoldsUnder (Function.Embedding.refl _) permutation.1} ≃
      {permutation : ActualInvolutionOn (Fin vertices) //
        matching.fixedPairFamily.HoldsUnder
          (Function.Embedding.refl _) permutation.1} :=
    Equiv.subtypeEquivRight fun permutation =>
      (matching.fixedPairFamily_holdsUnder
        (Function.Embedding.refl _) permutation.1).symm
  calc
    Fintype.card
        {permutation : ActualInvolutionOn (Fin vertices) //
          matching.HoldsUnder (Function.Embedding.refl _) permutation.1} =
        Fintype.card
          (Σ permutation : ActualInvolutionOn (Fin vertices),
            matching.fixedPairFamily.Contains permutation) :=
      Fintype.card_congr
        (semanticEquiv.trans matching.fixedPairFamily.holdsCarrierEquivContains)
    _ = involutionNumber (vertices - 2 * edges) :=
      matching.card_involutions_containing_family

end FibonacciRibbonKernel
