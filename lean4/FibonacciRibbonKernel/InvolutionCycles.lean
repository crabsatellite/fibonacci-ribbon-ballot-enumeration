import FibonacciRibbonKernel.InvolutionNumbers
import Mathlib.Data.Finset.Image

namespace FibonacciRibbonKernel

/-- Map every two-cycle through an embedding of label sets. -/
def mapCycleEdges {α β : Type*} [DecidableEq α] [DecidableEq β]
    (embedding : α ↪ β) (edges : Finset (Finset α)) :
    Finset (Finset β) :=
  edges.map (Finset.mapEmbedding embedding).toEmbedding

set_option linter.unusedVariables false in
/-- Concrete set of two-cycles decoded from the canonical involution code. -/
def InvolutionCode.cycleEdges :
    {size : ℕ} → InvolutionCode size → Finset (Finset (Fin size))
  | 0, _ => ∅
  | 1, _ => ∅
  | size + 2, Sum.inl fixedLargest =>
      mapCycleEdges Fin.castSuccEmb fixedLargest.cycleEdges
  | size + 2, Sum.inr pairedLargest =>
      let partner := pairedLargest.1
      let remainingEmbedding : Fin size ↪ Fin (size + 2) :=
        (Fin.succAboveEmb partner).trans Fin.castSuccEmb
      insert {partner.castSucc, Fin.last (size + 1)}
        (mapCycleEdges remainingEmbedding pairedLargest.2.cycleEdges)

theorem card_mapCycleEdges_edge
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (embedding : α ↪ β) (edge : Finset α) :
    (edge.map embedding).card = edge.card :=
  Finset.card_map (s := edge) embedding

theorem InvolutionCode.cycleEdges_card_two
    {size : ℕ} (code : InvolutionCode size) :
    ∀ edge ∈ code.cycleEdges, edge.card = 2 := by
  induction size using Nat.twoStepInduction with
  | zero => simp [InvolutionCode.cycleEdges]
  | one => simp [InvolutionCode.cycleEdges]
  | more size ih ihSucc =>
      cases code with
      | inl fixedLargest =>
          intro edge hedge
          simp only [InvolutionCode.cycleEdges, mapCycleEdges,
            Finset.mem_map] at hedge
          obtain ⟨source, hsource, rfl⟩ := hedge
          change (source.map Fin.castSuccEmb).card = 2
          rw [Finset.card_map]
          exact ihSucc fixedLargest source hsource
      | inr pairedLargest =>
          intro edge hedge
          simp only [InvolutionCode.cycleEdges, Finset.mem_insert] at hedge
          rcases hedge with rfl | hedge
          · have hne : pairedLargest.1.castSucc ≠ Fin.last (size + 1) := by
              intro heq
              have hval := congrArg Fin.val heq
              simp at hval
              have hp := pairedLargest.1.isLt
              omega
            simp [hne]
          · simp only [mapCycleEdges, Finset.mem_map] at hedge
            obtain ⟨source, hsource, rfl⟩ := hedge
            change (source.map
              ((Fin.succAboveEmb pairedLargest.1).trans Fin.castSuccEmb)).card = 2
            rw [Finset.card_map]
            exact ih pairedLargest.2 source hsource

theorem pairedEdge_disjoint_remaining
    {size : ℕ} (partner : Fin (size + 1)) (edge : Finset (Fin size)) :
    Disjoint ({partner.castSucc, Fin.last (size + 1)} : Finset (Fin (size + 2)))
      (edge.map ((Fin.succAboveEmb partner).trans Fin.castSuccEmb)) := by
  rw [Finset.disjoint_left]
  intro label hlabel hremaining
  simp only [Finset.mem_insert, Finset.mem_singleton] at hlabel
  simp only [Finset.mem_map] at hremaining
  obtain ⟨source, hsource, hsourceEq⟩ := hremaining
  rcases hlabel with hpartner | hlast
  · have heq := hsourceEq.trans hpartner
    have hval := congrArg Fin.val heq
    simp only [Function.Embedding.trans_apply, Fin.succAboveEmb_apply,
      Fin.castSuccEmb_apply, Fin.val_castSucc] at hval
    have hne := Fin.succAbove_ne partner source
    apply hne
    apply Fin.ext
    simpa using hval
  · have heq := hsourceEq.trans hlast
    have hval := congrArg Fin.val heq
    simp only [Function.Embedding.trans_apply, Fin.succAboveEmb_apply,
      Fin.castSuccEmb_apply, Fin.val_castSucc, Fin.val_last] at hval
    have hbound := (partner.succAbove source).isLt
    omega

/-- Distinct decoded two-cycles are pairwise disjoint. -/
theorem InvolutionCode.cycleEdges_pairwise_disjoint
    {size : ℕ} (code : InvolutionCode size) :
    ∀ first ∈ code.cycleEdges, ∀ second ∈ code.cycleEdges,
      first ≠ second → Disjoint first second := by
  induction size using Nat.twoStepInduction with
  | zero => simp [InvolutionCode.cycleEdges]
  | one => simp [InvolutionCode.cycleEdges]
  | more size ih ihSucc =>
      cases code with
      | inl fixedLargest =>
          intro first hfirst second hsecond hne
          simp only [InvolutionCode.cycleEdges, mapCycleEdges,
            Finset.mem_map] at hfirst hsecond
          obtain ⟨firstSource, hfirstSource, rfl⟩ := hfirst
          obtain ⟨secondSource, hsecondSource, rfl⟩ := hsecond
          change Disjoint (firstSource.map Fin.castSuccEmb)
            (secondSource.map Fin.castSuccEmb)
          rw [Finset.disjoint_map]
          apply ihSucc fixedLargest firstSource hfirstSource
            secondSource hsecondSource
          intro heq
          apply hne
          subst secondSource
          rfl
      | inr pairedLargest =>
          intro first hfirst second hsecond hne
          simp only [InvolutionCode.cycleEdges, Finset.mem_insert] at hfirst hsecond
          rcases hfirst with rfl | hfirst
          · rcases hsecond with rfl | hsecond
            · exact (hne rfl).elim
            · simp only [mapCycleEdges, Finset.mem_map] at hsecond
              obtain ⟨source, hsource, rfl⟩ := hsecond
              change Disjoint
                ({pairedLargest.1.castSucc, Fin.last (size + 1)} :
                  Finset (Fin (size + 2)))
                (source.map
                  ((Fin.succAboveEmb pairedLargest.1).trans Fin.castSuccEmb))
              exact pairedEdge_disjoint_remaining pairedLargest.1 source
          · rcases hsecond with rfl | hsecond
            · simp only [mapCycleEdges, Finset.mem_map] at hfirst
              obtain ⟨source, hsource, rfl⟩ := hfirst
              exact (pairedEdge_disjoint_remaining pairedLargest.1 source).symm
            · simp only [mapCycleEdges, Finset.mem_map] at hfirst hsecond
              obtain ⟨firstSource, hfirstSource, rfl⟩ := hfirst
              obtain ⟨secondSource, hsecondSource, rfl⟩ := hsecond
              change Disjoint
                (firstSource.map
                  ((Fin.succAboveEmb pairedLargest.1).trans Fin.castSuccEmb))
                (secondSource.map
                  ((Fin.succAboveEmb pairedLargest.1).trans Fin.castSuccEmb))
              rw [Finset.disjoint_map]
              apply ih pairedLargest.2 firstSource hfirstSource
                secondSource hsecondSource
              intro heq
              apply hne
              subst secondSource
              rfl

end FibonacciRibbonKernel
