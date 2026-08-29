import FibonacciRibbonKernel.RegevMehtaCenterLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace FibonacciRibbonKernel

open MeasureTheory Set
open scoped Classical

def standardMehtaChamber (dimension : ℕ) :
    Set (Fin dimension → ℝ) :=
  {coordinates | Antitone coordinates}

theorem continuous_standardMehtaGaussian (dimension : ℕ) :
    Continuous (standardMehtaGaussian dimension) := by
  unfold standardMehtaGaussian
  fun_prop

theorem continuous_standardMehtaVandermonde (dimension : ℕ) :
    Continuous (standardMehtaVandermonde dimension) := by
  unfold standardMehtaVandermonde
  apply continuous_finsetProd Finset.univ
  intro row hrow
  apply continuous_finsetProd (Finset.Ioi row)
  intro next hnext
  fun_prop

theorem continuous_standardMehtaIntegrand (dimension : ℕ) :
    Continuous (standardMehtaIntegrand dimension) := by
  unfold standardMehtaIntegrand
  exact (continuous_standardMehtaGaussian dimension).mul
    (continuous_standardMehtaVandermonde dimension)

theorem standardMehtaChamber_isClosed (dimension : ℕ) :
    IsClosed (standardMehtaChamber dimension) := by
  have hrepresentation : standardMehtaChamber dimension =
      ⋂ row : Fin dimension, ⋂ next : Fin dimension,
        ⋂ (_h : row ≤ next),
          {coordinates : Fin dimension → ℝ |
            coordinates next ≤ coordinates row} := by
    ext coordinates
    simp only [standardMehtaChamber, Set.mem_setOf_eq,
      Set.mem_iInter]
    exact Iff.rfl
  rw [hrepresentation]
  exact isClosed_iInter fun row =>
    isClosed_iInter fun next =>
      isClosed_iInter fun h =>
        isClosed_le (continuous_apply next) (continuous_apply row)

noncomputable def standardMehtaChamberIntegral (dimension : ℕ) : ℝ :=
  ∫ coordinates in standardMehtaChamber dimension,
    standardMehtaIntegrand dimension coordinates

def standardMehtaBlockChamber (rank : ℕ) :
    Set ((Fin rank ⊕ Fin 1) → ℝ) :=
  mehtaBlockOutput rank ⁻¹' standardMehtaChamber (rank + 1)

theorem standardMehtaBlockChamber_measurableSet (rank : ℕ) :
    MeasurableSet (standardMehtaBlockChamber rank) :=
  (measurableEmbedding_mehtaBlockOutput rank).measurable
    (standardMehtaChamber_isClosed (rank + 1)).measurableSet

noncomputable def standardMehtaBlockChamberIntegral (rank : ℕ) : ℝ :=
  ∫ coordinates in standardMehtaBlockChamber rank,
    standardMehtaIntegrand (rank + 1)
      (mehtaBlockOutput rank coordinates)

theorem standardMehtaBlockChamberIntegral_eq (rank : ℕ) :
    standardMehtaBlockChamberIntegral rank =
      standardMehtaChamberIntegral (rank + 1) := by
  unfold standardMehtaBlockChamberIntegral
  unfold standardMehtaBlockChamber standardMehtaChamberIntegral
  exact (volume_preserving_mehtaBlockOutput rank).setIntegral_preimage_emb
    (measurableEmbedding_mehtaBlockOutput rank)
    (standardMehtaIntegrand (rank + 1))
    (standardMehtaChamber (rank + 1))

end FibonacciRibbonKernel
