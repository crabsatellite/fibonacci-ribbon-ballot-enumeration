import FibonacciRibbonKernel.BesselDualScales

namespace FibonacciRibbonKernel

open scoped BigOperators

noncomputable def besselPairing
    {degree : ℕ} (weight vector : Fin (degree + 1) → ℚ) : ℚ :=
  ∑ index, weight index * vector index

theorem besselPairing_M0_dual
    (degree : ℕ) (weight vector : Fin (degree + 1) → ℚ) :
    besselPairing weight (besselM0CoeffAction degree vector) =
      besselPairing (besselM0DualCoeffAction degree weight) vector := by
  have hlower :
      (∑ index : Fin (degree + 1),
        weight index *
          (if hpositive : 0 < index.val then
            (2 * index.val : ℚ) * vector ⟨index.val - 1, by omega⟩
          else 0)) =
      ∑ index : Fin (degree + 1),
        (if hbelow : index.val < degree then
          (2 * (index.val + 1) : ℚ) *
            weight ⟨index.val + 1, by omega⟩
        else 0) * vector index := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    simp
    apply Finset.sum_congr rfl
    intro index _hindex
    have hsucc : (⟨index.val + 1, by omega⟩ : Fin (degree + 1)) =
        index.succ := by
      apply Fin.ext
      rfl
    have hcast : (⟨index.val, by omega⟩ : Fin (degree + 1)) =
        index.castSucc := by
      apply Fin.ext
      rfl
    calc
      weight index.succ *
          (2 * (index.val + 1 : ℚ) *
            vector ⟨index.val, by omega⟩) =
        weight index.succ *
          (2 * (index.val + 1 : ℚ) * vector index.castSucc) := by
            rw [congrArg vector hcast]
      _ = 2 * (index.val + 1 : ℚ) *
          weight index.succ * vector index.castSucc := by ring
      _ = 2 * (index.val + 1 : ℚ) *
          weight ⟨index.val + 1, by omega⟩ * vector index.castSucc := by
            rw [congrArg weight hsucc]
  have hupper :
      (∑ index : Fin (degree + 1),
        weight index *
          (if hbelow : index.val < degree then
            (2 * (degree - index.val) : ℚ) *
              vector ⟨index.val + 1, by omega⟩
          else 0)) =
      ∑ index : Fin (degree + 1),
        (if hpositive : 0 < index.val then
          (2 * (degree - index.val + 1) : ℚ) *
            weight ⟨index.val - 1, by omega⟩
        else 0) * vector index := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
    simp
    apply Finset.sum_congr rfl
    intro index _hindex
    have hsucc : (⟨index.val + 1, by omega⟩ : Fin (degree + 1)) =
        index.succ := by
      apply Fin.ext
      rfl
    have hcast : (⟨index.val, by omega⟩ : Fin (degree + 1)) =
        index.castSucc := by
      apply Fin.ext
      rfl
    calc
      weight index.castSucc *
          (2 * (degree - index.val : ℚ) *
            vector ⟨index.val + 1, by omega⟩) =
        weight index.castSucc *
          (2 * (degree - index.val : ℚ) * vector index.succ) := by
            rw [congrArg vector hsucc]
      _ = 2 * ((degree : ℚ) - ((index.val : ℚ) + 1) + 1) *
          weight ⟨index.val, by omega⟩ * vector index.succ := by
            rw [congrArg weight hcast]
            ring
  unfold besselPairing besselM0CoeffAction besselM0DualCoeffAction
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hlower, hupper]
  simp_rw [add_mul, Finset.sum_add_distrib]
  ring_nf

theorem besselPairing_M0_signed
    (degree : ℕ) (scaleIndex : Fin (degree + 1))
    (vector : Fin (degree + 1) → ℚ) :
    besselPairing (besselSignedEigenvector degree scaleIndex)
        (besselM0CoeffAction degree vector) =
      besselScaleEigenvalue degree scaleIndex *
        besselPairing (besselSignedEigenvector degree scaleIndex) vector := by
  rw [besselPairing_M0_dual]
  have heigen := signedBesselPolynomial_dual_eigenvector
    degree scaleIndex.val (by omega)
  unfold besselSignedEigenvector at heigen ⊢
  unfold besselScaleEigenvalue
  rw [heigen]
  unfold besselPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _hindex
  ring

end FibonacciRibbonKernel
