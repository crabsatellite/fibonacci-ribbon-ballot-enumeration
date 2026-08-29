import FibonacciRibbonKernel.CosineCubeFinSucc

namespace FibonacciRibbonKernel

open MeasureTheory

noncomputable def cosinePlusReindexEquiv (plusPower minusPower : ℕ) :
    (Fin ((plusPower + 1) + minusPower) → ℝ) ≃ᵐ
      (Fin ((plusPower + minusPower) + 1) → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin ((plusPower + minusPower) + 1) => ℝ)
    (finCongr (by omega :
      (plusPower + 1) + minusPower = (plusPower + minusPower) + 1))

noncomputable def cosineMinusReindexEquiv (minusPower : ℕ) :
    (Fin (0 + (minusPower + 1)) → ℝ) ≃ᵐ
      (Fin ((0 + minusPower) + 1) → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin ((0 + minusPower) + 1) => ℝ)
    (finCongr (by omega :
      0 + (minusPower + 1) = (0 + minusPower) + 1))

theorem cosinePlusReindexEquiv_symm_finCons
    (plusPower minusPower : ℕ) (angle : ℝ)
    (tail : Fin (plusPower + minusPower) → ℝ) :
    (cosinePlusReindexEquiv plusPower minusPower).symm
        (Fin.cons angle tail) =
      cosinePlusCons plusPower minusPower angle tail := by
  funext coordinate
  unfold cosinePlusReindexEquiv
  change (Equiv.piCongrLeft
      (fun _ : Fin ((plusPower + minusPower) + 1) => ℝ)
      (finCongr (by omega :
        (plusPower + 1) + minusPower = (plusPower + minusPower) + 1))).symm
        (Fin.cons angle tail) coordinate = _
  rw [Equiv.piCongrLeft_symm_apply]
  rfl

theorem cosineMinusReindexEquiv_symm_finCons
    (minusPower : ℕ) (angle : ℝ) (tail : Fin (0 + minusPower) → ℝ) :
    (cosineMinusReindexEquiv minusPower).symm (Fin.cons angle tail) =
      cosineMinusCons minusPower angle tail := by
  funext coordinate
  unfold cosineMinusReindexEquiv
  change (Equiv.piCongrLeft
      (fun _ : Fin ((0 + minusPower) + 1) => ℝ)
      (finCongr (by omega :
        0 + (minusPower + 1) = (0 + minusPower) + 1))).symm
        (Fin.cons angle tail) coordinate = _
  rw [Equiv.piCongrLeft_symm_apply]
  rfl

theorem measurePreserving_cosinePlusReindexEquiv
    (plusPower minusPower : ℕ) :
    MeasurePreserving (cosinePlusReindexEquiv plusPower minusPower)
      (cosineCubeProductMeasure ((plusPower + 1) + minusPower))
      (cosineCubeProductMeasure ((plusPower + minusPower) + 1)) := by
  unfold cosinePlusReindexEquiv cosineCubeProductMeasure
  exact measurePreserving_piCongrLeft
    (fun _ : Fin ((plusPower + minusPower) + 1) => cosineIntervalMeasure)
    (finCongr (by omega :
      (plusPower + 1) + minusPower = (plusPower + minusPower) + 1))

theorem measurePreserving_cosineMinusReindexEquiv (minusPower : ℕ) :
    MeasurePreserving (cosineMinusReindexEquiv minusPower)
      (cosineCubeProductMeasure (0 + (minusPower + 1)))
      (cosineCubeProductMeasure ((0 + minusPower) + 1)) := by
  unfold cosineMinusReindexEquiv cosineCubeProductMeasure
  exact measurePreserving_piCongrLeft
    (fun _ : Fin ((0 + minusPower) + 1) => cosineIntervalMeasure)
    (finCongr (by omega :
      0 + (minusPower + 1) = (0 + minusPower) + 1))

end FibonacciRibbonKernel
