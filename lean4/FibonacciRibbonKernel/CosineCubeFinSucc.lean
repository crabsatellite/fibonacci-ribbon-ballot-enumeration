import FibonacciRibbonKernel.CosineCubeIntegralCarrier

namespace FibonacciRibbonKernel

open scoped BigOperators

def cosinePlusCons
    (plusPower minusPower : ℕ) (angle : ℝ)
    (tail : Fin (plusPower + minusPower) → ℝ) :
    Fin ((plusPower + 1) + minusPower) → ℝ :=
  fun coordinate => (Fin.cons angle tail :
      Fin ((plusPower + minusPower) + 1) → ℝ)
    (Fin.cast (by omega : (plusPower + 1) + minusPower =
      (plusPower + minusPower) + 1) coordinate)

@[simp] theorem cosinePlusCons_zero
    (plusPower minusPower : ℕ) (angle : ℝ)
    (tail : Fin (plusPower + minusPower) → ℝ) :
    cosinePlusCons plusPower minusPower angle tail 0 = angle := by
  simp [cosinePlusCons]

@[simp] theorem cosinePlusCons_succ
    (plusPower minusPower : ℕ) (angle : ℝ)
    (tail : Fin (plusPower + minusPower) → ℝ)
    (coordinate : Fin (plusPower + minusPower)) :
    cosinePlusCons plusPower minusPower angle tail
        ⟨coordinate.val + 1, by omega⟩ = tail coordinate := by
  unfold cosinePlusCons
  have hindex : Fin.cast (by omega :
      (plusPower + 1) + minusPower = (plusPower + minusPower) + 1)
        ⟨coordinate.val + 1, by omega⟩ = coordinate.succ := by
    apply Fin.ext
    rfl
  rw [hindex, Fin.cons_succ]

def cosineMinusCons
    (minusPower : ℕ) (angle : ℝ)
    (tail : Fin (0 + minusPower) → ℝ) :
    Fin (0 + (minusPower + 1)) → ℝ :=
  fun coordinate => (Fin.cons angle tail : Fin ((0 + minusPower) + 1) → ℝ)
    (Fin.cast (by omega : 0 + (minusPower + 1) =
      (0 + minusPower) + 1) coordinate)

@[simp] theorem cosineMinusCons_zero
    (minusPower : ℕ) (angle : ℝ) (tail : Fin (0 + minusPower) → ℝ) :
    cosineMinusCons minusPower angle tail 0 = angle := by
  simp [cosineMinusCons]

@[simp] theorem cosineMinusCons_succ
    (minusPower : ℕ) (angle : ℝ) (tail : Fin (0 + minusPower) → ℝ)
    (coordinate : Fin (0 + minusPower)) :
    cosineMinusCons minusPower angle tail
        ⟨coordinate.val + 1, by omega⟩ = tail coordinate := by
  unfold cosineMinusCons
  have hindex : Fin.cast (by omega :
      0 + (minusPower + 1) = (0 + minusPower) + 1)
        ⟨coordinate.val + 1, by omega⟩ = coordinate.succ := by
    apply Fin.ext
    rfl
  rw [hindex, Fin.cons_succ]

theorem cosineCubeScale_plusCons
    (plusPower minusPower : ℕ) (angle : ℝ)
    (tail : Fin (plusPower + minusPower) → ℝ) :
    cosineCubeScale (cosinePlusCons plusPower minusPower angle tail) =
      2 * Real.cos angle + cosineCubeScale tail := by
  unfold cosineCubeScale
  have hsum :
      (∑ coordinate : Fin ((plusPower + 1) + minusPower),
        Real.cos (cosinePlusCons plusPower minusPower angle tail coordinate)) =
      ∑ coordinate : Fin ((plusPower + minusPower) + 1),
        Real.cos ((Fin.cons angle tail :
          Fin ((plusPower + minusPower) + 1) → ℝ) coordinate) := by
    apply Fintype.sum_equiv (finCongr (by omega :
      (plusPower + 1) + minusPower = (plusPower + minusPower) + 1))
    intro coordinate
    simp [cosinePlusCons]
  rw [hsum, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

theorem cosineCubeScale_minusCons
    (minusPower : ℕ) (angle : ℝ) (tail : Fin (0 + minusPower) → ℝ) :
    cosineCubeScale (cosineMinusCons minusPower angle tail) =
      2 * Real.cos angle + cosineCubeScale tail := by
  unfold cosineCubeScale
  have hsum :
      (∑ coordinate : Fin (0 + (minusPower + 1)),
        Real.cos (cosineMinusCons minusPower angle tail coordinate)) =
      ∑ coordinate : Fin ((0 + minusPower) + 1),
        Real.cos ((Fin.cons angle tail :
          Fin ((0 + minusPower) + 1) → ℝ) coordinate) := by
    apply Fintype.sum_equiv (finCongr (by omega :
      0 + (minusPower + 1) = (0 + minusPower) + 1))
    intro coordinate
    simp [cosineMinusCons]
  rw [hsum, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

theorem cosineCubeScale_finCons
    {dimension : ℕ} (angle : ℝ) (tail : Fin dimension → ℝ) :
    cosineCubeScale (Fin.cons angle tail) =
      2 * Real.cos angle + cosineCubeScale tail := by
  unfold cosineCubeScale
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

theorem cosineCoordinateIsPlus_zero_succ
    (plusPower minusPower : ℕ) :
    cosineCoordinateIsPlus (plusPower + 1) minusPower
      (0 : Fin ((plusPower + 1) + minusPower)) = true := by
  unfold cosineCoordinateIsPlus
  simp

theorem cosineCoordinateIsPlus_succ_succ
    (plusPower minusPower : ℕ)
    (coordinate : Fin (plusPower + minusPower)) :
    cosineCoordinateIsPlus (plusPower + 1) minusPower
        ⟨coordinate.val + 1, by omega⟩ =
      cosineCoordinateIsPlus plusPower minusPower coordinate := by
  unfold cosineCoordinateIsPlus
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

theorem cosineCubeWeight_plus_finCons
    (plusPower minusPower : ℕ) (angle : ℝ)
    (tail : Fin (plusPower + minusPower) → ℝ) :
    cosineCubeWeight (plusPower + 1) minusPower
        (cosinePlusCons plusPower minusPower angle tail) =
      cosineFactorWeight true angle *
        cosineCubeWeight plusPower minusPower tail := by
  unfold cosineCubeWeight
  have hprod :
      (∏ coordinate : Fin ((plusPower + 1) + minusPower),
        cosineFactorWeight
          (cosineCoordinateIsPlus (plusPower + 1) minusPower coordinate)
          (cosinePlusCons plusPower minusPower angle tail coordinate)) =
      ∏ coordinate : Fin ((plusPower + minusPower) + 1),
        cosineFactorWeight
          (cosineCoordinateIsPlus (plusPower + 1) minusPower
            ⟨coordinate.val, by omega⟩)
          ((Fin.cons angle tail :
            Fin ((plusPower + minusPower) + 1) → ℝ) coordinate) := by
    let equivalence := finCongr (by omega :
      (plusPower + 1) + minusPower = (plusPower + minusPower) + 1)
    apply Fintype.prod_equiv equivalence
    intro coordinate
    have hback :
        (⟨(equivalence coordinate).val, by omega⟩ :
          Fin ((plusPower + 1) + minusPower)) = coordinate := by
      apply Fin.ext
      rfl
    rw [hback]
    apply congrArg
      (cosineFactorWeight
        (cosineCoordinateIsPlus (plusPower + 1) minusPower coordinate))
    unfold cosinePlusCons
    congr 1
  rw [hprod, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  simp [cosineCoordinateIsPlus]

theorem cosineCoordinateIsPlus_zero_zero
    (minusPower : ℕ) :
    cosineCoordinateIsPlus 0 (minusPower + 1)
      (0 : Fin (0 + (minusPower + 1))) = false := by
  unfold cosineCoordinateIsPlus
  simp

theorem cosineCoordinateIsPlus_succ_zero
    (minusPower : ℕ) (coordinate : Fin (0 + minusPower)) :
    cosineCoordinateIsPlus 0 (minusPower + 1)
        ⟨coordinate.val + 1, by omega⟩ =
      cosineCoordinateIsPlus 0 minusPower coordinate := by
  unfold cosineCoordinateIsPlus
  simp

theorem cosineCubeWeight_minus_finCons
    (minusPower : ℕ) (angle : ℝ) (tail : Fin (0 + minusPower) → ℝ) :
    cosineCubeWeight 0 (minusPower + 1)
        (cosineMinusCons minusPower angle tail) =
      cosineFactorWeight false angle *
        cosineCubeWeight 0 minusPower tail := by
  unfold cosineCubeWeight
  have hprod :
      (∏ coordinate : Fin (0 + (minusPower + 1)),
        cosineFactorWeight
          (cosineCoordinateIsPlus 0 (minusPower + 1) coordinate)
          (cosineMinusCons minusPower angle tail coordinate)) =
      ∏ coordinate : Fin ((0 + minusPower) + 1),
        cosineFactorWeight
          (cosineCoordinateIsPlus 0 (minusPower + 1)
            ⟨coordinate.val, by omega⟩)
          ((Fin.cons angle tail : Fin ((0 + minusPower) + 1) → ℝ) coordinate) := by
    let equivalence := finCongr (by omega :
      0 + (minusPower + 1) = (0 + minusPower) + 1)
    apply Fintype.prod_equiv equivalence
    intro coordinate
    have hback :
        (⟨(equivalence coordinate).val, by omega⟩ :
          Fin (0 + (minusPower + 1))) = coordinate := by
      apply Fin.ext
      rfl
    rw [hback]
    apply congrArg
      (cosineFactorWeight
        (cosineCoordinateIsPlus 0 (minusPower + 1) coordinate))
    unfold cosineMinusCons
    congr 1
  rw [hprod, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  simp [cosineCoordinateIsPlus]

theorem cosineCubeRawIntegrand_plus_finCons
    (plusPower minusPower power : ℕ) (angle : ℝ)
    (tail : Fin (plusPower + minusPower) → ℝ) :
    cosineCubeRawIntegrand (plusPower + 1) minusPower power
        (cosinePlusCons plusPower minusPower angle tail) =
      (2 * Real.cos angle + cosineCubeScale tail) ^ power *
        cosineFactorWeight true angle *
          cosineCubeWeight plusPower minusPower tail := by
  unfold cosineCubeRawIntegrand
  rw [cosineCubeScale_plusCons, cosineCubeWeight_plus_finCons]
  ring

theorem cosineCubeRawIntegrand_minus_finCons
    (minusPower power : ℕ) (angle : ℝ)
    (tail : Fin (0 + minusPower) → ℝ) :
    cosineCubeRawIntegrand 0 (minusPower + 1) power
        (cosineMinusCons minusPower angle tail) =
      (2 * Real.cos angle + cosineCubeScale tail) ^ power *
        cosineFactorWeight false angle *
          cosineCubeWeight 0 minusPower tail := by
  unfold cosineCubeRawIntegrand
  rw [cosineCubeScale_minusCons, cosineCubeWeight_minus_finCons]
  ring

end FibonacciRibbonKernel
