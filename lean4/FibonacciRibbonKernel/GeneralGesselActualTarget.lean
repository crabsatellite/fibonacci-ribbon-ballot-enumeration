import FibonacciRibbonKernel.GeneralWeylGesselSeries

namespace FibonacciRibbonKernel

open PowerSeries

noncomputable def evenFormalGesselMatrixQ
    (halfDimension : ℕ) :
    Matrix (Fin halfDimension) (Fin halfDimension) ℚ⟦X⟧ :=
  fun row column =>
    symmetricLiteralBesselJ ((row.val : ℤ) - column.val) +
      symmetricLiteralBesselJ
        ((row.val + column.val + 1 : ℕ) : ℤ)

noncomputable def oddFormalGesselMatrixQ
    (halfDimension : ℕ) :
    Matrix (Fin halfDimension) (Fin halfDimension) ℚ⟦X⟧ :=
  fun row column =>
    symmetricLiteralBesselJ ((row.val : ℤ) - column.val) -
      symmetricLiteralBesselJ
        ((row.val + column.val + 2 : ℕ) : ℤ)

noncomputable def oddFormalGesselSeriesQ (halfDimension : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.exp ℚ * (oddFormalGesselMatrixQ halfDimension).det

def GeneralEvenGesselActualBridge (halfDimension : ℕ) : Prop :=
  generalUnrestrictedFactorialSeries (2 * halfDimension - 1) =
    (evenFormalGesselMatrixQ halfDimension).det

def GeneralOddGesselActualBridge (halfDimension : ℕ) : Prop :=
  generalUnrestrictedFactorialSeries (2 * halfDimension) =
    oddFormalGesselSeriesQ halfDimension

def GeneralEvenGesselAssemblyIdentity (halfDimension : ℕ) : Prop :=
  generalClosedEvenAssembly halfDimension =
    (halfDimension.factorial : ℚ⟦X⟧) *
      (X ^ staircaseWeight (2 * halfDimension - 1) *
        (evenFormalGesselMatrixQ halfDimension).det)

def GeneralOddGesselAssemblyIdentity (halfDimension : ℕ) : Prop :=
  generalClosedOddAssembly halfDimension =
    (halfDimension.factorial : ℚ⟦X⟧) *
      (X ^ staircaseWeight (2 * halfDimension) *
        oddFormalGesselSeriesQ halfDimension)

theorem factorial_powerSeries_ne_zero (value : ℕ) :
    (value.factorial : ℚ⟦X⟧) ≠ 0 := by
  intro hzero
  have hc := congrArg (PowerSeries.coeff 0) hzero
  norm_num at hc
  exact Nat.factorial_ne_zero value hc

theorem generalEvenGesselActualBridge_iff_assembly
    (halfDimension : ℕ) (hhalf : 1 ≤ halfDimension) :
    GeneralEvenGesselActualBridge halfDimension ↔
      GeneralEvenGesselAssemblyIdentity halfDimension := by
  constructor
  · intro hactual
    unfold GeneralEvenGesselActualBridge at hactual
    unfold GeneralEvenGesselAssemblyIdentity
    rw [← generalUnrestrictedFactorialSeries_even_closed halfDimension hhalf,
      hactual]
  · intro hassembly
    unfold GeneralEvenGesselAssemblyIdentity at hassembly
    have hclosed := generalUnrestrictedFactorialSeries_even_closed
      halfDimension hhalf
    rw [hassembly] at hclosed
    have hcancel :
        X ^ staircaseWeight (2 * halfDimension - 1) *
            generalUnrestrictedFactorialSeries (2 * halfDimension - 1) =
          X ^ staircaseWeight (2 * halfDimension - 1) *
            (evenFormalGesselMatrixQ halfDimension).det := by
      exact mul_left_cancel₀ (factorial_powerSeries_ne_zero halfDimension)
        hclosed
    unfold GeneralEvenGesselActualBridge
    exact PowerSeries.X_pow_mul_cancel hcancel

theorem generalOddGesselActualBridge_iff_assembly
    (halfDimension : ℕ) :
    GeneralOddGesselActualBridge halfDimension ↔
      GeneralOddGesselAssemblyIdentity halfDimension := by
  constructor
  · intro hactual
    unfold GeneralOddGesselActualBridge at hactual
    unfold GeneralOddGesselAssemblyIdentity
    rw [← generalUnrestrictedFactorialSeries_odd_closed halfDimension,
      hactual]
  · intro hassembly
    unfold GeneralOddGesselAssemblyIdentity at hassembly
    have hclosed := generalUnrestrictedFactorialSeries_odd_closed halfDimension
    rw [hassembly] at hclosed
    have hcancel :
        X ^ staircaseWeight (2 * halfDimension) *
            generalUnrestrictedFactorialSeries (2 * halfDimension) =
          X ^ staircaseWeight (2 * halfDimension) *
            oddFormalGesselSeriesQ halfDimension := by
      exact mul_left_cancel₀ (factorial_powerSeries_ne_zero halfDimension)
        hclosed
    unfold GeneralOddGesselActualBridge
    exact PowerSeries.X_pow_mul_cancel hcancel

theorem evenFormalGesselMatrixR_eq_map
    (halfDimension : ℕ) :
    evenFormalGesselMatrixR halfDimension =
      fun row column => PowerSeries.map (Rat.castHom ℝ)
        (evenFormalGesselMatrixQ halfDimension row column) := by
  apply Matrix.ext
  intro row column
  unfold evenFormalGesselMatrixR evenFormalGesselMatrixQ
    symmetricLiteralBesselJR
  rw [map_add]

theorem oddFormalGesselMatrixR_eq_map
    (halfDimension : ℕ) :
    oddFormalGesselMatrixR halfDimension =
      fun row column => PowerSeries.map (Rat.castHom ℝ)
        (oddFormalGesselMatrixQ halfDimension row column) := by
  apply Matrix.ext
  intro row column
  unfold oddFormalGesselMatrixR oddFormalGesselMatrixQ
    symmetricLiteralBesselJR
  rw [map_sub]

theorem evenFormalGesselMatrixQ_two_det :
    (evenFormalGesselMatrixQ 2).det = gesselHeightFourSeries := by
  rw [Matrix.det_fin_two]
  unfold evenFormalGesselMatrixQ symmetricLiteralBesselJ
  norm_num
  unfold gesselHeightFourSeries pairQ1 pairQ2 pairQ3
  ring

theorem evenFormalGesselMatrixQ_three_eq_heightSix :
    evenFormalGesselMatrixQ 3 = gesselHeightSixMatrix := by
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    norm_num [evenFormalGesselMatrixQ, symmetricLiteralBesselJ,
      gesselHeightSixMatrix]

theorem oddFormalGesselMatrixQ_two_det :
    (oddFormalGesselMatrixQ 2).det =
      (literalBesselJ 0 - literalBesselJ 2) *
          (literalBesselJ 0 - literalBesselJ 4) -
        (literalBesselJ 1 - literalBesselJ 3) ^ 2 := by
  rw [Matrix.det_fin_two]
  unfold oddFormalGesselMatrixQ symmetricLiteralBesselJ
  norm_num
  ring

theorem generalEvenGesselActualBridge_two :
    GeneralEvenGesselActualBridge 2 := by
  unfold GeneralEvenGesselActualBridge
  rw [show generalUnrestrictedFactorialSeries (2 * 2 - 1) =
      factorialSeries (fun size => (heightFourTableauCount size : ℚ)) by
    ext power
    rw [generalUnrestrictedFactorialSeries_coeff, factorialSeries_coeff]
    rfl]
  rw [factorialSeries_heightFourTableauCount_eq_gessel,
    evenFormalGesselMatrixQ_two_det]

theorem generalEvenGesselActualBridge_three :
    GeneralEvenGesselActualBridge 3 := by
  unfold GeneralEvenGesselActualBridge
  rw [show generalUnrestrictedFactorialSeries (2 * 3 - 1) =
      factorialSeries (fun size => (heightSixTableauCount size : ℚ)) by
    ext power
    rw [generalUnrestrictedFactorialSeries_coeff, factorialSeries_coeff]
    rfl]
  rw [factorialSeries_heightSixTableauCount_eq_gessel,
    evenFormalGesselMatrixQ_three_eq_heightSix,
    ← gesselHeightSixSeries_eq_det]

theorem generalOddGesselActualBridge_two :
    GeneralOddGesselActualBridge 2 := by
  unfold GeneralOddGesselActualBridge oddFormalGesselSeriesQ
  rw [show generalUnrestrictedFactorialSeries (2 * 2) =
      factorialSeries (fun size => (heightFiveTableauCount size : ℚ)) by
    ext power
    rw [generalUnrestrictedFactorialSeries_coeff, factorialSeries_coeff]
    rfl]
  rw [factorialSeries_heightFiveTableauCount_eq_gessel,
    oddFormalGesselMatrixQ_two_det]
  rfl

end FibonacciRibbonKernel
