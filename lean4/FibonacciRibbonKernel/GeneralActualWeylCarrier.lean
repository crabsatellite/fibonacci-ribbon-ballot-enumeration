import FibonacciRibbonKernel.GordonOddDeterminantFactorization
import FibonacciRibbonKernel.WeylCountBridge

namespace FibonacciRibbonKernel

open PowerSeries

theorem mapped_generalEvenUnrestricted_eq_weyl
    (halfDimension : ℕ) (hhalf : 1 ≤ halfDimension) :
    PowerSeries.map (Rat.castHom ℝ)
        (generalUnrestrictedFactorialSeries (2 * halfDimension - 1)) =
      evenWeylSeriesGeneralR halfDimension := by
  rw [generalEvenGesselActualBridge_all halfDimension hhalf]
  rw [(PowerSeries.map (Rat.castHom ℝ)).map_det]
  have hmatrix :
      (PowerSeries.map (Rat.castHom ℝ)).mapMatrix
          (evenFormalGesselMatrixQ halfDimension) =
        evenFormalGesselMatrixR halfDimension := by
    apply Matrix.ext
    intro row column
    have hentry := congrArg (fun matrix => matrix row column)
      (evenFormalGesselMatrixR_eq_map halfDimension)
    exact hentry.symm
  rw [hmatrix]
  exact evenFormalGesselDet_eq_weylSeries hhalf

theorem mapped_generalOddUnrestricted_eq_weyl
    (halfDimension : ℕ) (hhalf : 1 ≤ halfDimension) :
    PowerSeries.map (Rat.castHom ℝ)
        (generalUnrestrictedFactorialSeries (2 * halfDimension)) =
      oddWeylSeriesGeneralR halfDimension := by
  rw [generalOddGesselActualBridge_all]
  unfold oddFormalGesselSeriesQ
  rw [map_mul, PowerSeries.map_exp]
  rw [(PowerSeries.map (Rat.castHom ℝ)).map_det]
  have hmatrix :
      (PowerSeries.map (Rat.castHom ℝ)).mapMatrix
          (oddFormalGesselMatrixQ halfDimension) =
        oddFormalGesselMatrixR halfDimension := by
    apply Matrix.ext
    intro row column
    have hentry := congrArg (fun matrix => matrix row column)
      (oddFormalGesselMatrixR_eq_map halfDimension)
    exact hentry.symm
  rw [hmatrix]
  change oddFormalGesselSeriesR halfDimension = oddWeylSeriesGeneralR halfDimension
  exact oddFormalGesselSeries_eq_weylSeries hhalf

theorem generalEvenUnrestrictedCount_eq_normalizedWeylMoment
    (halfDimension : ℕ) (hhalf : 1 ≤ halfDimension) (power : ℕ) :
    (unrestrictedCount (2 * halfDimension - 1) power : ℝ) =
      evenWeylNormalization halfDimension *
        evenWeylGeometricMoment halfDimension power := by
  have hseries := mapped_generalEvenUnrestricted_eq_weyl halfDimension hhalf
  have hcoeff := congrArg (PowerSeries.coeff power) hseries
  unfold evenWeylSeriesGeneralR evenWeylMomentSeriesGeneralR at hcoeff
  rw [PowerSeries.coeff_map, generalUnrestrictedFactorialSeries_coeff,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_mk] at hcoeff
  have hcast :
      (Rat.castHom ℝ)
          ((unrestrictedCount (2 * halfDimension - 1) power : ℚ) /
            (power.factorial : ℚ)) =
        (unrestrictedCount (2 * halfDimension - 1) power : ℝ) /
          (power.factorial : ℝ) := by
    rw [map_div₀]
    norm_num
  rw [hcast] at hcoeff
  have hfactorial : (power.factorial : ℝ) ≠ 0 := by positivity
  field_simp [hfactorial] at hcoeff ⊢
  nlinarith

theorem generalOddUnrestrictedCount_eq_normalizedWeylMoment
    (halfDimension : ℕ) (hhalf : 1 ≤ halfDimension) (power : ℕ) :
    (unrestrictedCount (2 * halfDimension) power : ℝ) =
      oddWeylNormalization halfDimension *
        oddWeylGeometricMoment halfDimension power := by
  have hseries := mapped_generalOddUnrestricted_eq_weyl halfDimension hhalf
  have hcoeff := congrArg (PowerSeries.coeff power) hseries
  unfold oddWeylSeriesGeneralR oddWeylMomentSeriesR at hcoeff
  rw [PowerSeries.coeff_map, generalUnrestrictedFactorialSeries_coeff,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_mk] at hcoeff
  have hcast :
      (Rat.castHom ℝ)
          ((unrestrictedCount (2 * halfDimension) power : ℚ) /
            (power.factorial : ℚ)) =
        (unrestrictedCount (2 * halfDimension) power : ℝ) /
          (power.factorial : ℝ) := by
    rw [map_div₀]
    norm_num
  rw [hcast] at hcoeff
  have hfactorial : (power.factorial : ℝ) ≠ 0 := by positivity
  field_simp [hfactorial] at hcoeff ⊢
  nlinarith

theorem generalEvenRibbonCount_eq_normalizedWeylMoment
    (halfDimension : ℕ) (hhalf : 1 ≤ halfDimension) (power : ℕ) :
    (ribbonCount (2 * halfDimension - 1) power : ℝ) =
      evenWeylNormalization halfDimension *
        evenWeylFibonacciMoment halfDimension power := by
  symm
  apply evenWeylMoment_count_transfer halfDimension hhalf
    (evenWeylNormalization halfDimension)
  intro degree
  exact (generalEvenUnrestrictedCount_eq_normalizedWeylMoment
    halfDimension hhalf degree).symm

theorem generalOddRibbonCount_eq_normalizedWeylMoment
    (halfDimension : ℕ) (hhalf : 1 ≤ halfDimension) (power : ℕ) :
    (ribbonCount (2 * halfDimension) power : ℝ) =
      oddWeylNormalization halfDimension *
        oddWeylFibonacciMoment halfDimension power := by
  symm
  apply oddWeylMoment_count_transfer halfDimension hhalf
    (oddWeylNormalization halfDimension)
  intro degree
  exact (generalOddUnrestrictedCount_eq_normalizedWeylMoment
    halfDimension hhalf degree).symm

end FibonacciRibbonKernel
