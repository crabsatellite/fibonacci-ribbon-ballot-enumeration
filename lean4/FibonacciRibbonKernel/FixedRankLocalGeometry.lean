import FibonacciRibbonKernel.DefinitionFormulas

namespace FibonacciRibbonKernel

/-- The smaller root paired with `fixedRankGrowth`. -/
noncomputable def fixedRankPreimage (alphabetSize : ℕ) : ℝ :=
  ((alphabetSize : ℝ) -
    Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4)) / 2

/-- The real form of the manuscript substitution `w(z)=z/(1+z²)`. -/
noncomputable def ribbonSubstitutionReal (z : ℝ) : ℝ :=
  z / (1 + z ^ 2)

/-- The real prefactor in `B(z)=(1+z²)⁻¹U(w(z))`. -/
noncomputable def ribbonPrefactorReal (z : ℝ) : ℝ :=
  1 / (1 + z ^ 2)

/-- The algebraic derivative of the real ribbon substitution. -/
noncomputable def ribbonSubstitutionDerivativeReal (z : ℝ) : ℝ :=
  (1 - z ^ 2) / (1 + z ^ 2) ^ 2

private theorem discriminant_pos
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    0 < (alphabetSize : ℝ) ^ 2 - 4 := by
  have hn : (3 : ℝ) ≤ alphabetSize := by exact_mod_cast hsize
  nlinarith

theorem fixedRank_sqrt_sq
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    (Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4)) ^ 2 =
      (alphabetSize : ℝ) ^ 2 - 4 := by
  exact Real.sq_sqrt (le_of_lt (discriminant_pos alphabetSize hsize))

theorem fixedRank_sqrt_pos
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    0 < Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4) :=
  Real.sqrt_pos.2 (discriminant_pos alphabetSize hsize)

theorem fixedRank_sqrt_lt_size
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4) < alphabetSize := by
  have hn : (0 : ℝ) < alphabetSize := by positivity
  have hsnonneg :
      0 ≤ Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4) := Real.sqrt_nonneg _
  have hsq := fixedRank_sqrt_sq alphabetSize hsize
  nlinarith

theorem fixedRankGrowth_add_preimage
    (alphabetSize : ℕ) :
    fixedRankGrowth alphabetSize + fixedRankPreimage alphabetSize =
      alphabetSize := by
  simp only [fixedRankGrowth, fixedRankPreimage]
  ring

theorem fixedRankGrowth_mul_preimage
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    fixedRankGrowth alphabetSize * fixedRankPreimage alphabetSize = 1 := by
  rw [fixedRankGrowth, fixedRankPreimage]
  have hsq := fixedRank_sqrt_sq alphabetSize hsize
  nlinarith

theorem fixedRankGrowth_pos
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    0 < fixedRankGrowth alphabetSize := by
  rw [fixedRankGrowth]
  have hn : (0 : ℝ) < alphabetSize := by positivity
  have hs := Real.sqrt_nonneg ((alphabetSize : ℝ) ^ 2 - 4)
  positivity

theorem fixedRankPreimage_pos
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    0 < fixedRankPreimage alphabetSize := by
  rw [fixedRankPreimage]
  have hlt := fixedRank_sqrt_lt_size alphabetSize hsize
  positivity

theorem fixedRankPreimage_eq_inv_growth
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    fixedRankPreimage alphabetSize =
      (fixedRankGrowth alphabetSize)⁻¹ := by
  have hmul := fixedRankGrowth_mul_preimage alphabetSize hsize
  have hne := (fixedRankGrowth_pos alphabetSize hsize).ne'
  calc
    fixedRankPreimage alphabetSize =
        (fixedRankGrowth alphabetSize * fixedRankPreimage alphabetSize) *
          (fixedRankGrowth alphabetSize)⁻¹ := by field_simp
    _ = (fixedRankGrowth alphabetSize)⁻¹ := by rw [hmul]; simp

theorem fixedRankPreimage_sq_add_one_pos
    (alphabetSize : ℕ) :
    0 < 1 + fixedRankPreimage alphabetSize ^ 2 := by positivity

/-- The positive singularity `1/n` has the exact simple preimage `ρ_n`. -/
theorem ribbonSubstitutionReal_fixedRankPreimage
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    ribbonSubstitutionReal (fixedRankPreimage alphabetSize) =
      1 / alphabetSize := by
  have hsum := fixedRankGrowth_add_preimage alphabetSize
  have hmul := fixedRankGrowth_mul_preimage alphabetSize hsize
  have hrho := (fixedRankPreimage_pos alphabetSize hsize).ne'
  have hn : (alphabetSize : ℝ) ≠ 0 := by positivity
  have hdenom := (fixedRankPreimage_sq_add_one_pos alphabetSize).ne'
  have hNrho :
      (alphabetSize : ℝ) * fixedRankPreimage alphabetSize =
        1 + fixedRankPreimage alphabetSize ^ 2 := by
    calc
      (alphabetSize : ℝ) * fixedRankPreimage alphabetSize =
          (fixedRankGrowth alphabetSize + fixedRankPreimage alphabetSize) *
            fixedRankPreimage alphabetSize := by rw [hsum]
      _ = 1 + fixedRankPreimage alphabetSize ^ 2 := by
        rw [add_mul, hmul]
        ring
  rw [ribbonSubstitutionReal]
  field_simp
  simpa [mul_comm] using hNrho

/-- The prefactor at the positive preimage is `α_n/n`. -/
theorem ribbonPrefactorReal_fixedRankPreimage
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    ribbonPrefactorReal (fixedRankPreimage alphabetSize) =
      fixedRankGrowth alphabetSize / alphabetSize := by
  have hsum := fixedRankGrowth_add_preimage alphabetSize
  have hmul := fixedRankGrowth_mul_preimage alphabetSize hsize
  have hn : (alphabetSize : ℝ) ≠ 0 := by positivity
  have hdenom := (fixedRankPreimage_sq_add_one_pos alphabetSize).ne'
  have hdenomAlpha :
      (1 + fixedRankPreimage alphabetSize ^ 2) *
          fixedRankGrowth alphabetSize = alphabetSize := by
    calc
      (1 + fixedRankPreimage alphabetSize ^ 2) *
          fixedRankGrowth alphabetSize =
        fixedRankGrowth alphabetSize +
          fixedRankPreimage alphabetSize *
            (fixedRankGrowth alphabetSize *
              fixedRankPreimage alphabetSize) := by ring
      _ = fixedRankGrowth alphabetSize +
          fixedRankPreimage alphabetSize := by rw [hmul]; ring
      _ = alphabetSize := hsum
  rw [ribbonPrefactorReal]
  field_simp
  exact hdenomAlpha.symm

/-- The normalized derivative factor at the positive preimage is exactly
`sqrt(n²-4)/n`, the local scale used in the manuscript constant. -/
theorem ribbonSubstitutionDerivativeReal_fixedRankPreimage
    (alphabetSize : ℕ) (hsize : 3 ≤ alphabetSize) :
    fixedRankPreimage alphabetSize *
          ribbonSubstitutionDerivativeReal (fixedRankPreimage alphabetSize) /
        (1 / alphabetSize) =
      Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4) / alphabetSize := by
  let alpha := fixedRankGrowth alphabetSize
  let rho := fixedRankPreimage alphabetSize
  let root := Real.sqrt ((alphabetSize : ℝ) ^ 2 - 4)
  have hsum : alpha + rho = (alphabetSize : ℝ) :=
    fixedRankGrowth_add_preimage alphabetSize
  have hmul : alpha * rho = 1 :=
    fixedRankGrowth_mul_preimage alphabetSize hsize
  have hdiff : alpha - rho = root := by
    simp only [alpha, rho, root, fixedRankGrowth, fixedRankPreimage]
    ring
  have hrho : rho ≠ 0 := (fixedRankPreimage_pos alphabetSize hsize).ne'
  have hn : (alphabetSize : ℝ) ≠ 0 := by positivity
  have hdenom : 1 + rho ^ 2 ≠ 0 := by positivity
  have hNrho : (alphabetSize : ℝ) * rho = 1 + rho ^ 2 := by
    calc
      (alphabetSize : ℝ) * rho = (alpha + rho) * rho := by rw [hsum]
      _ = 1 + rho ^ 2 := by rw [add_mul, hmul]; ring
  have hOneMinus : 1 - rho ^ 2 = rho * root := by
    calc
      1 - rho ^ 2 = alpha * rho - rho ^ 2 := by rw [hmul]
      _ = rho * (alpha - rho) := by ring
      _ = rho * root := by rw [hdiff]
  change rho * ((1 - rho ^ 2) / (1 + rho ^ 2) ^ 2) /
      (1 / (alphabetSize : ℝ)) = root / alphabetSize
  rw [hOneMinus, ← hNrho]
  field_simp

end FibonacciRibbonKernel
