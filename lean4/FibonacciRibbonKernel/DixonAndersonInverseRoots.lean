import FibonacciRibbonKernel.DixonAndersonInversePolynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

namespace FibonacciRibbonKernel

open Set
open scoped Classical Interval

theorem simplexExtend_pos {dimension : ℕ}
    {coordinates : Fin dimension → ℝ}
    (hcoordinates : coordinates ∈ dirichletOpenSimplex dimension)
    (anchor : Fin (dimension + 1)) :
    0 < simplexExtend coordinates anchor := by
  cases anchor using Fin.lastCases with
  | last =>
      rw [simplexExtend_last]
      linarith [hcoordinates.2]
  | cast index =>
      rw [simplexExtend_castSucc]
      exact hcoordinates.1 index

theorem andersonPolynomialFromSimplex_eval_sign {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (coordinates : Fin dimension → ℝ)
    (hanchors : StrictAnti anchors)
    (hcoordinates : coordinates ∈ dirichletOpenSimplex dimension)
    (anchor : Fin (dimension + 1)) :
    SignType.sign
        ((andersonPolynomialFromSimplex anchors coordinates).eval
          (anchors anchor)) =
      (-1 : SignType) ^ anchor.val := by
  rw [andersonPolynomialFromSimplex_eval_anchor]
  rw [sign_mul, sign_pos (simplexExtend_pos hcoordinates anchor), one_mul]
  exact andersonDenominator_sign anchors hanchors anchor

theorem andersonPolynomialFromSimplex_adjacent_mul_neg {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (coordinates : Fin dimension → ℝ)
    (hanchors : StrictAnti anchors)
    (hcoordinates : coordinates ∈ dirichletOpenSimplex dimension)
    (index : Fin dimension) :
    (andersonPolynomialFromSimplex anchors coordinates).eval
        (anchors index.castSucc) *
      (andersonPolynomialFromSimplex anchors coordinates).eval
        (anchors index.succ) < 0 := by
  apply sign_eq_neg_one_iff.mp
  rw [sign_mul,
    andersonPolynomialFromSimplex_eval_sign anchors coordinates
      hanchors hcoordinates index.castSucc,
    andersonPolynomialFromSimplex_eval_sign anchors coordinates
      hanchors hcoordinates index.succ]
  simp only [Fin.val_castSucc, Fin.val_succ]
  rw [← pow_add]
  have hodd : Odd (index.val + (index.val + 1)) :=
    ⟨index.val, by omega⟩
  exact SignType.pow_odd (-1) hodd

theorem exists_anderson_root_in_interval {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (coordinates : Fin dimension → ℝ)
    (hanchors : StrictAnti anchors)
    (hcoordinates : coordinates ∈ dirichletOpenSimplex dimension)
    (index : Fin dimension) :
    ∃ root : ℝ,
      anchors index.succ < root ∧
        root < anchors index.castSucc ∧
        (andersonPolynomialFromSimplex anchors coordinates).eval root = 0 := by
  let polynomial := andersonPolynomialFromSimplex anchors coordinates
  let lower := anchors index.succ
  let upper := anchors index.castSucc
  have hlowerUpper : lower < upper :=
    hanchors index.castSucc_lt_succ
  have hnegative : polynomial.eval upper * polynomial.eval lower < 0 :=
    andersonPolynomialFromSimplex_adjacent_mul_neg
      anchors coordinates hanchors hcoordinates index
  have hbetween : (0 : ℝ) ∈ [[polynomial.eval lower, polynomial.eval upper]] := by
    rcases mul_neg_iff.mp hnegative with hcase | hcase
    · exact mem_uIcc.mpr (Or.inl ⟨hcase.2.le, hcase.1.le⟩)
    · exact mem_uIcc.mpr (Or.inr ⟨hcase.1.le, hcase.2.le⟩)
  obtain ⟨root, hrootInterval, hrootZero⟩ :=
    intermediate_value_uIcc polynomial.continuous.continuousOn hbetween
  rw [uIcc_of_le hlowerUpper.le] at hrootInterval
  have hproductNe : polynomial.eval upper * polynomial.eval lower ≠ 0 :=
    ne_of_lt hnegative
  have hlowerNe : polynomial.eval lower ≠ 0 :=
    right_ne_zero_of_mul hproductNe
  have hupperNe : polynomial.eval upper ≠ 0 :=
    left_ne_zero_of_mul hproductNe
  have hrootNeLower : root ≠ lower := by
    intro heq
    subst root
    exact hlowerNe hrootZero
  have hrootNeUpper : root ≠ upper := by
    intro heq
    subst root
    exact hupperNe hrootZero
  exact ⟨root,
    lt_of_le_of_ne hrootInterval.1 hrootNeLower.symm,
    lt_of_le_of_ne hrootInterval.2 hrootNeUpper,
    hrootZero⟩

noncomputable def andersonRootFromSimplex {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (coordinates : Fin dimension → ℝ)
    (hanchors : StrictAnti anchors)
    (hcoordinates : coordinates ∈ dirichletOpenSimplex dimension) :
    Fin dimension → ℝ :=
  fun index => (exists_anderson_root_in_interval
    anchors coordinates hanchors hcoordinates index).choose

theorem andersonRootFromSimplex_spec {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (coordinates : Fin dimension → ℝ)
    (hanchors : StrictAnti anchors)
    (hcoordinates : coordinates ∈ dirichletOpenSimplex dimension)
    (index : Fin dimension) :
    anchors index.succ <
        andersonRootFromSimplex anchors coordinates hanchors hcoordinates index ∧
      andersonRootFromSimplex anchors coordinates hanchors hcoordinates index <
        anchors index.castSucc ∧
      (andersonPolynomialFromSimplex anchors coordinates).eval
        (andersonRootFromSimplex anchors coordinates hanchors hcoordinates index) = 0 :=
  (exists_anderson_root_in_interval
    anchors coordinates hanchors hcoordinates index).choose_spec

theorem andersonRootFromSimplex_interlaces {dimension : ℕ}
    (anchors : Fin (dimension + 1) → ℝ)
    (coordinates : Fin dimension → ℝ)
    (hanchors : StrictAnti anchors)
    (hcoordinates : coordinates ∈ dirichletOpenSimplex dimension) :
    DixonAndersonInterlacing anchors
      (andersonRootFromSimplex anchors coordinates hanchors hcoordinates) := by
  intro index
  have hspec := andersonRootFromSimplex_spec
    anchors coordinates hanchors hcoordinates index
  exact ⟨hspec.2.1, hspec.1⟩

end FibonacciRibbonKernel
