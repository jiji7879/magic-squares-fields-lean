import MagicSquares.CenterOne.SquareCount
import MagicSquares.Weil.CoarseQuadratic

namespace MagicSquares.Square3

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- An unconditional version of the Section 7 count obtained from the
proved Stepánov theorem. The larger constant is intentional: this theorem
makes no use of the sharp Weil theorem. -/
theorem centerOne_square_count_coarse
    (hodd : ringChar F ≠ 2) (hq : 12800 ≤ Fintype.card F)
    (b : F) (hb : CenterOneGoodB b) :
    (Fintype.card F : ℝ) - 28 - 11520 * Real.sqrt (Fintype.card F : ℝ) ≤
      256 * ((centerOnePowerParameters 2 b).card : ℝ) := by
  classical
  let coeff := centerOneNoncenterCoeff b
  have hinj : Function.Injective coeff := hb.comp Fin.succAbove_right_injective
  have hnz (i : Fin 8) : coeff i ≠ 0 :=
    centerOneCoeff_ne_zero_of_good hb (Fin.succAbove_ne _ _)
  have hlarge (s : Finset (Fin 8)) (hs : 3 ≤ s.card) :
      |((∑ t : F, quadraticChar F (∏ i ∈ s, (1 + coeff i * t)) : ℤ) : ℝ)| ≤
        12 * (s.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
    have hs8 : s.card ≤ 8 := by simpa using Finset.card_le_univ s
    have h := coarse_quadratic_affine_bound hodd (fun i : s => coeff i)
      (by simpa using (show 0 < s.card by omega))
      (fun i j hij => Subtype.ext (hinj hij)) (fun i => hnz i)
      (by simp only [Fintype.card_coe]; nlinarith)
    have hprod (t : F) : (∏ i : s, (1 + coeff i * t)) =
        ∏ i ∈ s, (1 + coeff i * t) :=
      Finset.prod_coe_sort s (fun i => 1 + coeff i * t)
    simpa only [Fintype.card_coe, hprod] using h
  have hlower := affineSquareWeight_sum_lower_with_error hodd
    (fun r => 12 * (r : ℝ) * Real.sqrt (Fintype.card F : ℝ)) coeff hinj hnz hlarge
  have hsum : (∑ r ∈ Finset.range 9,
      if 3 ≤ r then (Nat.choose 8 r : ℝ) *
        (12 * (r : ℝ) * Real.sqrt (Fintype.card F : ℝ)) else 0) =
      11520 * Real.sqrt (Fintype.card F : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.choose]
    ring
  rw [hsum] at hlower
  calc
    _ ≤ ∑ t : F, affineSquareWeight coeff t := hlower
    _ ≤ ∑ t : F, if t ∈ centerOnePowerParameters 2 b then (256 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro t _
      simpa only [coeff, noncenter_squares_iff_mem] using affineSquareWeight_le_indicator coeff t
    _ = _ := by rw [Finset.sum_ite_mem]; simp [mul_comm]

/-- The coarser count suffices at the explicit threshold `11521²`. -/
theorem centerOne_coarse_numeric_bound {q : ℕ} (hq : 132733441 ≤ q) :
    (2304 : ℝ) < (q : ℝ) - 28 - 11520 * Real.sqrt (q : ℝ) := by
  have hqR : (132733441 : ℝ) ≤ q := by exact_mod_cast hq
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ q)
  have hs : (11521 : ℝ) ≤ Real.sqrt (q : ℝ) := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) hs0]

/-- **Unconditional existence of a magic square of nine distinct squares
in every odd finite field of cardinality at least `132733441`.**

This is a weaker numerical threshold than the paper's `553736`. Its proof
uses only the completed Stepánov estimate and elementary character theory,
with no analytic interface hypothesis. -/
theorem exists_centerOne_magic_of_squares_of_card_ge_132733441
    (hodd : ringChar F ≠ 2) (hq : 132733441 ≤ Fintype.card F) :
    ∃ M : Square3 F, IsMagicOfPowers 2 M := by
  obtain ⟨b, hb⟩ := exists_centerOneGoodB (F := F) hodd (by omega)
  have hlower := centerOne_square_count_coarse hodd (by omega) b hb
  have hnum := centerOne_coarse_numeric_bound hq
  have hcardR : (9 : ℝ) < (centerOnePowerParameters 2 b).card := by nlinarith
  have hcard : 9 < (centerOnePowerParameters 2 b).card := by exact_mod_cast hcardR
  obtain ⟨t, htpow, htbad⟩ := exists_power_parameter_outside_bad (F := F) hcard
  exact exists_centerOne_magic_of_powers_of_parameter 2 hb htpow htbad

/-- In particular, the cardinalities of odd Parker fields are bounded. -/
theorem not_isParker_of_card_ge_132733441
    (hodd : ringChar F ≠ 2) (hq : 132733441 ≤ Fintype.card F) : ¬ IsParker F := by
  intro hP
  exact hP (exists_centerOne_magic_of_squares_of_card_ge_132733441 hodd hq)

end MagicSquares.Square3
