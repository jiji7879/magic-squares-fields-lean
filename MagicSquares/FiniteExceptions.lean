import MagicSquares.CenterOne.PowerCount

/-!
# Finitely many odd n-Parker cardinalities (paper, Theorem 15.1)

The center-one existence theorem uses an inequality involving the power
index d = gcd(n, q - 1). This file bounds its constants using d <= n, then
shows that q > (10*n^8 + 10)^2 implies the required inequality.

Thus every exceptional odd cardinality lies in a finite initial interval.
The numerical bound is sufficient, not an optimal cutoff.
-/

namespace MagicSquares

/-- An explicit (deliberately nonoptimal) uniform bound of order `n^16`. -/
def powerExceptionBound (n : ℕ) : ℕ := (10 * n ^ 8 + 10) ^ 2

/-- The Section 14 constant is uniformly bounded in terms of the exponent. -/
theorem centerOneC1_le_eight_pow {n d : ℕ} (hn : 0 < n) (hdn : d ≤ n) :
    centerOneC1 d ≤ 8 * (n : ℝ) ^ 8 := by
  have hpow : (d : ℝ) ^ 8 ≤ (n : ℝ) ^ 8 := by
    exact_mod_cast Nat.pow_le_pow_left hdn 8
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 8 :=
    one_le_pow₀ (by exact_mod_cast hn)
  have hd7 : (0 : ℝ) ≤ (d : ℝ) ^ 7 := by positivity
  unfold centerOneC1
  nlinarith

/-- Above the explicit bound, the exact numerical hypothesis of
Theorem 14.1 holds for every possible power index. -/
theorem centerOne_power_inequality_of_bound {n d q : ℕ}
    (hn : 0 < n) (hdn : d ≤ n) (hq : powerExceptionBound n < q) :
    9 * (d : ℝ) ^ 8 < (q : ℝ) - centerOneC1 d * Real.sqrt (q : ℝ) := by
  have hqR : (10 * (n : ℝ) ^ 8 + 10) ^ 2 < (q : ℝ) := by
    exact_mod_cast hq
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 8 :=
    one_le_pow₀ (by exact_mod_cast hn)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ (q : ℝ) by positivity)
  have ht0 := Real.sqrt_nonneg (q : ℝ)
  have ht : 10 * (n : ℝ) ^ 8 + 10 < Real.sqrt (q : ℝ) := by
    by_contra h
    have hle := le_of_not_gt h
    have hm := mul_nonneg (sub_nonneg.mpr hle)
      (show 0 ≤ 10 * (n : ℝ) ^ 8 + 10 + Real.sqrt (q : ℝ) by positivity)
    nlinarith
  have hC := mul_le_mul_of_nonneg_right (centerOneC1_le_eight_pow hn hdn) ht0
  have hpow : (d : ℝ) ^ 8 ≤ (n : ℝ) ^ 8 := by
    exact_mod_cast Nat.pow_le_pow_left hdn 8
  have hm := mul_pos (show 0 < Real.sqrt (q : ℝ) by linarith)
    (show 0 < Real.sqrt (q : ℝ) - 8 * (n : ℝ) ^ 8 - 10 by linarith)
  nlinarith

namespace Square3

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Theorem 15.1, explicit form.** Every odd finite field with more than
`(10*n^8+10)^2` elements contains a magic square of nine distinct `n`-th powers. -/
theorem exists_magic_of_powers_of_card_gt_bound {n : ℕ} (hn : 0 < n)
    (hodd : ringChar F ≠ 2) (hq : powerExceptionBound n < Fintype.card F) :
    ∃ M : Square3 F, IsMagicOfPowers n M := by
  have hlarge : 7 < Fintype.card F := by
    have hb : 7 < powerExceptionBound n := by
      unfold powerExceptionBound
      nlinarith [Nat.zero_le (n ^ 8)]
    exact hb.trans hq
  exact exists_centerOne_magic_of_powers_of_bound hn hodd hlarge
    (centerOne_power_inequality_of_bound hn (powerIndex_le_left _ _ hn) hq)

/-- The uniform finite-exception bound, in `n`-Parker terminology. -/
theorem not_isNParker_of_card_gt_bound {n : ℕ} (hn : 0 < n)
    (hodd : ringChar F ≠ 2) (hq : powerExceptionBound n < Fintype.card F) :
    ¬ IsNParker F n := by
  intro hP
  exact hP (exists_magic_of_powers_of_card_gt_bound hn hodd hq)

/-- Every exceptional odd field has bounded cardinality. -/
theorem card_le_powerExceptionBound_of_isNParker {n : ℕ} (hn : 0 < n)
    (hodd : ringChar F ≠ 2) (hP : IsNParker F n) :
    Fintype.card F ≤ powerExceptionBound n := by
  by_contra h
  exact not_isNParker_of_card_gt_bound hn hodd (Nat.lt_of_not_ge h) hP

end Square3

/-- **Theorem 15.1.** For each fixed positive `n`, there are only finitely
many cardinalities of odd finite fields that are `n`-Parker. Finite fields
are classified up to isomorphism by their cardinalities. -/
theorem finite_nParker_cardinalities {n : ℕ} (hn : 0 < n) :
    Set.Finite {q : ℕ | ∃ (F : Type) (_ : Field F) (_ : Fintype F),
      ringChar F ≠ 2 ∧ Fintype.card F = q ∧ IsNParker F n} := by
  classical
  apply (Set.finite_Iic (powerExceptionBound n)).subset
  rintro q ⟨F, hfield, hfinite, hodd, rfl, hP⟩
  exact Square3.card_le_powerExceptionBound_of_isNParker hn hodd hP

end MagicSquares
