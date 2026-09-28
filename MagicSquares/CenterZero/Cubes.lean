import MagicSquares.CenterZero.PowerBounds

namespace MagicSquares

/-- The exact cubic numerical inequality holds from `q = 1037` onward. -/
theorem cube_centerZero_inequality {q : ℕ} (hq : 1037 ≤ q) :
    (135 : ℝ) < (q : ℝ) - 28 * Real.sqrt (q : ℝ) := cube_numeric_bound hq

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Section 13, explicit cube bound.** Every odd finite field with at
least `1037` elements has a center-zero magic square of nine distinct cubes. -/
theorem exists_centerZero_magic_of_cubes_of_card_ge_1037
    (hodd : ringChar F ≠ 2) (hq : 1037 ≤ Fintype.card F) :
    ∃ x : F, IsMagicOfPowers 3 (Square3.centerZero x) := by
  apply exists_centerZero_magic_of_powers_of_bound (by norm_num) hodd
    (isNthPower_neg_one_of_odd (by decide : Odd 3))
  have hd : powerIndex 3 (Fintype.card F) = 1 ∨ powerIndex 3 (Fintype.card F) = 3 := by
    exact (Nat.dvd_prime (by decide : Nat.Prime 3)).mp
      (Nat.gcd_dvd_left 3 (Fintype.card F - 1))
  rcases hd with hd | hd
  · rw [hd]
    norm_num [centerZeroC0]
    exact_mod_cast (show 7 < Fintype.card F by omega)
  · rw [hd]
    norm_num [centerZeroC0]
    exact cube_centerZero_inequality hq

/-- Consequently every odd cube-Parker field has fewer than `1037` elements. -/
theorem card_lt_1037_of_cubeParker
    (hodd : ringChar F ≠ 2) (hP : IsNParker F 3) : Fintype.card F < 1037 := by
  by_contra h
  obtain ⟨x, hx⟩ := exists_centerZero_magic_of_cubes_of_card_ge_1037 hodd (Nat.le_of_not_gt h)
  exact hP ⟨Square3.centerZero x, hx⟩

end MagicSquares
