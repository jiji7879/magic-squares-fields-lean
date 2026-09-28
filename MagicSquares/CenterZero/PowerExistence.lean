import MagicSquares.CenterZero.PowerCount

/-!
# Center-zero existence for general powers (paper, Theorem 12.1)

The counting input lives in `CenterZero.PowerCount`. Here the total weight
is compared with the weight of the collision parameters. A strict excess
supplies a parameter outside the bad set with nonzero power weight.

The remaining algebra turns the three conditions on x-1, x, and x+1 into
powers at all nine entries; the hypothesis on -1 handles their negatives.
-/

namespace MagicSquares

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
/-- Products of powers are powers. -/
theorem IsNthPower.mul {n : ℕ} {a b : F}
    (ha : IsNthPower n a) (hb : IsNthPower n b) : IsNthPower n (a * b) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x * y, mul_pow x y n⟩

omit [Fintype F] [DecidableEq F] in
/-- The sign condition makes every entry of the center-zero family a power. -/
theorem centerZero_all_entries_are_powers {n : ℕ} (hn : 0 < n) (x : F)
    (hneg : IsNthPower n (-1 : F))
    (hxm : IsNthPower n (x - 1)) (hx : IsNthPower n x)
    (hxp : IsNthPower n (x + 1)) :
    ∀ k : Fin 9, IsNthPower n ((Square3.centerZero x).entries k) := by
  have hnegx : IsNthPower n (-x) := by simpa using hneg.mul hx
  have hnegxm : IsNthPower n (1 - x) := by simpa [neg_sub] using hneg.mul hxm
  have hnegxp : IsNthPower n (-x - 1) := by
    simpa [neg_add_rev, sub_eq_add_neg, add_comm] using hneg.mul hxp
  have hzero : IsNthPower n (0 : F) := ⟨0, zero_pow hn.ne'⟩
  have hone : IsNthPower n (1 : F) := ⟨1, one_pow n⟩
  intro k
  fin_cases k <;> simp [Square3.entries, hnegx, hnegxm, hnegxp, hneg, hxm, hx, hxp, hzero, hone]

/-- **Theorem 12.1.** The exact center-zero sufficient inequality for
arbitrary powers, with all analytic and counting inputs proved. -/
theorem exists_centerZero_magic_of_powers_of_bound {n : ℕ} (hn : 0 < n)
    (hodd : ringChar F ≠ 2) (hneg : IsNthPower n (-1 : F))
    (hmain :
      4 * (powerIndex n (Fintype.card F) : ℝ) ^ 3 +
        3 * (powerIndex n (Fintype.card F) : ℝ) ^ 2 <
      (Fintype.card F : ℝ) - centerZeroC0 (powerIndex n (Fintype.card F)) *
        Real.sqrt (Fintype.card F : ℝ)) :
    ∃ x : F, IsMagicOfPowers n (Square3.centerZero x) := by
  let d := powerIndex n (Fintype.card F)
  have hd : 0 < d := powerIndex_pos hn
  -- Compare all parameter weights with the maximum weight of bad parameters.
  have hlower := centerZeroPowerWeight_sum_lower (F := F) hn hodd
  have hbad := centerZeroPowerWeight_bad_sum_le (F := F) (n := n) hd
  -- If every good parameter had zero weight, the strict inequality would fail.
  have hex : ∃ x : F, x ∉ (centerZeroBadValues : Finset F) ∧
      centerZeroPowerWeight n d x ≠ 0 := by
    by_contra h
    push Not at h
    have heq : ∑ x : F, centerZeroPowerWeight n d x =
        ∑ x ∈ (centerZeroBadValues : Finset F), centerZeroPowerWeight n d x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x _ hx
      exact h x hx
    rw [heq] at hlower
    linarith
  -- Extract the three power conditions and assemble the distinct magic square.
  obtain ⟨x, hx, hw⟩ := hex
  obtain ⟨hxm, hxp, hxpp⟩ := centerZeroPowerWeight_ne_zero_forces_powers hn hw
  exact ⟨x, Square3.centerZero_isMagic x,
    centerZero_pairwiseDistinct_of_not_mem_bad hodd hx,
    centerZero_all_entries_are_powers hn x hneg hxm hxp hxpp⟩

/-- The Section 12 conclusion in `n`-Parker terminology. -/
theorem not_isNParker_of_centerZero_bound {n : ℕ} (hn : 0 < n)
    (hodd : ringChar F ≠ 2) (hneg : IsNthPower n (-1 : F))
    (hmain :
      4 * (powerIndex n (Fintype.card F) : ℝ) ^ 3 +
        3 * (powerIndex n (Fintype.card F) : ℝ) ^ 2 <
      (Fintype.card F : ℝ) - centerZeroC0 (powerIndex n (Fintype.card F)) *
        Real.sqrt (Fintype.card F : ℝ)) : ¬ IsNParker F n := by
  obtain ⟨x, hx⟩ := exists_centerZero_magic_of_powers_of_bound hn hodd hneg hmain
  exact fun hP => hP ⟨Square3.centerZero x, hx⟩

omit [Fintype F] [DecidableEq F] in
/-- In particular the sign condition is automatic for odd exponents. -/
theorem isNthPower_neg_one_of_odd {n : ℕ} (hn : Odd n) :
    IsNthPower n (-1 : F) := ⟨-1, hn.neg_one_pow⟩

end MagicSquares
