import MagicSquares.Certificates.PrimeNegative
import MagicSquares.Certificates.PrimePositive
import MagicSquares.Certificates.QuadraticModels
import MagicSquares.CenterZero.Existence

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace MagicSquares
open Certificates

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem q1_card_coverage : ∀ q ∈ Finset.range 77, IsPrimePow q → q % 4 = 1 →
    q ∈ ([5, 9, 13, 17, 25, 29, 37, 41, 49, 53, 61, 73] : List ℕ) := by
  decide +kernel

omit [DecidableEq F] in
/-- All seven positive cases below the center-zero square bound. -/
theorem not_squareParker_of_card_q1_witness
    (hq : Fintype.card F ∈ ([29, 37, 41, 49, 53, 61, 73] : List ℕ)) : ¬ IsParker F := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with hq | hq | hq | hq | hq | hq | hq
  · letI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 2).mp h) ⟨_, square_witness_29⟩
  · letI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 2).mp h) ⟨_, square_witness_37⟩
  · letI : Fact (Nat.Prime 41) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 2).mp h) ⟨_, square_witness_41⟩
  · intro h
    have hc : Fintype.card F = Fintype.card Field49 := by simpa using hq
    exact ((isNParker_iff_of_card_eq hc 2).mp h) ⟨_, square_witness_49⟩
  · letI : Fact (Nat.Prime 53) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 2).mp h) ⟨_, square_witness_53⟩
  · letI : Fact (Nat.Prime 61) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 2).mp h) ⟨_, square_witness_61⟩
  · letI : Fact (Nat.Prime 73) := ⟨by norm_num⟩
    intro h
    exact ((isNParker_iff_zmod_of_card_eq hq 2).mp h) ⟨_, square_witness_73⟩

/-- **The complete `q ≡ 1 (mod 4)` square classification.** The analytic bound,
all small positive and negative certificates, and prime-power coverage are proved. -/
theorem squareParker_iff_of_card_mod_four_one
    (hmod : Fintype.card F % 4 = 1) :
    IsParker F ↔ Fintype.card F ∈ ([5, 9, 13, 17, 25] : List ℕ) := by
  have hodd : ringChar F ≠ 2 := by
    intro h
    have he := FiniteField.even_card_of_char_two h
    omega
  constructor
  · intro h
    have hq : Fintype.card F < 77 := by
      by_contra hq
      exact h (exists_centerZero_magic_of_squares_of_card_mod_four_one_unconditional
        hodd (by omega) hmod)
    have hc := q1_card_coverage _ (Finset.mem_range.mpr hq)
      (FiniteField.isPrimePow_card F) hmod
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
    all_goals first
      | (solve | simp [hc])
      | exact False.elim (not_squareParker_of_card_q1_witness (by simp [hc]) h)
  · intro hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with hq | hq | hq | hq | hq
    · apply squareParker_of_card_small
      simp [hq]
    · apply squareParker_of_card_small
      simp [hq]
    · apply squareParker_of_card_small
      simp [hq]
    · letI : Fact (Nat.Prime 17) := ⟨by decide⟩
      exact (isNParker_iff_zmod_of_card_eq hq 2).mpr square_parker_17
    · have hc : Fintype.card F = Fintype.card Field25 := by simpa using hq
      exact (isNParker_iff_of_card_eq hc 2).mpr square_parker_25

end MagicSquares
