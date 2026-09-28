import MagicSquares.Certificates.Q3Prime
import MagicSquares.CharacteristicTwo
import MagicSquares.Certificates.Q3Extension
import MagicSquares.Certificates.Q3PrimePowerCoverage
import MagicSquares.SquareQ1Classification
import MagicSquares.SquareExceptions
import MagicSquares.CenterOne.SquareCount

/-!
# Complete classification of Parker fields (paper, Theorem 9.1)

The proof first excludes cardinalities at least 553736 using the center-one
existence theorem. Below that bound, odd cardinalities split into two cases:
* q = 1 modulo 4: use the center-zero classification;
* q = 3 modulo 4: combine prime and extension-field certificate coverage.

The reverse implication uses the independently proved negative cases.
`squareParker_iff` then adds the characteristic-two obstruction.
-/

namespace MagicSquares
open Certificates

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Theorem 9.1: the complete odd-characteristic square classification.**
The large-field theorem, exhaustive coverage below 553736, all positive
prime and extension certificates, and every negative exception are proved. -/
theorem squareParker_iff_of_char_ne_two (hodd : ringChar F ≠ 2) :
    IsParker F ↔ Fintype.card F ∈
      ([3, 5, 7, 9, 11, 13, 17, 19, 23, 25, 27, 31, 43, 47, 67, 243] : List ℕ) := by
  constructor
  · intro h
    -- The analytic existence theorem bounds every possible exception.
    have hq : Fintype.card F < 553736 := by
      by_contra hq
      exact Square3.not_isParker_of_card_ge_553736 hodd (by omega) h
    -- Odd field orders are either 1 or 3 modulo 4.
    have hcardodd := FiniteField.odd_card_of_char_ne_two hodd
    have hm : Fintype.card F % 4 = 1 ∨ Fintype.card F % 4 = 3 := by omega
    rcases hm with hm | hm
    · have hc := (squareParker_iff_of_card_mod_four_one hm).mp h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      omega
    · have he : Fintype.card F ∈ q3Exceptions := by
        by_contra he
        -- Coverage separates prime fields from the remaining extension orders.
        obtain hp | hx := q3_prime_power_coverage hq (FiniteField.isPrimePow_card F) hm
        · exact not_squareParker_of_prime_card_q3 hp hq hm he h
        · have hn27 : Fintype.card F ≠ 27 := fun h27 => he (by simp [q3Exceptions, h27])
          have hn243 : Fintype.card F ≠ 243 := fun h243 => he (by simp [q3Exceptions, h243])
          have hw : Fintype.card F ∈
              ([343, 1331, 2187, 6859, 12167, 16807, 19683, 29791, 79507, 103823,
                161051, 177147, 205379, 300763, 357911, 493039] : List ℕ) := by
            simpa only [List.mem_cons, List.not_mem_nil, or_false, hn27, hn243, false_or] using hx
          exact not_squareParker_of_card_q3_extension hw h
      simp only [q3Exceptions, List.mem_cons, List.not_mem_nil, or_false] at he ⊢
      omega
  · exact squareParker_of_card_exception

/-- The square classification for every finite field, including characteristic two. -/
theorem squareParker_iff : IsParker F ↔ ringChar F = 2 ∨ Fintype.card F ∈
    ([3, 5, 7, 9, 11, 13, 17, 19, 23, 25, 27, 31, 43, 47, 67, 243] : List ℕ) := by
  by_cases ht : ringChar F = 2
  · haveI : CharP F 2 := by rw [← ht]; infer_instance
    exact ⟨fun _ => Or.inl ht, fun _ => isNParker_of_charTwo 2⟩
  · simpa only [ht, false_or] using squareParker_iff_of_char_ne_two ht

end MagicSquares
