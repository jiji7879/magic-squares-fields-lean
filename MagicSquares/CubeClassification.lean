import MagicSquares.CubePrimeClassification
import MagicSquares.Certificates.CubicModels
import MagicSquares.Certificates.QuadraticPositive
import MagicSquares.PowerIndexOne

/-!
# Complete classification of 3-Parker fields (paper, Theorem 13.1)

The center-zero existence bound reduces the problem to odd prime powers
below 1037. Prime fields use `cubeParker_iff_of_prime_card`. Extension fields
fall into three groups: trivial cube index, explicit positive witnesses,
and the two exceptions of cardinalities 25 and 343.

The finite coverage lemma proves that this case split is exhaustive.
The final reverse implication transports the negative certificates.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace MagicSquares
open Certificates

local instance cubeClassificationDecidablePrime (n : ℕ) : Decidable n.Prime := Nat.decidablePrime' n

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

-- Exhaustive arithmetic coverage; each listed order is handled below.
private theorem cube_card_coverage : ∀ q ∈ Finset.range 1037,
    IsPrimePow q → q % 2 = 1 →
      q.Prime ∨ q ∈ ([9, 25, 27, 49, 81, 121, 125, 169, 243, 289, 343, 361, 529, 625, 729, 841, 961] : List ℕ) := by
  decide +kernel

omit [DecidableEq F] in
/-- Positive certificates for all extension fields with nontrivial cube index
below the analytic bound, apart from the two certified exceptions. -/
theorem not_cubeParker_of_card_extension_witness
    (hq : Fintype.card F ∈ ([49, 121, 169, 289, 361, 529, 625, 841, 961] : List ℕ)) : ¬ IsNParker F 3 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with hq | hq | hq | hq | hq | hq | hq | hq | hq
  · intro h
    have hc : Fintype.card F = Fintype.card Field49 := by simpa using hq
    exact ((isNParker_iff_of_card_eq hc 3).mp h) ⟨_, cube_witness_49⟩
  · intro h
    have hc : Fintype.card F = Fintype.card Field121 := by simpa using hq
    exact ((isNParker_iff_of_card_eq hc 3).mp h) ⟨_, cube_witness_121⟩
  · intro h
    have hc : Fintype.card F = Fintype.card Field169 := by simpa using hq
    exact ((isNParker_iff_of_card_eq hc 3).mp h) ⟨_, cube_witness_169⟩
  · intro h
    have hc : Fintype.card F = Fintype.card Field289 := by simpa using hq
    exact ((isNParker_iff_of_card_eq hc 3).mp h) ⟨_, cube_witness_289⟩
  · intro h
    have hc : Fintype.card F = Fintype.card Field361 := by simpa using hq
    exact ((isNParker_iff_of_card_eq hc 3).mp h) ⟨_, cube_witness_361⟩
  · intro h
    have hc : Fintype.card F = Fintype.card Field529 := by simpa using hq
    exact ((isNParker_iff_of_card_eq hc 3).mp h) ⟨_, cube_witness_529⟩
  · intro h
    have hc : Fintype.card F = Fintype.card Field625 := by simpa using hq
    exact ((isNParker_iff_of_card_eq hc 3).mp h) ⟨_, cube_witness_625⟩
  · intro h
    have hc : Fintype.card F = Fintype.card Field841 := by simpa using hq
    exact ((isNParker_iff_of_card_eq hc 3).mp h) ⟨_, cube_witness_841⟩
  · intro h
    have hc : Fintype.card F = Fintype.card Field961 := by simpa using hq
    exact ((isNParker_iff_of_card_eq hc 3).mp h) ⟨_, cube_witness_961⟩

/-- **Theorem 13.1: the complete odd-characteristic cube classification.**
The large-field theorem, finite prime-power coverage, all positive witnesses,
and every negative search certificate are checked by Lean. -/
theorem cubeParker_iff_of_char_ne_two (hodd : ringChar F ≠ 2) :
    IsNParker F 3 ↔ Fintype.card F ∈ ([3, 5, 7, 13, 19, 25, 31, 37, 43, 61, 67, 79, 127, 343] : List ℕ) := by
  constructor
  · intro h
    -- First reduce the classification to the finite interval below 1037.
    have hq := card_lt_1037_of_cubeParker hodd h
    obtain hp | he := cube_card_coverage _ (Finset.mem_range.mpr hq)
      (FiniteField.isPrimePow_card F) (FiniteField.odd_card_of_char_ne_two hodd)
    · have hp' := (cubeParker_iff_of_prime_card hp hodd).mp h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp' ⊢
      rcases hp' with hp' | hp' | hp' | hp' | hp' | hp' | hp' | hp' | hp' | hp' | hp' | hp'
      all_goals simp [hp']
    -- Extension cases follow the order of the list in cube_card_coverage.
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he | he
      -- q = 9: every element is a cube.
      · exact False.elim (h (exists_magic_of_powers_of_powerIndex_eq_one
          (by decide : 0 < 3) hodd (by omega)
          (by norm_num [he, powerIndex, Nat.gcd])))
      -- q = 25: exceptional field.
      · simp [he]
      -- q = 27: every element is a cube.
      · exact False.elim (h (exists_magic_of_powers_of_powerIndex_eq_one
          (by decide : 0 < 3) hodd (by omega)
          (by norm_num [he, powerIndex, Nat.gcd])))
      -- q = 49: explicit positive certificate.
      · exact False.elim (not_cubeParker_of_card_extension_witness (by simp [he]) h)
      -- q = 81: every element is a cube.
      · exact False.elim (h (exists_magic_of_powers_of_powerIndex_eq_one
          (by decide : 0 < 3) hodd (by omega)
          (by norm_num [he, powerIndex, Nat.gcd])))
      -- q = 121: explicit positive certificate.
      · exact False.elim (not_cubeParker_of_card_extension_witness (by simp [he]) h)
      -- q = 125: every element is a cube.
      · exact False.elim (h (exists_magic_of_powers_of_powerIndex_eq_one
          (by decide : 0 < 3) hodd (by omega)
          (by norm_num [he, powerIndex, Nat.gcd])))
      -- q = 169: explicit positive certificate.
      · exact False.elim (not_cubeParker_of_card_extension_witness (by simp [he]) h)
      -- q = 243: every element is a cube.
      · exact False.elim (h (exists_magic_of_powers_of_powerIndex_eq_one
          (by decide : 0 < 3) hodd (by omega)
          (by norm_num [he, powerIndex, Nat.gcd])))
      -- q = 289: explicit positive certificate.
      · exact False.elim (not_cubeParker_of_card_extension_witness (by simp [he]) h)
      -- q = 343: exceptional field.
      · simp [he]
      -- q = 361: explicit positive certificate.
      · exact False.elim (not_cubeParker_of_card_extension_witness (by simp [he]) h)
      -- q = 529: explicit positive certificate.
      · exact False.elim (not_cubeParker_of_card_extension_witness (by simp [he]) h)
      -- q = 625: explicit positive certificate.
      · exact False.elim (not_cubeParker_of_card_extension_witness (by simp [he]) h)
      -- q = 729: every element is a cube.
      · exact False.elim (h (exists_magic_of_powers_of_powerIndex_eq_one
          (by decide : 0 < 3) hodd (by omega)
          (by norm_num [he, powerIndex, Nat.gcd])))
      -- q = 841: explicit positive certificate.
      · exact False.elim (not_cubeParker_of_card_extension_witness (by simp [he]) h)
      -- q = 961: explicit positive certificate.
      · exact False.elim (not_cubeParker_of_card_extension_witness (by simp [he]) h)
  · intro hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq
    · apply cubeParker_of_card_prime_exception
      simp [hq]
    · apply cubeParker_of_card_prime_exception
      simp [hq]
    · apply cubeParker_of_card_prime_exception
      simp [hq]
    · apply cubeParker_of_card_prime_exception
      simp [hq]
    · apply cubeParker_of_card_prime_exception
      simp [hq]
    · have hc : Fintype.card F = Fintype.card Field25 := by simpa using hq
      exact (isNParker_iff_of_card_eq hc 3).mpr cube_parker_25
    · apply cubeParker_of_card_prime_exception
      simp [hq]
    · apply cubeParker_of_card_prime_exception
      simp [hq]
    · apply cubeParker_of_card_prime_exception
      simp [hq]
    · apply cubeParker_of_card_prime_exception
      simp [hq]
    · apply cubeParker_of_card_prime_exception
      simp [hq]
    · apply cubeParker_of_card_prime_exception
      simp [hq]
    · apply cubeParker_of_card_prime_exception
      simp [hq]
    · have hc : Fintype.card F = Fintype.card Field343 := by simpa using hq
      exact (isNParker_iff_of_card_eq hc 3).mpr cube_parker_343

end MagicSquares
