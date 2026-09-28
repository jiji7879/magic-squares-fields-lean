import MagicSquares.Certificates.PrimeNegative
import MagicSquares.Certificates.QuadraticModels
import MagicSquares.Certificates.CubicModels
import MagicSquares.Certificates.QuinticModel

namespace MagicSquares
open Certificates

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Every field in the square exception table is Parker. This proves the
nonexistence direction of Theorem 9.1, including the extension fields
of orders 25, 27 and 243. -/
theorem squareParker_of_card_exception
    (hq : Fintype.card F ∈ ([3, 5, 7, 9, 11, 13, 17, 19, 23, 25, 27, 31, 43, 47, 67, 243] : List ℕ)) : IsParker F := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq
  · apply squareParker_of_card_small
    simp [hq]
  · apply squareParker_of_card_small
    simp [hq]
  · apply squareParker_of_card_small
    simp [hq]
  · apply squareParker_of_card_small
    simp [hq]
  · apply squareParker_of_card_small
    simp [hq]
  · apply squareParker_of_card_small
    simp [hq]
  · letI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
    exact (isNParker_iff_zmod_of_card_eq hq 2).mpr square_parker_17
  · letI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    exact (isNParker_iff_zmod_of_card_eq hq 2).mpr square_parker_19
  · letI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    exact (isNParker_iff_zmod_of_card_eq hq 2).mpr square_parker_23
  · have hc : Fintype.card F = Fintype.card Field25 := by simpa using hq
    exact (isNParker_iff_of_card_eq hc 2).mpr square_parker_25
  · have hc : Fintype.card F = Fintype.card Field27 := by simpa using hq
    exact (isNParker_iff_of_card_eq hc 2).mpr square_parker_27
  · letI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
    exact (isNParker_iff_zmod_of_card_eq hq 2).mpr square_parker_31
  · letI : Fact (Nat.Prime 43) := ⟨by norm_num⟩
    exact (isNParker_iff_zmod_of_card_eq hq 2).mpr square_parker_43
  · letI : Fact (Nat.Prime 47) := ⟨by norm_num⟩
    exact (isNParker_iff_zmod_of_card_eq hq 2).mpr square_parker_47
  · letI : Fact (Nat.Prime 67) := ⟨by norm_num⟩
    exact (isNParker_iff_zmod_of_card_eq hq 2).mpr square_parker_67
  · have hc : Fintype.card F = Fintype.card Field243 := by simpa using hq
    exact (isNParker_iff_of_card_eq hc 2).mpr square_parker_243

end MagicSquares
