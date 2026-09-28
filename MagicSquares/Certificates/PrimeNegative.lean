import MagicSquares.PrunedSearch
import MagicSquares.FieldTransport
import MagicSquares.SmallFieldObstructions

/-! Kernel-checked negative certificates for the prime fields in the
square and cube classification tables. No native evaluation is trusted. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace MagicSquares.Certificates

/-- The complete normalized search fails over `ZMod 17` for exponent 2. -/
theorem square_parker_17 : letI : Fact (Nat.Prime 17) := ⟨by decide⟩;
    IsNParker (ZMod 17) 2 := by
  letI : Fact (Nat.Prime 17) := ⟨by decide⟩
  rw [isNParker_iff_prunedPowerSearch_eq_false (by decide : 0 < 2)]
  decide +kernel

/-- The complete normalized search fails over `ZMod 19` for exponent 2. -/
theorem square_parker_19 : letI : Fact (Nat.Prime 19) := ⟨by decide⟩;
    IsNParker (ZMod 19) 2 := by
  letI : Fact (Nat.Prime 19) := ⟨by decide⟩
  rw [isNParker_iff_prunedPowerSearch_eq_false (by decide : 0 < 2)]
  decide +kernel

/-- The complete normalized search fails over `ZMod 23` for exponent 2. -/
theorem square_parker_23 : letI : Fact (Nat.Prime 23) := ⟨by decide⟩;
    IsNParker (ZMod 23) 2 := by
  letI : Fact (Nat.Prime 23) := ⟨by decide⟩
  rw [isNParker_iff_prunedPowerSearch_eq_false (by decide : 0 < 2)]
  decide +kernel

/-- The complete normalized search fails over `ZMod 31` for exponent 2. -/
theorem square_parker_31 : letI : Fact (Nat.Prime 31) := ⟨by decide⟩;
    IsNParker (ZMod 31) 2 := by
  letI : Fact (Nat.Prime 31) := ⟨by decide⟩
  rw [isNParker_iff_prunedPowerSearch_eq_false (by decide : 0 < 2)]
  decide +kernel

/-- The complete normalized search fails over `ZMod 43` for exponent 2. -/
theorem square_parker_43 : letI : Fact (Nat.Prime 43) := ⟨by decide⟩;
    IsNParker (ZMod 43) 2 := by
  letI : Fact (Nat.Prime 43) := ⟨by decide⟩
  rw [isNParker_iff_prunedPowerSearch_eq_false (by decide : 0 < 2)]
  decide +kernel

/-- The complete normalized search fails over `ZMod 47` for exponent 2. -/
theorem square_parker_47 : letI : Fact (Nat.Prime 47) := ⟨by decide⟩;
    IsNParker (ZMod 47) 2 := by
  letI : Fact (Nat.Prime 47) := ⟨by decide⟩
  rw [isNParker_iff_prunedPowerSearch_eq_false (by decide : 0 < 2)]
  decide +kernel

/-- The complete normalized search fails over `ZMod 67` for exponent 2. -/
theorem square_parker_67 : letI : Fact (Nat.Prime 67) := ⟨by decide⟩;
    IsNParker (ZMod 67) 2 := by
  letI : Fact (Nat.Prime 67) := ⟨by decide⟩
  rw [isNParker_iff_prunedPowerSearch_eq_false (by decide : 0 < 2)]
  decide +kernel

/-- The complete normalized search fails over `ZMod 31` for exponent 3. -/
theorem cube_parker_31 : letI : Fact (Nat.Prime 31) := ⟨by decide⟩;
    IsNParker (ZMod 31) 3 := by
  letI : Fact (Nat.Prime 31) := ⟨by decide⟩
  rw [isNParker_iff_prunedPowerSearch_eq_false (by decide : 0 < 3)]
  decide +kernel

/-- The complete normalized search fails over `ZMod 37` for exponent 3. -/
theorem cube_parker_37 : letI : Fact (Nat.Prime 37) := ⟨by decide⟩;
    IsNParker (ZMod 37) 3 := by
  letI : Fact (Nat.Prime 37) := ⟨by decide⟩
  rw [isNParker_iff_prunedPowerSearch_eq_false (by decide : 0 < 3)]
  decide +kernel

/-- The complete normalized search fails over `ZMod 43` for exponent 3. -/
theorem cube_parker_43 : letI : Fact (Nat.Prime 43) := ⟨by decide⟩;
    IsNParker (ZMod 43) 3 := by
  letI : Fact (Nat.Prime 43) := ⟨by decide⟩
  rw [isNParker_iff_prunedPowerSearch_eq_false (by decide : 0 < 3)]
  decide +kernel

/-- The complete normalized search fails over `ZMod 61` for exponent 3. -/
theorem cube_parker_61 : letI : Fact (Nat.Prime 61) := ⟨by decide⟩;
    IsNParker (ZMod 61) 3 := by
  letI : Fact (Nat.Prime 61) := ⟨by decide⟩
  rw [isNParker_iff_prunedPowerSearch_eq_false (by decide : 0 < 3)]
  decide +kernel

/-- The complete normalized search fails over `ZMod 67` for exponent 3. -/
theorem cube_parker_67 : letI : Fact (Nat.Prime 67) := ⟨by decide⟩;
    IsNParker (ZMod 67) 3 := by
  letI : Fact (Nat.Prime 67) := ⟨by decide⟩
  rw [isNParker_iff_prunedPowerSearch_eq_false (by decide : 0 < 3)]
  decide +kernel

/-- The complete normalized search fails over `ZMod 79` for exponent 3. -/
theorem cube_parker_79 : letI : Fact (Nat.Prime 79) := ⟨by decide⟩;
    IsNParker (ZMod 79) 3 := by
  letI : Fact (Nat.Prime 79) := ⟨by decide⟩
  rw [isNParker_iff_prunedPowerSearch_eq_false (by decide : 0 < 3)]
  decide +kernel

/-- The complete normalized search fails over `ZMod 127` for exponent 3. -/
theorem cube_parker_127 : letI : Fact (Nat.Prime 127) := ⟨by decide⟩;
    IsNParker (ZMod 127) 3 := by
  letI : Fact (Nat.Prime 127) := ⟨by decide⟩
  rw [isNParker_iff_prunedPowerSearch_eq_false (by decide : 0 < 3)]
  decide +kernel

end MagicSquares.Certificates
