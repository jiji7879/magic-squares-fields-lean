import MagicSquares.QuadraticCharacterSums
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace MagicSquares

/-- The exact cubic Weil estimate needed in Section 6 of the paper.

This is intentionally isolated as an interface while the LN97
Stepanov--Schmidt proof is formalized.  No axiom is introduced: downstream
results take a proof of this proposition as an explicit hypothesis. -/
def HasCenterZeroCubicWeilBound
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Prop :=
  |((∑ x : F,
      (quadraticChar F) ((x - 1) * x * (x + 1)) : ℤ) : ℝ)|
    ≤ 2 * Real.sqrt (Fintype.card F : ℝ)

end MagicSquares
