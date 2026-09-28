import MagicSquares.Stepanov.Lemma645.Abstract
import MagicSquares.Stepanov.Lemma653.RealArithmetic
import MagicSquares.Stepanov.Lemma653.ErrorTerm
import Mathlib.Tactic

namespace MagicSquares
namespace LN97

/-!
# Theorem 6.53 from the two Stepanov set bounds

This theorem isolates exactly what remains after Lemma 6.52 supplies
(6.28) for the two choices of `B`.
-/

/-- Abstract numerical form of LN97 Theorem 6.53. -/
theorem ln97_6_53_from_two_T_bounds
    (C : Lemma645Counts)
    (k : ℝ)
    (hm : 0 < (C.m : ℝ))
    (h01 :
      (C.t0 : ℝ) + C.t1 <
        (C.q : ℝ) / C.m +
          4 * k * Real.sqrt C.m * Real.sqrt C.q)
    (h02 :
      (C.t0 : ℝ) + C.t2 <
        ((C.m : ℝ) - 1) * C.q / C.m +
          4 * k * Real.sqrt C.m * Real.sqrt C.q) :
    |(C.N : ℝ) - C.q| <
      (C.m : ℝ) *
        (4 * k * Real.sqrt C.m * Real.sqrt C.q) := by
  have hmNat : 0 < C.m := by
    exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ C.m := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hmNat))
  apply theorem653_abs_arithmetic
    (q := C.q) (m := C.m) (N := C.N)
    (t0 := C.t0) (t1 := C.t1) (t2 := C.t2)
    (A := 4 * k * Real.sqrt C.m * Real.sqrt C.q)
    hm hm1
  · exact_mod_cast C.solutions
  · exact_mod_cast C.partition
  · exact h01
  · exact h02
  · positivity

end LN97
end MagicSquares
