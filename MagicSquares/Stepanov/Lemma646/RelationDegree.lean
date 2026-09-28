import MagicSquares.Stepanov.Lemma646.RelationPolynomial
import MagicSquares.Stepanov.Lemma652.Degree
import Mathlib.Tactic

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# A coarse degree envelope for first-block relations

This is not yet the Kummer argument, but it makes the degree restriction
in Lemma 6.46 explicit and reusable.
-/

omit [Fintype F] in
/-- If every `a_i` has degree at most `D` and `deg g ≤ G`, then the
ordinary first-block relation has degree at most
`D + (m-1)G`. -/
theorem quotientPowerRelationPolynomial_natDegree_le
    {m D G : ℕ}
    (a : Fin m → Polynomial F)
    (g : Polynomial F)
    (ha : ∀ i, (a i).natDegree ≤ D)
    (hg : g.natDegree ≤ G) :
    (quotientPowerRelationPolynomial a g).natDegree
      ≤ D + (m - 1) * G := by
  unfold quotientPowerRelationPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  have him : (i : ℕ) ≤ m - 1 := by
    omega
  have hpow :
      (g ^ (i : ℕ)).natDegree ≤ (m - 1) * G := by
    rw [Polynomial.natDegree_pow]
    exact le_trans
      (Nat.mul_le_mul_right g.natDegree him)
      (Nat.mul_le_mul_left (m - 1) hg)
  exact le_trans
    (natDegree_mul_le_add (F := F) (a i) (g ^ (i : ℕ)))
    (Nat.add_le_add (ha i) hpow)

end LN97
end MagicSquares
