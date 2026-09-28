import MagicSquares.Stepanov.Lemma653.SetBound
import MagicSquares.Stepanov.Lemma653.SpecialPolynomials
import MagicSquares.Stepanov.Lemma653.Abstract

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# Lidl--Niederreiter Theorem 6.53

The completed Lemmas 6.45 and 6.52 give the point count for the actual
curve `y^m=f(x)`, with no separate counting or auxiliary-polynomial
assumptions.  Applying (6.28) to `X-1` and the geometric polynomial yields
the two bounds used in the numerical proof.
-/

theorem stepanovFullT_B1 (m : ℕ) (f : Polynomial F) :
    stepanovFullT m f theorem653B1 = stepanovT0 f ∪ stepanovT1 m f := by
  ext c
  simp [stepanovFullT, theorem653B1, Polynomial.IsRoot, sub_eq_zero]

theorem stepanovFullT_B2 (m : ℕ) (f : Polynomial F) :
    stepanovFullT m f (theorem653B2 m) = stepanovT0 f ∪ stepanovT2 m f := by
  ext c
  simp [stepanovFullT, theorem653B2, Polynomial.IsRoot]

/-- **Lidl--Niederreiter Theorem 6.53.**  If `m≥2` divides `q-1`,
`deg f=k≥1`, `Y^m-f(X)` is absolutely irreducible, and `q≥100mk²`,
then the number `N` of pairs satisfying `y^m=f(x)` obeys
`|N-q| < 4 k m^(3/2) sqrt(q)`. -/
theorem ln97_6_53 {m : ℕ} (hm : 2 ≤ m) (hmq : m ∣ Fintype.card F - 1)
    (f : Polynomial F) (hk : 0 < f.natDegree)
    (hirr : KummerAbsolutelyIrreducible m f)
    (hq : 100 * m * f.natDegree ^ 2 ≤ Fintype.card F) :
    |(stepanovSolutionCount m f : ℝ) - Fintype.card F| <
      4 * f.natDegree * (m : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Fintype.card F) := by
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have h01 := ln97_6_28 hm hmq f hk hirr hq theorem653B1
    (by simp) (by simp only [theorem653B1_natDegree]; omega)
  rw [stepanovFullT_B1, Finset.card_union_of_disjoint (stepanovT0_disjoint_T1 hmq f)] at h01
  simp only [theorem653B1_natDegree, Nat.cast_add, Nat.cast_one, one_mul] at h01
  have h02 := ln97_6_28 hm hmq f hk hirr hq (theorem653B2 m)
    (by rw [theorem653B2_natDegree m (by omega)]; omega)
    (by rw [theorem653B2_natDegree m (by omega)]; omega)
  rw [stepanovFullT_B2,
    Finset.card_union_of_disjoint (stepanovT0_disjoint_T2 hm0 hmq f),
    theorem653B2_natDegree m (by omega)] at h02
  simp only [Nat.cast_add, Nat.cast_sub (show 1 ≤ m by omega), Nat.cast_one] at h02
  have hmain := ln97_6_53_from_two_T_bounds (lemma645CountsOfField hm0 hmq f)
    f.natDegree hmR h01 h02
  change |(stepanovSolutionCount m f : ℝ) - Fintype.card F| <
    (m : ℝ) * (4 * f.natDegree * Real.sqrt m * Real.sqrt (Fintype.card F)) at hmain
  rw [theorem653_error_rewrite, mul_sqrt_eq_rpow_three_halves _ (by positivity)] at hmain
  exact hmain

end LN97
end MagicSquares
