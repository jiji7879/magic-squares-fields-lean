import MagicSquares.Stepanov.Lemma646.AbsoluteIrreducibility
import MagicSquares.Stepanov.Lemma646.BlockTranslation

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F]

/-!
# Lidl--Niederreiter Lemma 6.46

This completes the block-independence lemma from the book's absolute
irreducibility hypothesis, including the case `f(0) = 0`.

The final theorem writes the book's coefficient-degree allowance without
truncated subtraction: every nonzero coefficient `e` satisfies
`m * (natDegree e + natDegree f) ≤ q`.  For nonzero `e`, this is precisely
`deg e ≤ q/m - deg f`.  Zero coefficients are allowed in every degree
range.  Consequently the theorem also covers a negative allowance.
-/

/-- Lemma 6.46 with a general strict degree budget. -/
theorem ln97_6_46_of_degree_budget
    {m D : ℕ} (hm : 2 ≤ m) (hmq : m ∣ Fintype.card F - 1)
    (f : Polynomial F) (hf : f ≠ 0)
    (hirr : KummerAbsolutelyIrreducible m f)
    (hbudget : m * D + (m - 1) * f.natDegree < Fintype.card F)
    (E : Fin m → Polynomial (Polynomial F))
    (hdeg : ∀ i j, ((E i).coeff j).natDegree ≤ D)
    (hrel : BlockRelation (Fintype.card F) (f ^ ((Fintype.card F - 1) / m)) E) :
    ∀ i, E i = 0 := by
  have hm0 : 0 < m := by omega
  have hkq : f.natDegree < Fintype.card F := by
    have hmul : f.natDegree ≤ (m - 1) * f.natDegree := by
      calc
        f.natDegree = 1 * f.natDegree := by omega
        _ ≤ (m - 1) * f.natDegree := Nat.mul_le_mul_right _ (by omega)
    omega
  obtain ⟨c, hc⟩ := exists_eval_ne_zero_of_natDegree_lt_card f hf hkq
  obtain ⟨zeta, hzeta⟩ := exists_primitiveRoot_of_dvd_card_sub_one hm0 hmq
  have hc0 : (Polynomial.taylor c f).eval 0 ≠ 0 := by
    simpa only [Polynomial.taylor_eval, zero_add] using hc
  have hbudget' : m * D + (m - 1) * (Polynomial.taylor c f).natDegree <
      Fintype.card F := by
    simpa only [Polynomial.natDegree_taylor] using hbudget
  have hrel' := hrel.blockTranslate c
  rw [Polynomial.taylor_pow] at hrel'
  have hz := ln97_6_46_of_normalized_irreducible hm0 hmq hzeta
    (Polynomial.taylor c f) hc0 hbudget'
    ((hirr.taylor c).normalized_irreducible hm0 hc0)
    (fun i => blockTranslate c (E i))
    (fun i => coeffNatDegreeLE_blockTranslate (hdeg i) c) hrel'
  intro i
  exact (blockTranslate_eq_zero_iff c (E i)).mp (hz i)

/-- The book's degree allowance in the nonnegative range, using natural
subtraction only after establishing `deg f ≤ q / m`. -/
theorem ln97_6_46_of_natDegree_bound
    {m : ℕ} (hm : 2 ≤ m) (hmq : m ∣ Fintype.card F - 1)
    (f : Polynomial F) (hk : 0 < f.natDegree)
    (hkq : f.natDegree ≤ Fintype.card F / m)
    (hirr : KummerAbsolutelyIrreducible m f)
    (E : Fin m → Polynomial (Polynomial F))
    (hdeg : ∀ i j, ((E i).coeff j).natDegree ≤ Fintype.card F / m - f.natDegree)
    (hrel : BlockRelation (Fintype.card F) (f ^ ((Fintype.card F - 1) / m)) E) :
    ∀ i, E i = 0 := by
  have hf : f ≠ 0 := by intro h; simp [h] at hk
  exact ln97_6_46_of_degree_budget hm hmq f hf hirr
    (firstBlock_degree_budget (by omega) hk hkq) E hdeg hrel

/-- LN97 Lemma 6.46, including all degree ranges and the translation
case.  The degree hypothesis is the book's inequality with denominators
cleared for each nonzero coefficient. -/
theorem ln97_6_46
    {m : ℕ} (hm : 2 ≤ m) (hmq : m ∣ Fintype.card F - 1)
    (f : Polynomial F) (hk : 0 < f.natDegree)
    (hirr : KummerAbsolutelyIrreducible m f)
    (E : Fin m → Polynomial (Polynomial F))
    (hdeg : ∀ i j, (E i).coeff j ≠ 0 →
      m * (((E i).coeff j).natDegree + f.natDegree) ≤ Fintype.card F)
    (hrel : BlockRelation (Fintype.card F) (f ^ ((Fintype.card F - 1) / m)) E) :
    ∀ i, E i = 0 := by
  have hm0 : 0 < m := by omega
  by_cases hkq : f.natDegree ≤ Fintype.card F / m
  · apply ln97_6_46_of_natDegree_bound hm hmq f hk hkq hirr E _ hrel
    intro i j
    by_cases he : (E i).coeff j = 0
    · simp [he]
    · have hd := hdeg i j he
      have hd' : ((E i).coeff j).natDegree + f.natDegree ≤ Fintype.card F / m := by
        exact (Nat.le_div_iff_mul_le hm0).mpr (by simpa [Nat.mul_comm] using hd)
      omega
  · intro i
    apply Polynomial.ext
    intro j
    simp only [Polynomial.coeff_zero]
    by_contra he
    have hd := hdeg i j he
    have hd' : ((E i).coeff j).natDegree + f.natDegree ≤ Fintype.card F / m := by
      exact (Nat.le_div_iff_mul_le hm0).mpr (by simpa [Nat.mul_comm] using hd)
    omega

end LN97
end MagicSquares
