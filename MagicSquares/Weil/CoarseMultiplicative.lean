import MagicSquares.Weil.CharacterFibers

namespace MagicSquares.LN97

open scoped BigOperators Classical
open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Stepánov's point-count bound controls every nontrivial character
whose order divides the absolutely irreducible Kummer exponent. -/
theorem coarse_multiplicative_bound
    {m : ℕ} (hm : 2 ≤ m) (hmq : m ∣ Fintype.card F - 1)
    (chi : MulChar F ℂ) (hchi : chi ≠ 1) (hpow : chi ^ m = 1)
    (f : Polynomial F) (hk : 0 < f.natDegree)
    (hirr : KummerAbsolutelyIrreducible m f)
    (hq : 100 * m * f.natDegree ^ 2 ≤ Fintype.card F) :
    ‖∑ x : F, chi (f.eval x)‖ ≤
      8 * f.natDegree * (m : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Fintype.card F) := by
  let B : ℝ := 4 * f.natDegree * (m : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Fintype.card F)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hterm (a : F) :
      ‖chi a * ((stepanovSolutionCount m (C a⁻¹ * f) : ℂ) - Fintype.card F)‖ ≤ B := by
    by_cases ha : a = 0
    · simpa only [ha, MulChar.map_zero, zero_mul, norm_zero] using hB
    · have hdeg : (C a⁻¹ * f).natDegree = f.natDegree := natDegree_C_mul (inv_ne_zero ha)
      have ht := ln97_6_53 hm hmq (C a⁻¹ * f) (by rwa [hdeg])
        (hirr.const_mul (by omega) (inv_ne_zero ha)) (by rwa [hdeg])
      rw [hdeg] at ht
      have hnorm : ‖(stepanovSolutionCount m (C a⁻¹ * f) : ℂ) - Fintype.card F‖ ≤ B := by
        simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs, B] using ht.le
      rw [norm_mul]
      calc
        _ ≤ 1 * ‖(stepanovSolutionCount m (C a⁻¹ * f) : ℂ) - Fintype.card F‖ :=
          mul_le_mul_of_nonneg_right (mulChar_norm_le_one chi a) (norm_nonneg _)
        _ ≤ B := by simpa using hnorm
  have hq2 : (2 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.one_lt_card (α := F)
  have hqnorm : ‖(Fintype.card F : ℂ) - 1‖ = (Fintype.card F : ℝ) - 1 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have htotal : ((Fintype.card F : ℝ) - 1) * ‖∑ x : F, chi (f.eval x)‖ ≤
      (Fintype.card F : ℝ) * B := by
    calc
      _ = ‖((Fintype.card F : ℂ) - 1) * ∑ x : F, chi (f.eval x)‖ := by rw [norm_mul, hqnorm]
      _ = _ := congrArg norm (character_sum_eq_weighted_twist_counts (by omega) chi hchi hpow f)
      _ ≤ ∑ a : F, ‖chi a * ((stepanovSolutionCount m (C a⁻¹ * f) : ℂ) - Fintype.card F)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _a : F, B := Finset.sum_le_sum fun a _ => hterm a
      _ = _ := by simp
  have htwo : ‖∑ x : F, chi (f.eval x)‖ ≤ 2 * B := by
    have hbq : (Fintype.card F : ℝ) * B ≤ 2 * ((Fintype.card F : ℝ) - 1) * B := by nlinarith
    have he := htotal.trans hbq
    exact (mul_le_mul_iff_right₀ (by linarith : 0 < (Fintype.card F : ℝ) - 1)).mp
      (by nlinarith [he])
  simpa only [B] using htwo.trans_eq (by ring)

/-- A uniform coarse estimate valid also for small fields. Its constant
is independent of the field cardinality, which is what Lemma 6.55 needs. -/
theorem multiplicative_sum_uniform_coarse
    {m : ℕ} (hm : 2 ≤ m) (hmq : m ∣ Fintype.card F - 1)
    (chi : MulChar F ℂ) (hchi : chi ≠ 1) (hpow : chi ^ m = 1)
    (f : Polynomial F) (hk : 0 < f.natDegree) (hirr : KummerAbsolutelyIrreducible m f) :
    ‖∑ x : F, chi (f.eval x)‖ ≤
      (100 * m * (f.natDegree : ℝ) ^ 2 + 8 * f.natDegree * (m : ℝ) ^ (3 / 2 : ℝ)) *
        Real.sqrt (Fintype.card F) := by
  have hC : 0 ≤ 100 * (m : ℝ) * (f.natDegree : ℝ) ^ 2 +
      8 * f.natDegree * (m : ℝ) ^ (3 / 2 : ℝ) := by positivity
  by_cases hq : 100 * m * f.natDegree ^ 2 ≤ Fintype.card F
  · calc
      _ ≤ 8 * f.natDegree * (m : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Fintype.card F) :=
        coarse_multiplicative_bound hm hmq chi hchi hpow f hk hirr hq
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (by positivity)) (Real.sqrt_nonneg _)
  · have htriv : ‖∑ x : F, chi (f.eval x)‖ ≤ (Fintype.card F : ℝ) := by
      calc
        _ ≤ ∑ x : F, ‖chi (f.eval x)‖ := norm_sum_le _ _
        _ ≤ ∑ _x : F, (1 : ℝ) := Finset.sum_le_sum fun x _ => mulChar_norm_le_one chi _
        _ = _ := by simp
    have hsmall : (Fintype.card F : ℝ) ≤ 100 * m * (f.natDegree : ℝ) ^ 2 := by
      exact_mod_cast (not_le.mp hq).le
    have hsqrt : 1 ≤ Real.sqrt (Fintype.card F : ℝ) :=
      Real.one_le_sqrt.mpr (by exact_mod_cast Fintype.card_pos (α := F))
    calc
      _ ≤ 100 * m * (f.natDegree : ℝ) ^ 2 := htriv.trans hsmall
      _ ≤ 100 * m * (f.natDegree : ℝ) ^ 2 + 8 * f.natDegree * (m : ℝ) ^ (3 / 2 : ℝ) := le_add_of_nonneg_right (by positivity)
      _ ≤ _ := le_mul_of_one_le_right hC hsqrt

end MagicSquares.LN97
