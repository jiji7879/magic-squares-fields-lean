import MagicSquares.Weil.LFunction.Representation
import MagicSquares.Weil.CoarseQuadratic
import MagicSquares.Weil.PowerSum

namespace MagicSquares.LN97

open scoped BigOperators Classical
open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A degree-dependent coarse constant valid over every odd finite field.
For small fields the elementary bound suffices; for large fields this is
the proved Stepánov bound. The uniform constant is used only to bound the
reciprocal roots, and disappears from the final sharp estimate. -/
theorem quadratic_split_sum_uniform_coarse
    (hodd : ringChar F ≠ 2) {r : ℕ} (roots : Fin r → F) (hr : 0 < r)
    (hinj : Function.Injective roots) :
    ‖∑ x : F, ((quadraticChar F (∏ i, (x - roots i)) : ℤ) : ℂ)‖ ≤
      (200 * (r : ℝ) ^ 2 + 12 * r) * Real.sqrt (Fintype.card F : ℝ) := by
  have hC : 0 ≤ 200 * (r : ℝ) ^ 2 + 12 * r := by positivity
  by_cases hq : 200 * r ^ 2 ≤ Fintype.card F
  · let f : Polynomial F := ∏ i, (X - C (roots i))
    have hdegree : f.natDegree = r := by
      dsimp [f]
      rw [natDegree_prod_of_monic]
      · simp
      · intro i _
        exact monic_X_sub_C _
    have ha : f.rootMultiplicity (roots ⟨0, hr⟩) = 1 :=
      rootMultiplicity_prod_distinct_linear Finset.univ roots
        (fun _ _ _ _ h => hinj h) (Finset.mem_univ _)
    have h := coarse_quadratic_bound_of_simple_root hodd f ha (by simpa [hdegree] using hq)
    have heval (x : F) : f.eval x = ∏ i, (x - roots i) := by simp [f, eval_prod]
    simp only [heval, hdegree] at h
    rw [← Int.cast_sum, Complex.norm_intCast]
    have htwo : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 3 := by
      rw [← mul_sqrt_eq_rpow_three_halves 2 (by norm_num)]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
    calc
      _ ≤ 4 * r * (2 : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Fintype.card F) := h.le
      _ ≤ 4 * r * 3 * Real.sqrt (Fintype.card F) := by gcongr
      _ ≤ _ := by nlinarith [Real.sqrt_nonneg (Fintype.card F : ℝ), sq_nonneg (r : ℝ)]
  · have htriv : ‖∑ x : F, ((quadraticChar F (∏ i, (x - roots i)) : ℤ) : ℂ)‖ ≤
        (Fintype.card F : ℝ) := by
      calc
        _ ≤ ∑ x : F, ‖((quadraticChar F (∏ i, (x - roots i)) : ℤ) : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ _x : F, (1 : ℝ) := Finset.sum_le_sum fun x _ => by
          rw [Complex.norm_intCast]
          exact quadraticChar_abs_le_one _
        _ = _ := by simp
    have hsmall : (Fintype.card F : ℝ) ≤ 200 * (r : ℝ) ^ 2 := by exact_mod_cast (not_le.mp hq).le
    have hsqrt : 1 ≤ Real.sqrt (Fintype.card F : ℝ) :=
      Real.one_le_sqrt.mpr (by exact_mod_cast Fintype.card_pos (α := F))
    calc
      _ ≤ (Fintype.card F : ℝ) := htriv
      _ ≤ 200 * (r : ℝ) ^ 2 + 12 * r := by nlinarith
      _ ≤ _ := le_mul_of_one_le_right hC hsqrt

private theorem sqrt_nat_pow (q s : ℕ) :
    Real.sqrt ((q : ℝ) ^ s) = Real.sqrt (q : ℝ) ^ s := by
  induction s with
  | zero => simp
  | succ s ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

/-- The sharp quadratic Weil bound, obtained from the actual extension
representation, the proved Stepánov bound, and LN97 Lemma 6.55. -/
theorem sharp_quadratic_weil (hodd : ringChar F ≠ 2) : HasSplitQuadraticWeilBound F := by
  intro r roots hr hinj
  let chars : Fin r → MulChar F ℂ := fun _ => quadraticCharC F
  have hchars : ∃ j, chars j ≠ 1 := ⟨⟨0, hr⟩, quadraticCharC_ne_one hodd⟩
  obtain ⟨d, alpha, hd, htrace⟩ :=
    splitLTrace_exists_powerSum_representation roots hinj chars hchars
  let B := Real.sqrt (Fintype.card F : ℝ)
  have hB : 0 < B := Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos (α := F))
  have hbound (s : ℕ) (hs : 0 < s) :
      ‖∑ i, alpha i ^ s‖ ≤ (200 * (r : ℝ) ^ 2 + 12 * r) * B ^ s := by
    letI : NeZero s := ⟨Nat.ne_of_gt hs⟩
    obtain ⟨p, hp⟩ := CharP.exists F
    letI : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
    let E := FiniteField.Extension F p s
    letI : Fintype E := Fintype.ofFinite E
    letI : DecidableEq E := Classical.decEq E
    have hoddE : ringChar E ≠ 2 := by rwa [← Algebra.ringChar_eq F E]
    let eroots : Fin r → E := fun i => algebraMap F E (roots i)
    have hei : Function.Injective eroots := (algebraMap F E).injective.comp hinj
    have hsum : splitExtensionSum (E := E) roots chars = -(∑ i, alpha i ^ s) := by
      rw [← splitLTrace_eq_extensionSum roots hinj chars hchars,
        show Module.finrank F E = s from FiniteField.finrank_extension F p s]
      exact htrace s hs
    have heval : splitExtensionSum (E := E) roots chars =
        ∑ x : E, ((quadraticChar E (∏ i, (x - eroots i)) : ℤ) : ℂ) := by
      simp only [splitExtensionSum, chars, normLift_quadraticCharC hodd,
        quadraticCharC_apply, map_prod, Int.cast_prod, eroots]
    have hcard : Fintype.card E = Fintype.card F ^ s := by
      simpa only [Fintype.card_eq_nat_card] using FiniteField.natCard_extension F p s
    calc
      _ = ‖splitExtensionSum (E := E) roots chars‖ := by rw [hsum, norm_neg]
      _ ≤ (200 * (r : ℝ) ^ 2 + 12 * r) * Real.sqrt (Fintype.card E : ℝ) := by
        rw [heval]
        exact quadratic_split_sum_uniform_coarse hoddE eroots hr hei
      _ = _ := by rw [hcard, Nat.cast_pow, sqrt_nat_pow]
  have hfirst : (∑ x : F, ((quadraticChar F (∏ i, (x - roots i)) : ℤ) : ℂ)) =
      -(∑ i, alpha i) := by
    have h := htrace 1 (by norm_num)
    rw [splitLTrace_one roots hinj chars hchars] at h
    simpa only [chars, quadraticCharC_apply, map_prod, Int.cast_prod, pow_one] using h
  rw [hfirst, norm_neg]
  calc
    ‖∑ i, alpha i‖ ≤ ∑ i, ‖alpha i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, B := Finset.sum_le_sum fun i _ => ln97_6_55 alpha hB hbound i
    _ = (d : ℝ) * B := by simp
    _ ≤ (r - 1 : ℕ) * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hd) hB.le

end MagicSquares.LN97
