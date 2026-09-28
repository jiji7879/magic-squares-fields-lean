import MagicSquares.Weil.LFunction.Representation
import MagicSquares.Weil.CoarseMultiplicative
import MagicSquares.Weil.ExponentReduction
import MagicSquares.Weil.PowerSum
import MagicSquares.Weil.SharpInterface

/-!
# The sharp split multiplicative-character bound from LN97

The proof follows the roles of LN97 Theorems 5.39, 6.56, and 5.41:
1. Represent extension-field sums by powers of finitely many reciprocal roots.
2. Apply the coarse Stepanov bound uniformly over finite extensions.
3. Use Lemma 6.55 to bound each reciprocal root by sqrt(q).
4. Sum those bounds; the L-polynomial has degree at most r - 1.

The primitive-exponent theorem carries out this argument. Exponent reduction
then handles the general repeated-root case, and squarefree specialization
provides the simpler interface. No sharp bound is assumed as an extra axiom.
-/

namespace MagicSquares.LN97

open scoped BigOperators Classical
open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem sqrt_nat_pow (q s : ℕ) :
    Real.sqrt ((q : ℝ) ^ s) = Real.sqrt (q : ℝ) ^ s := by
  induction s with
  | zero => simp
  | succ s ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

omit [DecidableEq F] in
/-- Sharp Weil bound for split polynomials whose multiplicities have no
common prime divisor with the character order. -/
theorem sharp_split_bound_of_primitive_exponents
    {r : ℕ} (roots : Fin r → F) (hr : 0 < r) (hinj : Function.Injective roots)
    (chi : MulChar F ℂ) (hm : 2 ≤ orderOf chi) (exponents : Fin r → ℕ)
    (hpos : ∀ i, 0 < exponents i)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ orderOf chi → ∃ i, ¬ p ∣ exponents i) :
    ‖∑ x : F, chi (∏ i, (x - roots i) ^ exponents i)‖ ≤
      (r - 1 : ℕ) * Real.sqrt (Fintype.card F : ℝ) := by
  let chars : Fin r → MulChar F ℂ := fun i => chi ^ exponents i
  have hchars : ∃ i, chars i ≠ 1 := by
    obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (by omega : orderOf chi ≠ 1)
    obtain ⟨i, hi⟩ := hprime p hp hpm
    refine ⟨i, fun he => hi (hpm.trans ?_)⟩
    exact orderOf_dvd_of_pow_eq_one he
  have hchi : chi ≠ 1 := by intro h; simp [h] at hm
  -- LN97 5.39: the reciprocal-root representation has at most r - 1 terms.
  obtain ⟨d, alpha, hd, htrace⟩ :=
    splitLTrace_exists_powerSum_representation roots hinj chars hchars
  let k := ∑ i, exponents i
  have hk : 0 < k := by
    have hle : exponents ⟨0, hr⟩ ≤ k :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (exponents i)) (Finset.mem_univ _)
    exact (hpos ⟨0, hr⟩).trans_le hle
  let B := Real.sqrt (Fintype.card F : ℝ)
  let A : ℝ := 100 * orderOf chi * (k : ℝ) ^ 2 + 8 * k * (orderOf chi : ℝ) ^ (3 / 2 : ℝ)
  have hB : 0 < B := Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos (α := F))
  -- LN97 6.56: one constant A works over every degree-s extension.
  have hbound (s : ℕ) (hs : 0 < s) : ‖∑ i, alpha i ^ s‖ ≤ A * B ^ s := by
    letI : NeZero s := ⟨hs.ne'⟩
    obtain ⟨p, hp⟩ := CharP.exists F
    letI : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
    let E := FiniteField.Extension F p s
    letI : Fintype E := Fintype.ofFinite E
    letI : DecidableEq E := Classical.decEq E
    let eroots : Fin r → E := fun i => algebraMap F E (roots i)
    let ech := normLift (E := E) chi
    let f : Polynomial E := ∏ i, (X - C (eroots i)) ^ exponents i
    have hei : Function.Injective eroots := (algebraMap F E).injective.comp hinj
    have horder : orderOf ech = orderOf chi := normLift_orderOf chi
    have hdegree : f.natDegree = k := by
      dsimp [f, k]
      rw [natDegree_prod_of_monic _ _ (fun i _ => (monic_X_sub_C _).pow _)]
      simp only [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
    -- The primitive multiplicities justify the Kummer irreducibility hypothesis.
    have hirr : KummerAbsolutelyIrreducible (orderOf chi) f :=
      kummerAbsolutelyIrreducible_prod_distinct_linear_powers chi.orderOf_pos eroots hei exponents hprime
    have hmq : orderOf chi ∣ Fintype.card E - 1 := horder ▸ ech.orderOf_dvd_card_sub_one
    have hpow : ech ^ orderOf chi = 1 := by rw [← horder]; exact pow_orderOf_eq_one ech
    have hsum : splitExtensionSum (E := E) roots chars = -(∑ i, alpha i ^ s) := by
      rw [← splitLTrace_eq_extensionSum roots hinj chars hchars,
        show Module.finrank F E = s from FiniteField.finrank_extension F p s]
      exact htrace s hs
    have heval : splitExtensionSum (E := E) roots chars = ∑ x : E, ech (f.eval x) := by
      unfold splitExtensionSum
      apply Finset.sum_congr rfl
      intro x _
      simp only [chars, normLift_pow, f, eval_prod, eval_pow, eval_sub, eval_X, eval_C, map_prod]
      apply Finset.prod_congr rfl
      intro i _
      rw [MulChar.pow_apply' _ (hpos i).ne', map_pow]
    have hcard : Fintype.card E = Fintype.card F ^ s := by
      simpa only [Fintype.card_eq_nat_card] using FiniteField.natCard_extension F p s
    calc
      _ = ‖splitExtensionSum (E := E) roots chars‖ := by rw [hsum, norm_neg]
      _ ≤ A * Real.sqrt (Fintype.card E : ℝ) := by
        rw [heval]
        have h := multiplicative_sum_uniform_coarse hm hmq ech (normLift_ne_one hchi)
          hpow f (by rwa [hdegree]) hirr
        simpa only [hdegree, A] using h
      _ = _ := by rw [hcard, Nat.cast_pow, sqrt_nat_pow]
  -- Return to extension degree one to recover the original character sum.
  have hfirst : (∑ x : F, chi (∏ i, (x - roots i) ^ exponents i)) = -(∑ i, alpha i) := by
    have h := htrace 1 (by norm_num)
    rw [splitLTrace_one roots hinj chars hchars] at h
    have heval (x : F) : (∏ i, chars i (x - roots i)) =
        chi (∏ i, (x - roots i) ^ exponents i) := by
      rw [map_prod]
      apply Finset.prod_congr rfl
      intro i _
      dsimp only [chars]
      rw [chi.pow_apply' (hpos i).ne', map_pow]
    simpa only [heval, pow_one] using h
  -- Lemma 6.55 bounds each reciprocal root; the triangle inequality finishes.
  rw [hfirst, norm_neg]
  calc
    ‖∑ i, alpha i‖ ≤ ∑ i, ‖alpha i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, B := Finset.sum_le_sum fun i _ => ln97_6_55 alpha hB hbound i
    _ = (d : ℝ) * B := by simp
    _ ≤ (r - 1 : ℕ) * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hd) hB.le

/-- The exponent-sensitive sharp multiplicative Weil bound, with every
analytic and irreducibility input discharged. -/
theorem sharp_power_multiplicative_weil : HasSplitPowerMultiplicativeWeilBound F := by
  intro r roots exponents hr hinj hpos chi _ hnon
  obtain ⟨tau, reduced, hm, hredpos, hprime, heval⟩ :=
    exists_primitive_exponent_reduction chi exponents hpos hnon
  simp_rw [heval]
  exact sharp_split_bound_of_primitive_exponents roots hr hinj tau hm reduced hredpos hprime

/-- The squarefree specialization for any nontrivial character. -/
theorem sharp_multiplicative_weil : HasSplitMultiplicativeWeilBound F :=
  (sharp_power_multiplicative_weil (F := F)).squarefree

end MagicSquares.LN97
