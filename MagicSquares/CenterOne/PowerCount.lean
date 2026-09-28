import MagicSquares.Characters.PowerIndicator
import MagicSquares.Characters.PowerExpansion
import MagicSquares.Weil.AffineMultiplicative
import MagicSquares.CenterOne.SquareCount

namespace MagicSquares

open scoped BigOperators Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The unnormalized Section 14 indicator for eight affine power conditions. -/
noncomputable def affinePowerWeight (n d : ℕ) (coeff : Fin 8 → F) (t : F) : ℝ :=
  ∏ i, powerIndicatorNumerator n d (1 + coeff i * t)

private theorem affine_power_minor_bound {d : ℕ}
    (chi : MulChar F ℂ) (horder : orderOf chi = d)
    (coeff : Fin 8 → F) (hinj : Function.Injective coeff)
    (hnonzero : ∀ i, coeff i ≠ 0) (e : Fin 8 → Fin d)
    (hs : (powerExponentSupport e).Nonempty) :
    ‖∑ t : F, chi (∏ i, (1 + coeff i * t) ^ (e i : ℕ))‖ ≤
      ((powerExponentSupport e).card - 1 : ℕ) * Real.sqrt (Fintype.card F : ℝ) := by
  let s := powerExponentSupport e
  obtain ⟨i, hi⟩ := hs
  have hipos : 0 < (e i : ℕ) :=
    Nat.pos_of_ne_zero ((mem_powerExponentSupport e i).mp hi)
  have hnondvd : ¬ orderOf chi ∣ (e i : ℕ) := by
    rw [horder]
    exact Nat.not_dvd_of_pos_of_lt hipos (e i).isLt
  have hchi : chi ≠ 1 := by
    intro heq
    apply hnondvd
    simp [heq]
  have h := (LN97.sharp_power_multiplicative_weil (F := F)).affine
    (fun j : s => coeff j) (fun j : s => (e j : ℕ))
    (by simpa only [Fintype.card_coe] using Finset.card_pos.mpr ⟨i, hi⟩)
    (fun j k hjk => Subtype.ext (hinj hjk)) (fun j => hnonzero j)
    (fun j => Nat.pos_of_ne_zero ((mem_powerExponentSupport e j).mp j.property))
    chi hchi ⟨⟨i, hi⟩, hnondvd⟩
  have hprod (t : F) : (∏ j : s, (1 + coeff j * t) ^ (e j : ℕ)) =
      ∏ j : Fin 8, (1 + coeff j * t) ^ (e j : ℕ) := by
    rw [Finset.prod_coe_sort s (fun j : Fin 8 => (1 + coeff j * t) ^ (e j : ℕ))]
    apply Finset.prod_subset (Finset.subset_univ s)
    intro j _ hj
    have he : (e j : ℕ) = 0 := by
      simpa only [s, mem_powerExponentSupport, not_not] using hj
    simp [he]
  simpa only [hprod, Fintype.card_coe] using h

/-- Exact expansion into the `d^8` character sums. -/
theorem affinePowerWeight_sum_expand {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (chi : MulChar F ℂ) (horder : orderOf chi = d)
    (hdgcd : d = powerIndex n (Fintype.card F)) (coeff : Fin 8 → F) :
    (∑ t : F, affinePowerWeight n d coeff t) =
      ∑ e : Fin 8 → Fin d,
        (∑ t : F, chi (∏ i, (1 + coeff i * t) ^ (e i : ℕ))).re := by
  have hc : ((∑ t : F, affinePowerWeight n d coeff t : ℝ) : ℂ) =
      ∑ e : Fin 8 → Fin d, ∑ t : F, chi (∏ i, (1 + coeff i * t) ^ (e i : ℕ)) := by
    rw [Complex.ofReal_sum, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    simp only [affinePowerWeight, Complex.ofReal_prod]
    simp_rw [← sum_character_powers_eq_indicator hn hd chi horder hdgcd]
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro e _
    simp only [map_prod, map_pow]
  have hr := congrArg Complex.re hc
  simpa only [Complex.ofReal_re, Complex.re_sum] using hr

/-- **Section 14 weighted count.** The complete character expansion has
error constant `C₁(d) = d^7(7d-8)+1`. -/
theorem affinePowerWeight_sum_lower {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (chi : MulChar F ℂ) (horder : orderOf chi = d)
    (hdgcd : d = powerIndex n (Fintype.card F))
    (coeff : Fin 8 → F) (hinj : Function.Injective coeff)
    (hnonzero : ∀ i, coeff i ≠ 0) :
    (Fintype.card F : ℝ) - centerOneC1 d * Real.sqrt (Fintype.card F : ℝ) ≤
      ∑ t : F, affinePowerWeight n d coeff t := by
  let z : Fin 8 → Fin d := fun _ => ⟨0, hd⟩
  rw [affinePowerWeight_sum_expand hn hd chi horder hdgcd]
  have hminor (e : Fin 8 → Fin d) :
      (if e = z then (Fintype.card F : ℝ) else 0) -
        ((powerExponentSupport e).card - 1 : ℕ) * Real.sqrt (Fintype.card F : ℝ) ≤
      (∑ t : F, chi (∏ i, (1 + coeff i * t) ^ (e i : ℕ))).re := by
    by_cases he : e = z
    · subst e
      have hz : powerExponentSupport z = ∅ :=
        (powerExponentSupport_eq_empty_iff hd z).mpr rfl
      simp [hz, z]
    · have hs : (powerExponentSupport e).Nonempty := by
        apply Finset.nonempty_iff_ne_empty.mpr
        exact fun h => he ((powerExponentSupport_eq_empty_iff hd e).mp h)
      have hb := affine_power_minor_bound chi horder coeff hinj hnonzero e hs
      have hr := (abs_le.mp (Complex.abs_re_le_norm
        (∑ t : F, chi (∏ i, (1 + coeff i * t) ^ (e i : ℕ))))).1
      simp only [if_neg he, zero_sub]
      linarith
  calc
    _ = ∑ e : Fin 8 → Fin d,
        ((if e = z then (Fintype.card F : ℝ) else 0) -
          ((powerExponentSupport e).card - 1 : ℕ) * Real.sqrt (Fintype.card F : ℝ)) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      have hcost := sum_powerExponentSupport_cost hd
      push_cast at hcost
      rw [hcost]
      simp
    _ ≤ _ := Finset.sum_le_sum fun e _ => hminor e

omit [Fintype F] in
/-- The weighted indicator is dominated by the exact power indicator,
including all parameters where an entry vanishes. -/
theorem affinePowerWeight_le_indicator {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (coeff : Fin 8 → F) (t : F) :
    affinePowerWeight n d coeff t ≤
      if ∀ i, IsNthPower n (1 + coeff i * t) then (d : ℝ) ^ 8 else 0 := by
  by_cases h : ∀ i, IsNthPower n (1 + coeff i * t)
  · rw [if_pos h]
    calc
      _ ≤ ∏ _i : Fin 8, (d : ℝ) := by
        apply Finset.prod_le_prod
        · intro i _
          exact powerIndicatorNumerator_nonneg _ _ _
        · intro i _
          exact powerIndicatorNumerator_le hd _
      _ = _ := by simp
  · rw [if_neg h]
    push Not at h
    obtain ⟨i, hi⟩ := h
    have hz : affinePowerWeight n d coeff t = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact powerIndicatorNumerator_eq_zero_of_not_power hn hi
    exact hz.le

namespace Square3

omit [DecidableEq F] in
theorem noncenter_powers_iff_mem (n : ℕ) (b t : F) :
    (∀ i, IsNthPower n (1 + centerOneNoncenterCoeff b i * t)) ↔
      t ∈ centerOnePowerParameters n b := by
  rw [mem_centerOnePowerParameters]
  constructor
  · intro h k
    by_cases hk : k = 4
    · subst k
      refine ⟨1, ?_⟩
      simp [centerOneCoeff]
    · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hk
      exact h i
  · intro h i
    exact h ((4 : Fin 9).succAbove i)

/-- The complete Section 14 estimate, with no unproved analytic hypothesis. -/
theorem hasCenterOnePowerCountBound {n : ℕ} (hn : 0 < n) :
    HasCenterOnePowerCountBound F n (powerIndex n (Fintype.card F)) := by
  let d := powerIndex n (Fintype.card F)
  have hd : 0 < d := powerIndex_pos hn
  obtain ⟨chi, horder⟩ := MulChar.exists_mulChar_orderOf F
    (Nat.gcd_dvd_right n (Fintype.card F - 1)) (Complex.isPrimitiveRoot_exp d hd.ne')
  intro b hb
  have hinj : Function.Injective (centerOneNoncenterCoeff b) :=
    hb.comp Fin.succAbove_right_injective
  have hnz (i : Fin 8) : centerOneNoncenterCoeff b i ≠ 0 :=
    centerOneCoeff_ne_zero_of_good hb (Fin.succAbove_ne _ _)
  calc
    _ ≤ ∑ t : F, affinePowerWeight n d (centerOneNoncenterCoeff b) t :=
      affinePowerWeight_sum_lower hn hd chi horder rfl _ hinj hnz
    _ ≤ ∑ t : F, if t ∈ centerOnePowerParameters n b then (d : ℝ) ^ 8 else 0 := by
      apply Finset.sum_le_sum
      intro t _
      simpa only [noncenter_powers_iff_mem] using
        affinePowerWeight_le_indicator hn hd (centerOneNoncenterCoeff b) t
    _ = _ := by
      rw [Finset.sum_ite_mem]
      simp [mul_comm, d]

end Square3
end MagicSquares

/-!
## General-power existence (paper, Theorem 14.1)

The counting estimate above now supplies the existence criterion.
-/

namespace MagicSquares.Square3

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Theorem 14.1.** The center-one construction for general powers,
with the character-sum and counting inputs fully proved. -/
theorem exists_centerOne_magic_of_powers_of_bound {n : ℕ} (hn : 0 < n)
    (hodd : ringChar F ≠ 2) (hq : 7 < Fintype.card F)
    (hmain :
      9 * (powerIndex n (Fintype.card F) : ℝ) ^ 8 <
        (Fintype.card F : ℝ) -
          centerOneC1 (powerIndex n (Fintype.card F)) *
            Real.sqrt (Fintype.card F : ℝ)) :
    ∃ M : Square3 F, IsMagicOfPowers n M :=
  exists_centerOne_magic_of_powers n (powerIndex n (Fintype.card F))
    (powerIndex_pos hn) hodd hq (hasCenterOnePowerCountBound hn) hmain

/-- Theorem 14.1 in `n`-Parker terminology. -/
theorem not_isNParker_of_power_bound {n : ℕ} (hn : 0 < n)
    (hodd : ringChar F ≠ 2) (hq : 7 < Fintype.card F)
    (hmain :
      9 * (powerIndex n (Fintype.card F) : ℝ) ^ 8 <
        (Fintype.card F : ℝ) -
          centerOneC1 (powerIndex n (Fintype.card F)) *
            Real.sqrt (Fintype.card F : ℝ)) :
    ¬ IsNParker F n := by
  intro hP
  exact hP (exists_centerOne_magic_of_powers_of_bound hn hodd hq hmain)

end MagicSquares.Square3
