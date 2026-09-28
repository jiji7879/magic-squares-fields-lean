import MagicSquares.Characters.PowerIndicator
import MagicSquares.Characters.PowerExpansion
import MagicSquares.Weil.SharpMultiplicative

namespace MagicSquares

open scoped BigOperators Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Unnormalized power indicator for a family of shifted linear factors. -/
noncomputable def splitPowerWeight {r : ℕ} (n d : ℕ) (roots : Fin r → F) (t : F) : ℝ :=
  ∏ i, powerIndicatorNumerator n d (t - roots i)

private theorem split_power_minor_bound {r d : ℕ}
    (chi : MulChar F ℂ) (horder : orderOf chi = d)
    (roots : Fin r → F) (hinj : Function.Injective roots)
    (e : Fin r → Fin d)
    (hs : (powerExponentSupport e).Nonempty) :
    ‖∑ t : F, chi (∏ i, (t - roots i) ^ (e i : ℕ))‖ ≤
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
  let eqv := (Fintype.equivFin s).symm
  have h := LN97.sharp_power_multiplicative_weil (F := F)
    (Fintype.card s) (fun j => roots (eqv j)) (fun j => (e (eqv j) : ℕ))
    (by simpa only [Fintype.card_coe] using Finset.card_pos.mpr ⟨i, hi⟩)
    (fun j k hjk => eqv.injective (Subtype.ext (hinj hjk)))
    (fun j => Nat.pos_of_ne_zero ((mem_powerExponentSupport e (eqv j)).mp (eqv j).property))
    chi hchi ⟨eqv.symm ⟨i, hi⟩, by simpa using hnondvd⟩
  have hprod0 (t : F) :
      (∏ j : Fin (Fintype.card s), (t - roots (eqv j)) ^ (e (eqv j) : ℕ)) =
        ∏ j : s, (t - roots j) ^ (e j : ℕ) :=
    eqv.prod_comp (fun j : s => (t - roots j) ^ (e j : ℕ))
  simp_rw [hprod0] at h
  have hprod (t : F) : (∏ j : s, (t - roots j) ^ (e j : ℕ)) =
      ∏ j : Fin r, (t - roots j) ^ (e j : ℕ) := by
    rw [Finset.prod_coe_sort s (fun j : Fin r => (t - roots j) ^ (e j : ℕ))]
    apply Finset.prod_subset (Finset.subset_univ s)
    intro j _ hj
    have he : (e j : ℕ) = 0 := by
      simpa only [s, mem_powerExponentSupport, not_not] using hj
    simp [he]
  simpa only [hprod, Fintype.card_coe] using h

/-- Exact character expansion for an arbitrary finite family of roots. -/
theorem splitPowerWeight_sum_expand {r n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (chi : MulChar F ℂ) (horder : orderOf chi = d)
    (hdgcd : d = powerIndex n (Fintype.card F)) (roots : Fin r → F) :
    (∑ t : F, splitPowerWeight n d roots t) =
      ∑ e : Fin r → Fin d,
        (∑ t : F, chi (∏ i, (t - roots i) ^ (e i : ℕ))).re := by
  have hc : ((∑ t : F, splitPowerWeight n d roots t : ℝ) : ℂ) =
      ∑ e : Fin r → Fin d, ∑ t : F, chi (∏ i, (t - roots i) ^ (e i : ℕ)) := by
    rw [Complex.ofReal_sum, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    simp only [splitPowerWeight, Complex.ofReal_prod]
    simp_rw [← sum_character_powers_eq_indicator hn hd chi horder hdgcd]
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro e _
    simp only [map_prod, map_pow]
  have hr := congrArg Complex.re hc
  simpa only [Complex.ofReal_re, Complex.re_sum] using hr

/-- Sharp lower bound for simultaneous power conditions at distinct roots. -/
theorem splitPowerWeight_sum_lower {r n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (chi : MulChar F ℂ) (horder : orderOf chi = d)
    (hdgcd : d = powerIndex n (Fintype.card F))
    (roots : Fin r → F) (hinj : Function.Injective roots) :
    (Fintype.card F : ℝ) - ((r : ℝ) * (d : ℝ) ^ (r - 1) * ((d : ℝ) - 1) - (d : ℝ) ^ r + 1) * Real.sqrt (Fintype.card F : ℝ) ≤
      ∑ t : F, splitPowerWeight n d roots t := by
  let z : Fin r → Fin d := fun _ => ⟨0, hd⟩
  rw [splitPowerWeight_sum_expand hn hd chi horder hdgcd]
  have hminor (e : Fin r → Fin d) :
      (if e = z then (Fintype.card F : ℝ) else 0) -
        ((powerExponentSupport e).card - 1 : ℕ) * Real.sqrt (Fintype.card F : ℝ) ≤
      (∑ t : F, chi (∏ i, (t - roots i) ^ (e i : ℕ))).re := by
    by_cases he : e = z
    · subst e
      have hz : powerExponentSupport z = ∅ :=
        (powerExponentSupport_eq_empty_iff hd z).mpr rfl
      simp [hz, z]
    · have hs : (powerExponentSupport e).Nonempty := by
        apply Finset.nonempty_iff_ne_empty.mpr
        exact fun h => he ((powerExponentSupport_eq_empty_iff hd e).mp h)
      have hb := split_power_minor_bound chi horder roots hinj e hs
      have hr := (abs_le.mp (Complex.abs_re_le_norm
        (∑ t : F, chi (∏ i, (t - roots i) ^ (e i : ℕ))))).1
      simp only [if_neg he, zero_sub]
      linarith
  calc
    _ = ∑ e : Fin r → Fin d,
        ((if e = z then (Fintype.card F : ℝ) else 0) -
          ((powerExponentSupport e).card - 1 : ℕ) * Real.sqrt (Fintype.card F : ℝ)) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      have hcost := sum_powerExponentSupport_cost_general (r := r) hd
      push_cast at hcost
      rw [hcost]
      simp
    _ ≤ _ := Finset.sum_le_sum fun e _ => hminor e


end MagicSquares
