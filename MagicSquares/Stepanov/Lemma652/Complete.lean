import MagicSquares.Stepanov.Lemma646.Complete
import MagicSquares.Stepanov.Lemma652.DerivativeDataConstruct
import MagicSquares.Stepanov.Lemma652.ConcreteConstraints
import MagicSquares.Stepanov.Lemma652.VariableConstraints
import MagicSquares.Stepanov.Lemma652.BookArithmetic

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# Lidl--Niederreiter Lemma 6.52

The variable degree constraints supply a nonzero coefficient vector.
The completed Lemma 6.46 makes its auxiliary polynomial nonzero directly;
no quotient-independence hypothesis is required.  The derivative expansion
gives multiplicity at least `M` both at roots of `B(g)` and at roots of `f`.
Finally, the book's numerical hypotheses imply the dimension inequality
and the strict degree bound.
-/

/-- Auxiliary-polynomial existence with the exact equation count left
as a numerical hypothesis, but all algebraic inputs proved. -/
theorem ln97_6_52_of_equationCount
    {m r u D M : ℕ} (hm : 2 ≤ m) (hmq : m ∣ Fintype.card F - 1)
    (f B : Polynomial F) (hk : 0 < f.natDegree)
    (hirr : KummerAbsolutelyIrreducible m f)
    (hbudget : m * D + (m - 1) * f.natDegree < Fintype.card F)
    (hMcard : M ≤ Fintype.card F)
    (hB : B.Monic) (hr : 0 < r) (hBdeg : B.natDegree = r)
    (hcount : stepanovEquationCount r M D f.natDegree u <
      m * (u + 1) * (D + 1)) :
    ∃ h : Polynomial F, h ≠ 0 ∧
      (∀ c, B.IsRoot (eval c (f ^ ((Fintype.card F - 1) / m))) ∨ f.IsRoot c →
        M ≤ rootMultiplicity c h) ∧
      h.natDegree ≤ M * f.natDegree +
        (D + Fintype.card F * u +
          (m - 1) * (((Fintype.card F - 1) / m) * f.natDegree)) := by
  have hf : f ≠ 0 := by intro h; simp [h] at hk
  let s := (Fintype.card F - 1) / m
  let data := stepanovDerivativeDataOfPower
    (m := m) (u := u) (D := D) (M := M) (K := f.natDegree)
    f s hf hk le_rfl hMcard
  let S := stepanovSTNFamilyLinear (r := r) B data
  let N : Fin M → ℕ := fun n => D + (n : ℕ) * (f.natDegree - 1) + u
  let T := polynomialFamilyVariableConstraints N S
  have hcount' : r * ∑ n : Fin M, (N n + 1) < m * (u + 1) * (D + 1) := by
    change r * (∑ n : Fin M, (fun j : ℕ => D + j * (f.natDegree - 1) + u + 1) n) < _
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => D + j * (f.natDegree - 1) + u + 1) M]
    exact hcount
  obtain ⟨v, hvne, hvker⟩ := exists_nonzero_stepanovUnknown_in_variable_kernel T hcount'
  have hstn : ∀ t n, S v t n = 0 := by
    apply polynomialFamily_eq_zero_of_variableConstraints_eq_zero N S v _ hvker
    intro t n
    change (stepanovSTN
      (fun tt ii => powerReductionCoeff B (ii : ℕ) (tt : ℕ))
      (fun i j => stepanovBookDerivativeCoeffLinear f s hf hk n i j v) t).natDegree ≤
        D + (n : ℕ) * (f.natDegree - 1) + u
    exact stepanovSTN_natDegree_le (m := m) (r := r) (u := u) _ _
      (fun i j => stepanovBookDerivativeCoeff_natDegree_le f s hf hk v n i j) t
  let E := stepanovDecode v
  let h := stepanovAuxiliary (Fintype.card F) M f (f ^ s) E
  have hcoeff : ∀ i j, ((E i).coeff j).natDegree ≤ D :=
    stepanovDecode_coeff_natDegree_le v
  have hne : h ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero M hf)
    intro hzero
    have hall := ln97_6_46_of_degree_budget hm hmq f hf hirr hbudget E hcoeff hzero
    obtain ⟨i, hi⟩ := exists_stepanovDecode_ne_zero_of_ne_zero v hvne
    exact hi (hall i)
  refine ⟨h, hne, ?_, ?_⟩
  · intro c hc
    apply ln97_6_51_rootMultiplicity h c M hne
    intro n hn
    let nn : Fin M := ⟨n, hn⟩
    have hexp := data.expansion_eval v nn c
    change eval c ((hasseDeriv (nn : ℕ)) h) = 0
    rw [hexp]
    rcases hc with hc | hc
    · have hsum := eval_doubleSum_frobenius_eq_zero_of_stepanovSTN_eq_zero
        B hB hr hBdeg (fun i j => data.eDeriv v nn i j) (f ^ s) c hc
        (fun t => hstn t nn)
      rw [hsum, mul_zero]
    · have hpos : M - (nn : ℕ) ≠ 0 := by have := nn.isLt; omega
      simp only [Polynomial.IsRoot] at hc
      simp [hc, hpos]
  · exact stepanovAuxiliary_natDegree_le (Fintype.card F) M D u f.natDegree
      (s * f.natDegree) f (f ^ s) E (stepanovDecode_natDegree_le v) hcoeff
      le_rfl (by rw [Polynomial.natDegree_pow])

/-- LN97 Lemma 6.52 with its degree inequality multiplied by `m`.
The polynomial `B` is arbitrary of degree between `1` and `m-1`;
normalization to a monic polynomial is performed inside the proof. -/
theorem ln97_6_52_cleared
    {m M : ℕ} (hm : 2 ≤ m) (hmq : m ∣ Fintype.card F - 1)
    (f : Polynomial F) (hk : 0 < f.natDegree)
    (hirr : KummerAbsolutelyIrreducible m f)
    (B : Polynomial F) (hr : 0 < B.natDegree) (hrm : B.natDegree < m)
    (hM : f.natDegree + 1 ≤ M)
    (hshift : (M + 3) ^ 2 * m ≤ 2 * Fintype.card F) :
    ∃ h : Polynomial F, h ≠ 0 ∧
      (∀ c, B.IsRoot (eval c (f ^ ((Fintype.card F - 1) / m))) ∨ f.IsRoot c →
        M ≤ rootMultiplicity c h) ∧
      m * h.natDegree < B.natDegree * Fintype.card F * M +
        4 * f.natDegree * Fintype.card F * m := by
  have hm0 : 0 < m := by omega
  obtain ⟨hkq, hMcard⟩ := ln97_6_52_parameter_bounds hm0 hk hM hshift
  have hB0 : B ≠ 0 := by intro hz; simp [hz] at hr
  let B' := B * C B.leadingCoeff⁻¹
  have hB' : B'.Monic := Polynomial.monic_mul_leadingCoeff_inv hB0
  have hBdeg : B'.natDegree = B.natDegree :=
    Polynomial.natDegree_mul_C (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hB0))
  obtain ⟨h, hh, hmult, hdeg⟩ := ln97_6_52_of_equationCount
    (u := stepanovU B.natDegree m M f.natDegree)
    (D := Fintype.card F / m - f.natDegree)
    hm hmq f B' hk hirr (firstBlock_degree_budget hm0 hk hkq)
    hMcard hB' hr hBdeg
    (ln97_6_52_equationCount_lt_unknowns hm0 hr hrm hk hM hshift)
  refine ⟨h, hh, ?_, ?_⟩
  · intro c hc
    apply hmult c
    rcases hc with hc | hc
    · left
      change eval (eval c (f ^ ((Fintype.card F - 1) / m)))
        (B * C B.leadingCoeff⁻¹) = 0
      rw [Polynomial.eval_mul, hc, zero_mul]
    · exact Or.inr hc
  · exact (Nat.mul_le_mul_left m hdeg).trans_lt
      (ln97_6_52_auxiliary_degree_bound (Fintype.card_pos) hm0 hrm hk hMcard)

/-- **Lidl--Niederreiter Lemma 6.52.**  From precisely the book's
absolute-irreducibility, degree, and numerical hypotheses, construct a
nonzero polynomial with multiplicity at least `M` at every point of `T`
and degree strictly below `(r/m) q M + 4 k q`.

The shifted-square hypothesis is written with its positive denominator
cleared; the final degree bound uses rational division. -/
theorem ln97_6_52
    {m M : ℕ} (hm : 2 ≤ m) (hmq : m ∣ Fintype.card F - 1)
    (f : Polynomial F) (hk : 0 < f.natDegree)
    (hirr : KummerAbsolutelyIrreducible m f)
    (B : Polynomial F) (hr : 0 < B.natDegree) (hrm : B.natDegree < m)
    (hM : f.natDegree + 1 ≤ M)
    (hshift : (M + 3) ^ 2 * m ≤ 2 * Fintype.card F) :
    ∃ h : Polynomial F, h ≠ 0 ∧
      (∀ c, B.IsRoot (eval c (f ^ ((Fintype.card F - 1) / m))) ∨ f.IsRoot c →
        M ≤ rootMultiplicity c h) ∧
      (h.natDegree : ℚ) < (B.natDegree : ℚ) / m * Fintype.card F * M +
        4 * f.natDegree * Fintype.card F := by
  obtain ⟨h, hh, hmult, hdeg⟩ := ln97_6_52_cleared hm hmq f hk hirr B hr hrm hM hshift
  refine ⟨h, hh, hmult, ?_⟩
  have hmQ : (0 : ℚ) < m := by exact_mod_cast (show 0 < m by omega)
  apply (mul_lt_mul_iff_right₀ hmQ).mp
  have heq : (m : ℚ) * ((B.natDegree : ℚ) / m * Fintype.card F * M +
      4 * f.natDegree * Fintype.card F) =
      B.natDegree * Fintype.card F * M + 4 * f.natDegree * Fintype.card F * m := by
    field_simp
  rw [heq]
  exact_mod_cast hdeg

end LN97
end MagicSquares
