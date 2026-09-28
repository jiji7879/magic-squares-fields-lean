import MagicSquares.Stepanov.Lemma652.Complete
import MagicSquares.Stepanov.Lemma653.MultiplicityChoice
import MagicSquares.Stepanov.Lemma653.TSet
import MagicSquares.Stepanov.Lemma645.Complete

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# The concrete set estimate (6.28)

The set in Lemma 6.52 includes both the zeros of `f` and the points where
`B(g(c))=0`.  Applying the completed auxiliary-polynomial theorem to this
union, with the chosen integer multiplicity, gives (6.28).
-/

/-- The complete set `T` from Lemma 6.52, including the zeros of `f`. -/
noncomputable def stepanovFullT (m : ℕ) (f B : Polynomial F) : Finset F :=
  stepanovT0 f ∪ stepanovT B (stepanovG m f)

@[simp] theorem mem_stepanovFullT (m : ℕ) (f B : Polynomial F) (c : F) :
    c ∈ stepanovFullT m f B ↔
      f.IsRoot c ∨ B.IsRoot (eval c (stepanovG m f)) := by
  simp [stepanovFullT, Polynomial.IsRoot]

/-- Equation (6.28), derived from absolute irreducibility and the size
hypothesis, with no assumed auxiliary polynomial or multiplicity bound. -/
theorem ln97_6_28 {m : ℕ} (hm : 2 ≤ m) (hmq : m ∣ Fintype.card F - 1)
    (f : Polynomial F) (hk : 0 < f.natDegree)
    (hirr : KummerAbsolutelyIrreducible m f)
    (hq : 100 * m * f.natDegree ^ 2 ≤ Fintype.card F)
    (B : Polynomial F) (hr : 0 < B.natDegree) (hrm : B.natDegree < m) :
    ((stepanovFullT m f B).card : ℝ) <
      (B.natDegree : ℝ) * Fintype.card F / m +
        4 * f.natDegree * Real.sqrt m * Real.sqrt (Fintype.card F) := by
  let q := Fintype.card F
  let M := theorem653Multiplicity q m
  have hm0 : 0 < m := by omega
  obtain ⟨hMk, hshift, hMlow⟩ := theorem653Multiplicity_spec hm0 hk hq
  have hMpos : 0 < M := by dsimp [M, q]; omega
  obtain ⟨h, hh, hmult, hdeg⟩ := ln97_6_52_cleared hm hmq f hk hirr B hr hrm hMk hshift
  have hcard : M * (stepanovFullT m f B).card ≤ h.natDegree := by
    apply card_mul_le_natDegree_of_rootMultiplicity h _ M hMpos
    intro c hc
    have hc' := (mem_stepanovFullT m f B c).mp hc
    exact hmult c (by simpa only [stepanovG, stepanovPowerExponent] using hc'.symm)
  have hcard' := (Nat.mul_le_mul_left m hcard).trans_lt hdeg
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hcount : (M : ℝ) * (stepanovFullT m f B).card <
      ((B.natDegree : ℝ) * q / m) * M + 4 * f.natDegree * q := by
    apply (mul_lt_mul_iff_right₀ hmR).mp
    have heq : (m : ℝ) * (((B.natDegree : ℝ) * q / m) * M +
        4 * f.natDegree * q) = B.natDegree * q * M + 4 * f.natDegree * q * m := by
      field_simp
    rw [heq]
    exact_mod_cast hcard'
  have hsqrt : Real.sqrt ((q : ℝ) / m) * Real.sqrt m = Real.sqrt q := by
    rw [← Real.sqrt_mul (by positivity), div_mul_cancel₀ _ hmR.ne']
  have hprod : Real.sqrt ((q : ℝ) / m) *
      (4 * f.natDegree * Real.sqrt m * Real.sqrt q) = 4 * f.natDegree * q := by
    calc
      _ = 4 * f.natDegree *
          ((Real.sqrt ((q : ℝ) / m) * Real.sqrt m) * Real.sqrt q) := by ring
      _ = 4 * f.natDegree * q := by
        rw [hsqrt, Real.mul_self_sqrt (by positivity)]
  have herror := mul_le_mul_of_nonneg_right hMlow
    (show (0 : ℝ) ≤ 4 * f.natDegree * Real.sqrt m * Real.sqrt q by positivity)
  rw [hprod] at herror
  apply (mul_lt_mul_iff_right₀ hMR).mp
  change (M : ℝ) * (stepanovFullT m f B).card <
    M * ((B.natDegree : ℝ) * q / m + 4 * f.natDegree * Real.sqrt m * Real.sqrt q)
  nlinarith

end LN97
end MagicSquares
