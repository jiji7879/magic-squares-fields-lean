import MagicSquares.Weil.LFunction.MonicSeries

namespace MagicSquares.LN97

open scoped BigOperators Classical
open Polynomial

variable {F : Type*} [Field F] [Fintype F]

/-- The untruncated monic generating series is the finite split
L-polynomial, by the coefficient cancellation theorem. -/
theorem splitLPolynomial_eq_monicSeries {r : ℕ} (roots : Fin r → F)
    (hinj : Function.Injective roots) (chars : Fin r → MulChar F ℂ)
    (hchars : ∃ j, chars j ≠ 1) :
    (splitLPolynomial roots chars : PowerSeries ℂ) =
      avoidingSeries (fun g => splitDegreeWeight roots chars g.natDegree g) ∅ := by
  ext n
  rw [Polynomial.coeff_coe, splitLPolynomial_coeff roots hinj chars hchars,
    avoidingSeries_coeff]
  simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
    Finset.filter_true_of_mem]
  rw [sum_monicPolynomials]
  simp only [monicOfCoeffs_natDegree, splitLCoeff]

/-- The extension-field identity in LN97 5.39: the actual norm-lifted
character sum is the corresponding logarithmic derivative coefficient
of the finite L-polynomial. -/
theorem splitLTrace_eq_extensionSum
    {E : Type*} [Field E] [Fintype E] [Algebra F E]
    {r : ℕ} (roots : Fin r → F) (hinj : Function.Injective roots)
    (chars : Fin r → MulChar F ℂ) (hchars : ∃ j, chars j ≠ 1) :
    splitLTrace roots chars (Module.finrank F E) = splitExtensionSum (E := E) roots chars := by
  let w : Polynomial F → ℂ := fun g => splitDegreeWeight roots chars g.natDegree g
  have hw1 : w 1 = 1 := by simp [w, splitDegreeWeight, splitEvaluationWeight]
  have hw (g h : Polynomial F) (hg : g.Monic) (hh : h.Monic) : w (g * h) = w g * w h := by
    dsimp [w]
    rw [hg.natDegree_mul hh, splitDegreeWeight_mul]
  rw [splitLTrace, splitLPolynomial_eq_monicSeries roots hinj chars hchars,
    monicSeries_logDerivative_coeff w hw1 hw Module.finrank_pos, ← Finset.sum_filter]
  have hset : (monicIrreduciblesThrough (Module.finrank F E)).filter
      (fun p : Polynomial F => p.natDegree ∣ Module.finrank F E) =
      extensionMinimalPolynomials (F := F) (E := E) := by
    ext p
    rw [Finset.mem_filter, mem_monicIrreduciblesThrough, mem_extensionMinimalPolynomials_iff]
    constructor
    · rintro ⟨⟨hm, hi, _⟩, hd⟩
      exact ⟨hm, hi, hd⟩
    · rintro ⟨hm, hi, hd⟩
      exact ⟨⟨hm, hi, Nat.le_of_dvd Module.finrank_pos hd⟩, hd⟩
  rw [hset, splitExtensionSum_eq_sum_minpoly_weights]

/-- LN97 Theorem 5.39 for distinct split roots with possibly different
characters at each root. A single collection of at most `r-1` complex
numbers represents the actual character sums in every finite extension.

This proves the representation itself; bounds for the complex numbers
are a separate consequence of Stepánov and Lemma 6.55. -/
theorem splitCharacterPowerSum_representation
    {r : ℕ} (roots : Fin r → F) (hinj : Function.Injective roots)
    (chars : Fin r → MulChar F ℂ) (hchars : ∃ j, chars j ≠ 1) :
    ∃ (d : ℕ) (alpha : Fin d → ℂ), d ≤ r - 1 ∧
      ∀ (E : Type) [Field E] [Fintype E] [Algebra F E],
        splitExtensionSum (E := E) roots chars = -(∑ i, alpha i ^ Module.finrank F E) := by
  obtain ⟨d, alpha, hd, htrace⟩ :=
    splitLTrace_exists_powerSum_representation roots hinj chars hchars
  refine ⟨d, alpha, hd, ?_⟩
  intro E _ _ _
  rw [← splitLTrace_eq_extensionSum roots hinj chars hchars]
  exact htrace _ Module.finrank_pos

/-- The canonical degree-`s` extension realizes the power sums for every
positive `s`. -/
theorem splitCharacterPowerSum_representation_extensions
    {r : ℕ} (roots : Fin r → F) (hinj : Function.Injective roots)
    (chars : Fin r → MulChar F ℂ) (hchars : ∃ j, chars j ≠ 1)
    (p : ℕ) [Fact p.Prime] [CharP F p] :
    ∃ (d : ℕ) (alpha : Fin d → ℂ), d ≤ r - 1 ∧
      ∀ (s : ℕ) [NeZero s],
        letI : Fintype (FiniteField.Extension F p s) := Fintype.ofFinite _
        splitExtensionSum (E := FiniteField.Extension F p s) roots chars = -(∑ i, alpha i ^ s) := by
  obtain ⟨d, alpha, hd, hsum⟩ := splitCharacterPowerSum_representation roots hinj chars hchars
  refine ⟨d, alpha, hd, ?_⟩
  intro s _
  letI : Fintype (FiniteField.Extension F p s) := Fintype.ofFinite _
  simpa only [FiniteField.finrank_extension] using hsum (FiniteField.Extension F p s)

end MagicSquares.LN97
