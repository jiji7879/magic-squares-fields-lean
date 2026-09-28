import MagicSquares.Stepanov.Lemma653.Complete
import MagicSquares.Stepanov.Lemma654.SimpleRoot
import MagicSquares.Weil.AffineQuadratic

namespace MagicSquares.LN97

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The quadratic character sum is exactly the error term in the point
count for `y² = f(x)`. Zeros of `f` are included with their correct fiber
cardinality one. -/
theorem quadratic_sum_eq_solutionCount_sub_card
    (hodd : ringChar F ≠ 2) (f : Polynomial F) :
    (∑ x : F, quadraticChar F (f.eval x)) =
      (stepanovSolutionCount 2 f : ℤ) - Fintype.card F := by
  have hfiber (x : F) :
      ((Finset.univ.filter (fun y : F => y ^ 2 = f.eval x)).card : ℤ) =
        quadraticChar F (f.eval x) + 1 := by
    simpa using quadraticChar_card_sqrts hodd (f.eval x)
  rw [stepanovSolutionCount_eq_sum, Nat.cast_sum]
  simp_rw [hfiber]
  simp [Finset.sum_add_distrib]

/-- A coarse quadratic character bound obtained from the proved Stepánov
point count, with irreducibility discharged by a simple root. This remains
strictly weaker than the sharp Weil bound. -/
theorem coarse_quadratic_bound_of_simple_root
    (hodd : ringChar F ≠ 2) (f : Polynomial F) {a : F}
    (ha : f.rootMultiplicity a = 1)
    (hq : 200 * f.natDegree ^ 2 ≤ Fintype.card F) :
    |((∑ x : F, quadraticChar F (f.eval x) : ℤ) : ℝ)| <
      4 * f.natDegree * (2 : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (Fintype.card F) := by
  have hmq : 2 ∣ Fintype.card F - 1 := by
    have h := FiniteField.odd_card_of_char_ne_two hodd
    omega
  have hk : 0 < f.natDegree := by
    by_contra! hn
    have hf := Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hn)
    rw [hf, Polynomial.rootMultiplicity_C] at ha
    omega
  have hirr := kummerAbsolutelyIrreducible_of_simple_root (by norm_num : 0 < 2) ha
  have h := ln97_6_53 (by norm_num : 2 ≤ 2) hmq f hk hirr (by simpa using hq)
  rw [quadratic_sum_eq_solutionCount_sub_card hodd f, Int.cast_sub, Int.cast_natCast,
    Int.cast_natCast]
  exact h

end MagicSquares.LN97

namespace MagicSquares

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- An unconditional coarse affine character bound for a nonempty family
of distinct nonzero coefficients. The constant `12r` is a rational upper
bound for the Stepánov constant `4r 2^(3/2)`. -/
theorem coarse_quadratic_affine_bound
    (hodd : ringChar F ≠ 2) {ι : Type*} [Fintype ι]
    (coeff : ι → F) (hpos : 0 < Fintype.card ι)
    (hinj : Function.Injective coeff) (hnz : ∀ i, coeff i ≠ 0)
    (hq : 200 * (Fintype.card ι) ^ 2 ≤ Fintype.card F) :
    |((∑ t : F, quadraticChar F (∏ i, (1 + coeff i * t)) : ℤ) : ℝ)| ≤
      12 * Fintype.card ι * Real.sqrt (Fintype.card F : ℝ) := by
  classical
  let roots : ι → F := fun i => -(coeff i)⁻¹
  let f : Polynomial F := ∏ i, (Polynomial.X - Polynomial.C (roots i))
  have hrootinj : Function.Injective roots := by
    intro i j h
    apply hinj
    simpa [roots] using h
  have hdegree : f.natDegree = Fintype.card ι := by
    dsimp [f]
    rw [Polynomial.natDegree_prod_of_monic]
    · simp
    · intro i _
      exact Polynomial.monic_X_sub_C _
  obtain ⟨i⟩ := Fintype.card_pos_iff.mp hpos
  have ha : f.rootMultiplicity (roots i) = 1 :=
    LN97.rootMultiplicity_prod_distinct_linear Finset.univ roots
      (fun _ _ _ _ h => hrootinj h) (Finset.mem_univ _)
  have h := LN97.coarse_quadratic_bound_of_simple_root hodd f ha (by simpa [hdegree] using hq)
  have heval (t : F) : f.eval t = ∏ i, (t - roots i) := by simp [f, Polynomial.eval_prod]
  simp only [heval, hdegree] at h
  have htwo : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 3 := by
    rw [← LN97.mul_sqrt_eq_rpow_three_halves 2 (by norm_num)]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  rw [quadraticChar_affine_product_sum coeff hnz, Int.cast_mul, abs_mul]
  calc
    _ ≤ 1 * |((∑ t : F, quadraticChar F (∏ i, (t - roots i)) : ℤ) : ℝ)| :=
      mul_le_mul_of_nonneg_right (quadraticChar_abs_le_one _) (abs_nonneg _)
    _ ≤ 4 * Fintype.card ι * (2 : ℝ) ^ (3 / 2 : ℝ) *
        Real.sqrt (Fintype.card F) := by simpa using h.le
    _ ≤ 4 * Fintype.card ι * 3 * Real.sqrt (Fintype.card F) := by gcongr
    _ = _ := by ring

end MagicSquares
