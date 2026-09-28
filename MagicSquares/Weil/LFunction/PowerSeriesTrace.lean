import MagicSquares.Weil.LFunction.ReciprocalRoots
import Mathlib.RingTheory.PowerSeries.Derivative

namespace MagicSquares.LN97

open scoped BigOperators

/-- The formal logarithmic derivative, used only when the constant
coefficient is nonzero. It involves no analytic convergence assumptions. -/
noncomputable def formalLogDerivative (P : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.derivative ℂ P * P⁻¹

theorem formalLogDerivative_mul (P Q : PowerSeries ℂ)
    (hP : PowerSeries.constantCoeff P ≠ 0) (hQ : PowerSeries.constantCoeff Q ≠ 0) :
    formalLogDerivative (P * Q) = formalLogDerivative P + formalLogDerivative Q := by
  simp only [formalLogDerivative, Derivation.leibniz, smul_eq_mul, PowerSeries.mul_inv_rev]
  calc
    _ = (PowerSeries.derivative ℂ P * P⁻¹) * (Q * Q⁻¹) +
        (PowerSeries.derivative ℂ Q * Q⁻¹) * (P * P⁻¹) := by ring
    _ = _ := by rw [PowerSeries.mul_inv_cancel P hP, PowerSeries.mul_inv_cancel Q hQ]; ring

@[simp]
theorem formalLogDerivative_one : formalLogDerivative 1 = 0 := by
  simp [formalLogDerivative, Derivation.map_one_eq_zero]

noncomputable def reciprocalFactor (a : ℂ) : PowerSeries ℂ :=
  1 - PowerSeries.C a * PowerSeries.X

theorem reciprocalFactor_constantCoeff (a : ℂ) :
    PowerSeries.constantCoeff (reciprocalFactor a) = 1 := by simp [reciprocalFactor]

theorem reciprocalFactor_inv (a : ℂ) :
    (reciprocalFactor a)⁻¹ = PowerSeries.mk (fun n => a ^ n) := by
  symm
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by simp [reciprocalFactor])).mpr
  ext n
  rw [reciprocalFactor, mul_sub, mul_one]
  have heq : PowerSeries.mk (fun n => a ^ n) * (PowerSeries.C a * PowerSeries.X) =
      PowerSeries.C a * PowerSeries.mk (fun n => a ^ n) * PowerSeries.X := by ring
  rw [heq, map_sub]
  cases n with
  | zero => simp [PowerSeries.coeff_mk]
  | succ n =>
    rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C_mul]
    simp [PowerSeries.coeff_mk, pow_succ, mul_comm]

private theorem reciprocalFactor_logDerivative_coeff (a : ℂ) (n : ℕ) :
    PowerSeries.coeff n (formalLogDerivative (reciprocalFactor a)) = -a ^ (n + 1) := by
  have hd : PowerSeries.derivative ℂ (reciprocalFactor a) = -PowerSeries.C a := by
    simp [reciprocalFactor, map_sub, Derivation.leibniz, Derivation.map_one_eq_zero,
      PowerSeries.derivative_C, PowerSeries.derivative_X, smul_eq_mul]
  rw [formalLogDerivative, hd, reciprocalFactor_inv, neg_mul, map_neg,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
  simp [pow_succ, mul_comm]

private theorem formalLogDerivative_prod_reciprocalFactors
    {ι : Type*} (s : Finset ι) (a : ι → ℂ) :
    formalLogDerivative (∏ i ∈ s, reciprocalFactor (a i)) =
      ∑ i ∈ s, formalLogDerivative (reciprocalFactor (a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      formalLogDerivative_mul, ih]
    · simp [reciprocalFactor_constantCoeff]
    · simp [map_prod, reciprocalFactor_constantCoeff]

/-- Coefficients of the logarithmic derivative of a split normalized
polynomial are the negative power sums of its reciprocal roots. This is
the algebraic generating-function identity (5.24) used in LN97 5.39. -/
theorem logDerivative_coeff_eq_neg_powerSum
    {d : ℕ} (alpha : Fin d → ℂ) (P : Polynomial ℂ)
    (hP : P = ∏ i, (1 - Polynomial.C (alpha i) * Polynomial.X)) (n : ℕ) :
    PowerSeries.coeff n (formalLogDerivative (P : PowerSeries ℂ)) =
      -(∑ i, alpha i ^ (n + 1)) := by
  have hcoe : (P : PowerSeries ℂ) = ∏ i, reciprocalFactor (alpha i) := by
    rw [hP]
    change Polynomial.coeToPowerSeries.ringHom
      (∏ i : Fin d, (1 - Polynomial.C (alpha i) * Polynomial.X)) = _
    rw [map_prod]
    simp [reciprocalFactor]
  rw [hcoe, formalLogDerivative_prod_reciprocalFactors, map_sum]
  simp only [reciprocalFactor_logDerivative_coeff, Finset.sum_neg_distrib]

/-- The first logarithmic-derivative coefficient is the linear coefficient
when the constant coefficient is one. -/
theorem logDerivative_coeff_zero (P : Polynomial ℂ) (hP : P.coeff 0 = 1) :
    PowerSeries.coeff 0 (formalLogDerivative (P : PowerSeries ℂ)) = P.coeff 1 := by
  rw [formalLogDerivative, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_mul, PowerSeries.constantCoeff_inv, Polynomial.constantCoeff_coe, hP]
  simp only [inv_one, mul_one]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative,
    Polynomial.coeff_coe]
  simp

variable {F : Type*} [Field F] [Fintype F]

/-- The logarithmic-derivative sequence of the actual split L-polynomial. -/
noncomputable def splitLTrace {r : ℕ} (roots : Fin r → F)
    (chars : Fin r → MulChar F ℂ) (s : ℕ) : ℂ :=
  PowerSeries.coeff (s - 1) (formalLogDerivative (splitLPolynomial roots chars : PowerSeries ℂ))

/-- The first trace is already the character sum over the base field. -/
theorem splitLTrace_one {r : ℕ} (roots : Fin r → F)
    (hinj : Function.Injective roots) (chars : Fin r → MulChar F ℂ)
    (hchars : ∃ j, chars j ≠ 1) :
    splitLTrace roots chars 1 = ∑ t : F, ∏ i, chars i (t - roots i) := by
  simp only [splitLTrace, Nat.sub_self]
  rw [logDerivative_coeff_zero _ (splitLPolynomial_coeff_zero roots hinj chars hchars),
    splitLPolynomial_coeff roots hinj chars hchars, splitLCoeff_one]

/-- The finite generating polynomial supplies at most `r-1` complex
numbers with all its positive traces as negative power sums.

`LFunction.Representation` identifies `splitLTrace s` with the actual
norm-lifted character sum over a degree-`s` extension. The present theorem
establishes the algebraic power-sum representation used there. -/
theorem splitLTrace_exists_powerSum_representation {r : ℕ} (roots : Fin r → F)
    (hinj : Function.Injective roots) (chars : Fin r → MulChar F ℂ)
    (hchars : ∃ j, chars j ≠ 1) :
    ∃ (d : ℕ) (alpha : Fin d → ℂ), d ≤ r - 1 ∧
      ∀ s : ℕ, 0 < s → splitLTrace roots chars s = -(∑ i, alpha i ^ s) := by
  obtain ⟨d, alpha, hd, hfactor⟩ := splitLPolynomial_exists_reciprocal_roots roots hinj chars hchars
  refine ⟨d, alpha, hd, ?_⟩
  intro s hs
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  simpa only [splitLTrace, Nat.succ_eq_add_one, Nat.add_sub_cancel] using
    logDerivative_coeff_eq_neg_powerSum alpha _ hfactor n

end MagicSquares.LN97
