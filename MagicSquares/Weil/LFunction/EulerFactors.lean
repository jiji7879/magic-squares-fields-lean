import MagicSquares.Weil.LFunction.PowerSeriesTrace
import MagicSquares.Weil.LFunction.ExtensionSum
import Mathlib.RingTheory.PowerSeries.Expand

namespace MagicSquares.LN97

open scoped BigOperators Classical

/-- The denominator of the Euler factor attached to a degree-`d`
irreducible with character weight `a`. -/
noncomputable def eulerFactor (d : ℕ) (a : ℂ) : PowerSeries ℂ :=
  1 - PowerSeries.C a * PowerSeries.X ^ d

theorem eulerFactor_constantCoeff {d : ℕ} (hd : 0 < d) (a : ℂ) :
    PowerSeries.constantCoeff (eulerFactor d a) = 1 := by
  simp [eulerFactor, Nat.ne_of_gt hd]

theorem formalLogDerivative_inv (P : PowerSeries ℂ)
    (hP : PowerSeries.constantCoeff P ≠ 0) :
    formalLogDerivative P⁻¹ = -formalLogDerivative P := by
  have h := formalLogDerivative_mul P P⁻¹ hP (by simpa using hP)
  rw [PowerSeries.mul_inv_cancel P hP, formalLogDerivative_one] at h
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using h.symm)

/-- The geometric-series coefficient in an arbitrary positive degree. -/
theorem eulerFactor_inv_coeff {d : ℕ} (hd : 0 < d) (a : ℂ) (n : ℕ) :
    PowerSeries.coeff n (eulerFactor d a)⁻¹ =
      if d ∣ n then a ^ (n / d) else 0 := by
  have hexpand : PowerSeries.expand d (Nat.ne_of_gt hd) (reciprocalFactor a) =
      eulerFactor d a := by
    simp [reciprocalFactor, eulerFactor, map_sub, PowerSeries.expand_C]
  have hinv : (eulerFactor d a)⁻¹ =
      PowerSeries.expand d (Nat.ne_of_gt hd) (PowerSeries.mk (fun k => a ^ k)) := by
    symm
    apply (PowerSeries.eq_inv_iff_mul_eq_one (by rw [eulerFactor_constantCoeff hd]; norm_num)).mpr
    rw [← hexpand, ← reciprocalFactor_inv, ← map_mul,
      PowerSeries.inv_mul_cancel _ (by rw [reciprocalFactor_constantCoeff]; norm_num), map_one]
  rw [hinv, PowerSeries.coeff_expand]
  simp only [PowerSeries.coeff_mk]

private theorem X_mul_eulerFactor_logDerivative {d : ℕ} (hd : 0 < d) (a : ℂ) :
    PowerSeries.X * formalLogDerivative (eulerFactor d a) =
      PowerSeries.C (d : ℂ) * (1 - (eulerFactor d a)⁻¹) := by
  have hpow : (PowerSeries.X : PowerSeries ℂ) ^ (d - 1) * PowerSeries.X =
      PowerSeries.X ^ d := by rw [← pow_succ, Nat.sub_add_cancel hd]
  have hderiv : PowerSeries.X * PowerSeries.derivative ℂ (eulerFactor d a) =
      PowerSeries.C (d : ℂ) * (eulerFactor d a - 1) := by
    simp only [eulerFactor, map_sub, Derivation.map_one_eq_zero, Derivation.leibniz,
      PowerSeries.derivative_C, PowerSeries.derivative_pow, PowerSeries.derivative_X,
      smul_eq_mul, mul_zero, add_zero, mul_one, zero_sub]
    rw [show (d : PowerSeries ℂ) = PowerSeries.C (d : ℂ) by simp]
    calc
      _ = -(PowerSeries.C (d : ℂ) * PowerSeries.C a *
        (PowerSeries.X ^ (d - 1) * PowerSeries.X)) := by ring
      _ = _ := by rw [hpow]; ring
  rw [formalLogDerivative, ← mul_assoc, hderiv]
  have hc : PowerSeries.constantCoeff (eulerFactor d a) ≠ 0 := by
    rw [eulerFactor_constantCoeff hd]; norm_num
  calc
    _ = PowerSeries.C (d : ℂ) *
        ((eulerFactor d a) * (eulerFactor d a)⁻¹ - (eulerFactor d a)⁻¹) := by ring
    _ = _ := by rw [PowerSeries.mul_inv_cancel _ hc]

/-- A local Euler factor contributes precisely when its degree divides
`s`, and then contributes `d * a^(s/d)` to the logarithmic derivative. -/
theorem eulerFactor_inv_logDerivative_coeff {d s : ℕ} (hd : 0 < d) (hs : 0 < s) (a : ℂ) :
    PowerSeries.coeff (s - 1) (formalLogDerivative (eulerFactor d a)⁻¹) =
      if d ∣ s then (d : ℂ) * a ^ (s / d) else 0 := by
  have hc : PowerSeries.constantCoeff (eulerFactor d a) ≠ 0 := by
    rw [eulerFactor_constantCoeff hd]; norm_num
  have he := congrArg (PowerSeries.coeff s) (X_mul_eulerFactor_logDerivative hd a)
  rw [show s = (s - 1) + 1 from (Nat.sub_add_cancel hs).symm,
    PowerSeries.coeff_succ_X_mul] at he
  rw [Nat.sub_add_cancel hs, PowerSeries.coeff_C_mul, map_sub,
    PowerSeries.coeff_one, if_neg (Nat.ne_of_gt hs), zero_sub, eulerFactor_inv_coeff hd] at he
  rw [formalLogDerivative_inv _ hc, map_neg, he]
  split_ifs <;> ring

/-- The denominator has the negative of the local Euler trace. -/
theorem eulerFactor_logDerivative_coeff {d s : ℕ} (hd : 0 < d) (hs : 0 < s) (a : ℂ) :
    PowerSeries.coeff (s - 1) (formalLogDerivative (eulerFactor d a)) =
      -(if d ∣ s then (d : ℂ) * a ^ (s / d) else 0) := by
  have hc : PowerSeries.constantCoeff (eulerFactor d a) ≠ 0 := by
    rw [eulerFactor_constantCoeff hd]; norm_num
  have h := eulerFactor_inv_logDerivative_coeff hd hs a
  rw [formalLogDerivative_inv _ hc, map_neg] at h
  linear_combination -h

/-- Logarithmic derivatives turn a finite product of normalized factors
into a sum. -/
theorem formalLogDerivative_prod {ι : Type*} (S : Finset ι) (P : ι → PowerSeries ℂ)
    (hP : ∀ i ∈ S, PowerSeries.constantCoeff (P i) ≠ 0) :
    formalLogDerivative (∏ i ∈ S, P i) = ∑ i ∈ S, formalLogDerivative (P i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, formalLogDerivative_mul]
    · rw [ih (fun j hj => hP j (Finset.mem_insert_of_mem hj))]
    · exact hP i (Finset.mem_insert_self _ _)
    · simpa only [map_prod] using Finset.prod_ne_zero_iff.mpr
        (fun j hj => hP j (Finset.mem_insert_of_mem hj))

/-- The extension sum is the indicated coefficient of the finite product
of Euler factors for the irreducibles represented in the extension.
`MonicSeries` and `Representation` prove the finite factorization step
relating these coefficients to `splitLPolynomial`. -/
theorem splitExtensionSum_eq_finiteEulerTrace
    {F E : Type*} [Field F] [Field E] [Fintype F] [Fintype E] [Algebra F E]
    {r : ℕ} (roots : Fin r → F) (chars : Fin r → MulChar F ℂ) :
    splitExtensionSum (E := E) roots chars =
      PowerSeries.coeff (Module.finrank F E - 1)
        (formalLogDerivative
          (∏ p ∈ extensionMinimalPolynomials (F := F) (E := E),
            (eulerFactor p.natDegree (splitDegreeWeight roots chars p.natDegree p))⁻¹)) := by
  have hpos (p : Polynomial F)
      (hp : p ∈ extensionMinimalPolynomials (F := F) (E := E)) : 0 < p.natDegree := by
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
    exact minpoly.natDegree_pos (IsIntegral.of_finite F x)
  rw [formalLogDerivative_prod]
  · rw [map_sum, splitExtensionSum_eq_sum_minpoly_weights]
    apply Finset.sum_congr rfl
    intro p hp
    rw [eulerFactor_inv_logDerivative_coeff (hpos p hp) Module.finrank_pos,
      if_pos ((mem_extensionMinimalPolynomials_iff p).mp hp).2.2]
  · intro p hp
    simp [PowerSeries.constantCoeff_inv, eulerFactor_constantCoeff (hpos p hp)]

end MagicSquares.LN97
