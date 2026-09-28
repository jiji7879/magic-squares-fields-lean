import MagicSquares.Weil.SharpInterface
import MagicSquares.Stepanov.Lemma653.Abstract
import MagicSquares.Stepanov.Lemma653.Parameters

namespace MagicSquares

/-!
# Separation of the two analytic bounds

The Stepánov Chapter 6 development and the sharp Chapter 5 Weil theorem are
kept as separate layers.

* `MagicSquares.LN97.ln97_6_53`, in `Stepanov.Lemma653.Complete`, proves
  the coarse point-count bound from LN97 Theorem 6.53 for the actual
  finite-field solution set.
* `MagicSquares.LN97.ln97_6_55`, in `Weil.PowerSum`, proves the power-sum
  lemma, including the arithmetic-subsequence version needed in 6.56.
* `Stepanov.Lemma654.SimpleRoot` proves absolute irreducibility when a
  polynomial has a simple root, including products of distinct linear factors.
* `Weil.CoarseQuadratic` converts the actual point count into an unconditional
  quadratic-character bound.
* `CenterOne.SquareCount` proves the exact Section 7 counting estimate
  (constants 28 and 741) from `HasSplitQuadraticWeilBound`.
* `CenterOne.CoarseSquareExistence` proves unconditional square existence
  for odd fields with `q >= 132733441`, using the coarse bound.
* `HasSplitPowerMultiplicativeWeilBound` records the exponent-sensitive
  sharp theorem needed for general powers and the constant `C1(d)`.

`Weil.LFunction.Representation` now proves the split extension-field
power-sum representation of LN97 5.39, including distinct roots equipped
with different characters. Its proof includes the monic-weight cancellation,
finite L-polynomial, Euler factors, and minimal-polynomial norm identities.

`Weil.SharpQuadratic.sharp_quadratic_weil` combines that representation
with the actual Stepánov bound and Lemma 6.55. It proves
`HasSplitQuadraticWeilBound F` in every odd finite field.
`CenterOne.SharpSquareExistence` therefore proves the threshold `553736`
unconditionally, with no character-sum or counting interface hypothesis.

`Stepanov.Lemma654.KummerCriterion` proves the multiplicity criterion,
including even exponents. `Weil.CharacterFibers` expresses arbitrary
character sums through point counts of constant twists, and
`Weil.CoarseMultiplicative` proves the uniform coarse estimate.
`Weil.SharpMultiplicative` then proves the sharp bound with repeated roots.

`CenterOne.PowerCount` proves the complete Section 14 indicator expansion,
including zero entries and the exact constant `C1(d) = d^7(7d-8)+1`.
`CenterOne.SharpPowerExistence` proves Theorem 14.1 unconditionally.
`FiniteExceptions` proves Theorem 15.1 with the explicit sufficient bound
`q > (10*n^8+10)^2` for every positive exponent and every odd finite field.
`CenterZero.PowerCount` and `CenterZero.PowerExistence` prove the exact
Section 12 count and Theorem 12.1. `CenterZero.PowerBounds` gives the
stronger bound `q > (6*n^3+6)^2` whenever `-1` is an `n`-th power,
in particular for every odd exponent. `CenterZero.Cubes` proves the
published cube threshold `q >= 1037`.

`Characters.SignCriterion` proves Lemma 12.1, and `Characters.PowerTest`
proves the exact membership test from Algorithm 1. `NormalizedSearch`
proves that the center-zero and center-one finite search is sound and
complete, including the center-one-only reduction under a sign obstruction.
`SmallFieldObstructions` certifies the exceptions forced by there being
too few power residues.

`FieldTransport` transfers certificates to every finite field of the same
cardinality. `PrunedSearch` proves the opposite-entry pruning rule, and
`FiniteCertificates` proves a smaller certificate checker using verified
supersets of the powers and possible offsets. The certificate data are checked
by kernel reduction, including the field axioms for the explicit cubic and
quintic coordinate models; no native evaluation is trusted.

`CubeClassification` proves `cubeParker_iff_of_char_ne_two`, the complete
odd-characteristic cube classification in Theorem 13.1, including all finite
prime-power coverage below 1037 and both directions of the table.
`SquareQ1Classification` proves `squareParker_iff_of_card_mod_four_one`, the
complete square classification for `q ≡ 1 (mod 4)`.
`SquareExceptions` proves `squareParker_of_card_exception`: every field
listed in Theorem 9.1 is Parker, including the fields of orders 25, 27 and 243.

`SquareClassification` proves `squareParker_iff_of_char_ne_two`, the complete
odd-characteristic square classification in Theorem 9.1. Its prime branch
checks every integer `3 mod 4` below 553736 by a positive square certificate,
a proper divisor, or a listed exception. All 22,825 positive prime witnesses
and sixteen extension-field witnesses are checked by kernel reduction.
`Q3PrimePowerCoverage` proves that these prime and extension cases exhaust
the relevant prime powers. The extension checker proves polynomial identities
and divisibility in `X^q-X`, then obtains a root in every field of the stated
cardinality; it does not assume the search program's field model is correct.
`squareParker_iff` also includes the already-proved characteristic-two case.
The finite square and cube classifications are now both complete.
-/

end MagicSquares
