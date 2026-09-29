# Paper-to-Lean theorem map

This guide identifies the main entry points in the formalization source tree. Paper numbering follows the revised paper after merging its former Sections 3 and 4. Lean source docstrings may retain the previous numbering; declaration names are unchanged. It is a map of the principal results and supporting arguments, not an assertion that every sentence or variant in the paper or LN97 has a separate formal counterpart.

See [VERIFICATION.md](VERIFICATION.md) for build evidence and pending checks.

All paths below are relative to the project root. Names are fully qualified. Import `MagicSquares` to access the listed results. The scope column summarizes essential hypotheses; consult the Lean declaration for the complete statement.

| Paper result or role | Lean declaration | Source | Scope |
| --- | --- | --- | --- |
| Theorem 8.1: odd-field square classification | `MagicSquares.squareParker_iff_of_char_ne_two` | [Source](MagicSquares/SquareClassification.lean) | Odd characteristic; equivalence with the complete 16-order exception list. |
| All finite fields: square classification | `MagicSquares.squareParker_iff` | [Source](MagicSquares/SquareClassification.lean) | Characteristic two, or membership in the same exception list. |
| Theorem 12.1: odd-field cube classification | `MagicSquares.cubeParker_iff_of_char_ne_two` | [Source](MagicSquares/CubeClassification.lean) | Odd characteristic; equivalence with the complete 14-order exception list. |
| Section 15: characteristic-two obstruction | `MagicSquares.isNParker_of_charTwo` | [Source](MagicSquares/CharacteristicTwo.lean) | Any commutative ring of characteristic two, every exponent. |
| Square existence threshold | `MagicSquares.Square3.exists_centerOne_magic_of_squares_of_card_ge_553736` | [Source](MagicSquares/CenterOne/SquareCount.lean) | Odd finite field; q ≥ 553736. |
| Cube existence threshold | `MagicSquares.exists_centerZero_magic_of_cubes_of_card_ge_1037` | [Source](MagicSquares/CenterZero/Cubes.lean) | Odd finite field; q ≥ 1037. |
| Lemma 11.1: sign criterion | `MagicSquares.isNthPower_neg_one_iff_powerIndex_dvd_half` | [Source](MagicSquares/Characters/SignCriterion.lean) | n > 0, odd characteristic; −1 is an n-th power iff gcd(n,q−1) divides (q−1)/2. |
| Theorem 11.1: center-zero powers | `MagicSquares.exists_centerZero_magic_of_powers_of_bound` | [Source](MagicSquares/CenterZero/PowerExistence.lean) | n > 0, odd characteristic, sign condition and the exact numerical inequality in the statement. |
| Theorem 13.1: center-one powers | `MagicSquares.Square3.exists_centerOne_magic_of_powers_of_bound` | [Source](MagicSquares/CenterOne/PowerCount.lean) | n > 0, odd characteristic, q > 7 and the exact numerical inequality in the statement. |
| Theorem 14.1: finite exceptions | `MagicSquares.finite_nParker_cardinalities` | [Source](MagicSquares/FiniteExceptions.lean) | For each positive n, finitely many exceptional odd-field cardinalities. |
| Explicit general-power bound | `MagicSquares.Square3.exists_magic_of_powers_of_card_gt_bound` | [Source](MagicSquares/FiniteExceptions.lean) | n > 0, odd characteristic; q > (10 n^8 + 10)^2. |
| Algorithm 1: power membership | `MagicSquares.isNthPower_iff_zero_or_pow_eq_one` | [Source](MagicSquares/Characters/PowerTest.lean) | n > 0; zero, or the stated multiplicative exponent test. |
| Normalized search completeness | `MagicSquares.exists_magic_of_powers_iff_normalized` | [Source](MagicSquares/NormalizedSearch.lean) | Existence iff one of the normalized center-zero/center-one searches has a witness. |
| Quadratic Weil input | `MagicSquares.LN97.sharp_quadratic_weil` | [Source](MagicSquares/Weil/SharpQuadratic.lean) | Proves the split quadratic Weil interface in odd finite fields. |
| General-power Weil input | `MagicSquares.LN97.sharp_power_multiplicative_weil` | [Source](MagicSquares/Weil/SharpMultiplicative.lean) | Proves the exponent-sensitive split multiplicative Weil interface. |
| LN97 5.39 representation used here | `MagicSquares.LN97.splitCharacterPowerSum_representation_extensions` | [Source](MagicSquares/Weil/LFunction/Representation.lean) | Split character sums over extension fields; the project-specific representation, not a claim about every formulation of LN97 5.39. |
| LN97 6.53 | `MagicSquares.LN97.ln97_6_53` | [Source](MagicSquares/Stepanov/Lemma653/Complete.lean) | Finite-field point-count estimate under the theorem’s degree, divisibility and multiplicity hypotheses. |
| LN97 6.55 | `MagicSquares.LN97.ln97_6_55` | [Source](MagicSquares/Weil/PowerSum.lean) | Power-sum bound used to pass from coarse to sharp estimates. |
| Finite prime certificate coverage | `MagicSquares.Certificates.q3Prime_covered` | [Source](MagicSquares/Certificates/Q3Prime.lean) | 136 joined intervals; each candidate is excluded by a proper divisor, listed as an exception, or supplied with a checked square. |
| Extension witnesses | `MagicSquares.Certificates.not_squareParker_of_card_q3_extension` | [Source](MagicSquares/Certificates/Q3Extension.lean) | All 16 positive extension orders below 553736 in the 3 mod 4 branch. |
| Prime-power coverage | `MagicSquares.Certificates.q3_prime_power_coverage` | [Source](MagicSquares/Certificates/Q3PrimePowerCoverage.lean) | Every relevant prime power below 553736 is prime or one of the 18 extension orders, including exceptions 27 and 243. |

## How the classification proofs fit together

The square proof splits odd field sizes into the residue classes 1 and 3 modulo 4. `SquareQ1Classification.lean` handles the first class. For the second, the proved 553736 threshold handles large fields; the finite certificates and prime-power coverage handle the remaining sizes. `SquareExceptions.lean` proves the nonexistence direction for every listed order. `SquareClassification.lean` assembles the equivalence and adds characteristic two.

The cube proof combines the proved threshold 1037, complete small prime-power coverage, explicit positive witnesses and negative certificates. Its final odd-characteristic statement is in `CubeClassification.lean`; `CharacteristicTwo.lean` supplies the even-characteristic obstruction.

## What the finite data proves

Prime certificates use nine integer roots. Lean checks their squares modulo q, all line sums and distinctness. The dense coverage checker also verifies proper divisors of composite candidates, so the list of positive witnesses is not itself assumed exhaustive.

Extension certificates use dense polynomial coefficients. Lean checks root identities, line sums, inverse identities for entry differences, and a modular-power trace showing that the defining polynomial divides X^q−X. That polynomial has a root in every field of size q; the checked identities produce a valid magic square at that root. The argument does not assume that Python correctly constructed a finite field.

`q3_prime_power_coverage` separately proves that no relevant extension order was omitted. The two negative extension cases in this branch are 27 and 243.

## Interfaces versus completed results

Names beginning with `Has...Bound` describe mathematical propositions used between proof stages. Their presence does not mean the final classification assumes an unproved estimate. The sharp Weil modules prove the required interfaces, and the final existence and classification declarations discharge those analytic inputs. For theorem application, prefer the final entry points above to intermediate conditional lemmas.

## General powers: scope of completion

Theorems 11.1 and 13.1 provide sufficient numerical conditions; Theorem 14.1 proves finiteness of exceptional odd-field cardinalities. The Lean development additionally supplies the explicit uniform bound listed above. These results apply to arbitrary positive n. The complete explicit exception tables in this release are for n = 2 and n = 3.
