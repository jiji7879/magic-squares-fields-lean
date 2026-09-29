# From the paper to the Lean proofs

This guide follows the earlier LN97 dependency map: **the result, what it uses, why those intermediate results are needed, and where they live in Lean**. It describes the completed proof architecture in the current source archive, rather than a list of future formalization tasks.

Paths below are relative to the project root. The LN97 numbering follows the earlier guide. The implementation proves the split-polynomial character bounds needed by this paper; it does not claim to formalize every statement of LN97 in its full generality. This is a source-based dependency guide, not a new line-by-line audit of the paper.

**Book reference (LN97).** Rudolf Lidl and Harald Niederreiter. *Finite Fields*. Volume 20 of *Encyclopedia of Mathematics and Its Applications*. 2nd edition. Cambridge University Press, 1997.

Throughout this guide, **LN97** refers to this book. Numbers explicitly labeled LN97 (such as Theorem 5.41 or Lemma 6.55) are the book's theorem and lemma numbers; references labeled “the paper” refer to the revised magic-squares paper after merging its former Sections 3 and 4. Lean source docstrings may retain the previous numbering; the declarations and proofs are unchanged.

## 1. The endpoints: what the project proves

A field is `n`-Parker when it has no magic square of nine distinct `n`-th powers. `IsParker` is the square case.

### Complete square classification

**Result.** In odd characteristic, a finite field is Parker exactly when its cardinality is one of

`3, 5, 7, 9, 11, 13, 17, 19, 23, 25, 27, 31, 43, 47, 67, 243`.

Every finite field of characteristic two is Parker.

**Uses:**

1. The sharp character-sum bound and the center-one counting argument, giving existence above the cutoff 553736.
2. The separate classification for cardinalities congruent to 1 modulo 4.
3. Positive certificates and exhaustive coverage below the cutoff for cardinalities congruent to 3 modulo 4.
4. Negative proofs for the exceptional fields.
5. The characteristic-two obstruction.

**Why these are needed.** An asymptotic existence theorem leaves a finite interval unresolved. Positive examples alone do not prove that every nonexceptional field in that interval has been covered; the coverage theorems supply that step.

**Lean:** `MagicSquares/SquareClassification.lean`.

- `MagicSquares.squareParker_iff_of_char_ne_two`
- `MagicSquares.squareParker_iff`

### Complete cube classification

**Result.** In odd characteristic, a finite field is 3-Parker exactly when its cardinality is one of

`3, 5, 7, 13, 19, 25, 31, 37, 43, 61, 67, 79, 127, 343`.

The general characteristic-two obstruction also applies to cubes.

**Uses:**

1. The center-zero cube existence theorem for cardinalities at least 1037.
2. The prime-field classification below that bound.
3. Extension-field witnesses and the negative extension-field cases.
4. The power-index-one case, where every field element is a cube.

**Lean:** `MagicSquares/CubeClassification.lean`, with the prime case in `MagicSquares/CubePrimeClassification.lean`.

- `MagicSquares.cubeParker_iff_of_char_ne_two`

### General powers

**Result.** For each positive exponent `n`, there are only finitely many odd finite-field cardinalities that are `n`-Parker. One explicit sufficient bound for existence is

`q > (10*n^8 + 10)^2`.

For odd exponents, the center-zero argument gives the improved sufficient bound

`q > (6*n^3 + 6)^2`.

**Uses:** the exact center-one and center-zero counting inequalities described in Section 3 below, followed by elementary numerical estimates.

**Lean:** `MagicSquares/FiniteExceptions.lean` and `MagicSquares/CenterZero/PowerBounds.lean`.

- `MagicSquares.Square3.exists_magic_of_powers_of_card_gt_bound`
- `MagicSquares.finite_nParker_cardinalities`
- `MagicSquares.exists_centerZero_magic_of_odd_powers_of_card_gt_bound`

These are general existence and finiteness results, not a complete exception list for every exponent.

## 2. The LN97 proof of the character-sum bound

This section groups the book-derived analytic and algebraic ingredients together: the sharp bound and L-function argument from Chapter 5, followed by the Chapter 6 Stepanov machinery that supplies the coarse estimates. The following section returns to the paper's magic-square constructions.

### 2.1. The sharp bound and L-function argument

#### The paper's Theorem 4.1 / the role of LN97 Theorem 5.41

For a nontrivial multiplicative character `χ` and a product with `r` distinct roots,

`f(x) = ∏ᵢ (x - aᵢ)^eᵢ`,

the needed bound is

`‖Σₓ χ(f(x))‖ ≤ (r - 1)√q`,

provided all listed exponents are positive and at least one is not divisible by the order of `χ`. The number of **distinct roots**, rather than the total degree with multiplicity, controls the constant.

**Uses:**

1. A finite L-polynomial of degree at most `r - 1`.
2. A representation of character sums over extensions as power sums of its reciprocal roots.
3. Coarse Stepanov bounds over all extensions.
4. The power-sum growth lemma, which turns those coarse bounds into a modulus bound for each reciprocal root.

**Why these are needed.** The coarse Stepanov estimate is not itself the sharp `(r - 1)√q` estimate. Passing through extensions and reciprocal roots removes the coarse constant.

**Lean interfaces:** `MagicSquares/Weil/SharpInterface.lean`.

- `HasSplitQuadraticWeilBound`
- `HasSplitMultiplicativeWeilBound`
- `HasSplitPowerMultiplicativeWeilBound`

**Proofs:** `MagicSquares/Weil/SharpQuadratic.lean` and `MagicSquares/Weil/SharpMultiplicative.lean`.

- `sharp_quadratic_weil`
- `sharp_multiplicative_weil`
- `sharp_power_multiplicative_weil`

These interfaces are discharged by proofs. They are not additional axioms that the final classification assumes. The repeated-root version is essential for general powers; the squarefree version alone would not cover the character expansions in Sections 11 and 13 of the paper.

#### The role of LN97 Theorem 5.39: the power-sum representation

**Result.** There are complex numbers `α₁, …, α_d`, with `d ≤ r - 1`, such that the relevant character sum over a degree-`s` extension is

`-Σⱼ αⱼ^s`.

**Uses:**

1. Weights attached to monic polynomials and cancellation of sufficiently high-degree coefficients.
2. A finite L-polynomial with constant coefficient one and degree at most `r - 1`.
3. Factorization over the complex numbers into reciprocal-root factors.
4. Formal logarithmic derivatives and Euler factors.
5. Norm identities and grouping extension-field elements by their minimal polynomial.

**Why this intermediate code exists.** Factoring a complex polynomial gives formal power sums, but does not by itself identify them with the actual character sums over finite extensions. The norm, minimal-polynomial, and Euler-factor arguments establish that identification.

**Lean, in reading order:**

1. `MagicSquares/Weil/LFunction/MonicWeights.lean`
2. `MagicSquares/Weil/LFunction/SplitPolynomial.lean`
3. `MagicSquares/Weil/LFunction/ReciprocalRoots.lean`
4. `MagicSquares/Weil/LFunction/PowerSeriesTrace.lean`
5. `MagicSquares/Weil/LFunction/ExtensionSum.lean`
6. `MagicSquares/Weil/LFunction/EulerFactors.lean`
7. `MagicSquares/Weil/LFunction/MonicSeries.lean`
8. `MagicSquares/Weil/LFunction/Representation.lean`

The final bridge is expressed by `splitLTrace_eq_extensionSum`, `splitCharacterPowerSum_representation`, and `splitCharacterPowerSum_representation_extensions`.

#### The role of LN97 Theorem 6.56: bounding each reciprocal root

**Result.** Every reciprocal root in the representation has modulus at most `√q`.

**Uses:**

1. The preceding power-sum representation.
2. Coarse character-sum bounds in every finite extension.
3. Extension cardinalities `q^s` and norm-lifted characters.
4. LN97 Lemma 6.55: if all positive power sums are bounded by `A B^s` for one fixed constant `A`, each underlying complex number has modulus at most `B`.

**Why this gives the sharp bound.** Take `B = √q`; at extension degree one, the triangle inequality gives `d√q ≤ (r - 1)√q`.

**Lean:** the assembly is in `SharpQuadratic.lean` and `SharpMultiplicative.lean`. Supporting files are `MagicSquares/Weil/NormLift.lean`, `MagicSquares/Weil/CoarseQuadratic.lean`, `MagicSquares/Weil/CoarseMultiplicative.lean`, and `MagicSquares/Weil/PowerSum.lean` (`ln97_6_55`).

The full equality `|αⱼ| = √q` associated with LN97 Theorem 5.40 is not needed. The role of Theorem 6.56 is integrated into the sharp-bound proofs; a separate declaration named `ln97_6_56` is not required.

#### The role of LN97 Lemma 6.54: absolute irreducibility

**Result.** Establish the absolute irreducibility needed for the Kummer curve `y^m = f(x)` used by the coarse point-count argument.

**Uses:** root multiplicities, rational-function power obstructions, Kummer irreducibility, and a polynomial/rational-function bridge.

**Why another reduction is needed.** With repeated roots and composite character order, the original exponents may share factors. The proof first reduces the character and exponents to a suitable primitive situation; it does not simply assume the original Kummer curve is absolutely irreducible in every case.

**Lean:**

- `MagicSquares/Stepanov/Lemma654/SimpleRoot.lean`
- `MagicSquares/Stepanov/Lemma654/KummerCriterion.lean`
- `MagicSquares/Weil/ExponentReduction.lean`

Useful landmarks are `kummerAbsolutelyIrreducible_prod_distinct_linear_powers`, `exists_primitive_exponent_reduction`, and `sharp_split_bound_of_primitive_exponents` in `SharpMultiplicative.lean`.

### 2.2. The Stepanov machinery (LN97 Chapter 6)

#### LN97 Theorem 6.53: the coarse point-count estimate

**Uses:**

1. Lemma 6.52: a nonzero auxiliary polynomial with high-multiplicity zeros at the relevant points.
2. Lemma 6.45: the fibers of the equation `y^m = f(x)`.
3. The fact that the total multiplicity of roots of a nonzero polynomial is at most its degree.
4. Degree estimates and numerical parameter choices.

**Why these are needed.** High multiplicity makes each solution consume a controlled amount of the auxiliary polynomial's degree, producing the point-count bound.

**Lean:** `MagicSquares/Stepanov/Lemma653/Complete.lean`, culminating in `ln97_6_53`. The fiber arguments are under `MagicSquares/Stepanov/Lemma645/`.

#### LN97 Lemma 6.52: constructing the auxiliary polynomial

**Uses:**

1. Lemma 6.46: independence ensuring that nonzero coefficients yield a nonzero polynomial.
2. Lemma 6.47 and Corollaries 6.48–6.50: Hasse-derivative identities and degree control.
3. Lemma 6.51: vanishing derivatives imply root multiplicity.
4. Finite-dimensional linear algebra: more unknowns than homogeneous constraints gives a nonzero solution.
5. Arithmetic showing that the chosen parameters satisfy the required inequalities.

**Why this intermediate code exists.** Linear algebra supplies coefficients satisfying the vanishing equations, but two separate arguments are still necessary: the resulting polynomial is not identically zero, and those equations imply the required multiplicities.

**Lean:** `MagicSquares/Stepanov/Lemma652/Complete.lean`, with `ln97_6_52`, `ln97_6_52_cleared`, and `ln97_6_52_of_equationCount`.

#### LN97 Lemma 6.46: the independence argument

**Uses:** a specialized Kummer/Gauss argument, quotient-field orbit reasoning, and translation of polynomial blocks while preserving degree bounds.

**Why this implementation differs from the earlier plan.** The older guide identified a textbook appeal to symmetric polynomials as a possible formalization obstacle. The project now supplies the specialized algebraic argument needed here; it does not require a new formalization of that entire general textbook route.

**Lean:**

- `MagicSquares/Stepanov/Lemma646/QuotientOrbit.lean`
- `MagicSquares/Stepanov/Lemma646/KummerGaussBridge.lean`
- `MagicSquares/Stepanov/Lemma646/AbsoluteIrreducibility.lean`
- `MagicSquares/Stepanov/Lemma646/BlockTranslation.lean`
- `MagicSquares/Stepanov/Lemma646/Complete.lean` (`ln97_6_46`)

#### LN97 Lemmas 6.47–6.51: derivative and multiplicity infrastructure

| Textbook role | Lean source under `MagicSquares/Stepanov/Core/` | Main declaration |
|---|---|---|
| Hasse product rule, 6.47 | `Hasse.lean` | `ln97_6_47_two_factors` |
| Translation identity, 6.48 | `HasseShift.lean` | `ln97_6_48` |
| Power/degree estimate, 6.49 | `PowerDegree.lean` | `ln97_6_49` |
| Frobenius derivative simplification, 6.50 | `Corollary650.lean` | `ln97_6_50` |
| Multiplicity from vanishing derivatives, 6.51 | `Hasse.lean` | `ln97_6_51_pow_dvd`, `ln97_6_51_rootMultiplicity` |

These are the local algebraic tools that make the auxiliary-polynomial construction work in positive characteristic.

## 3. From character sums to magic squares

### Character indicators: expressing “is an n-th power” algebraically

**Uses:** the multiplicative group of a finite field, characters of the appropriate order, and a finite geometric sum. The relevant index is `d = gcd(n, q - 1)`.

**Why this is needed.** Products of indicators count parameters for which all required entries are powers. Expanding those products produces the character sums estimated above. Values where an entry is zero require explicit treatment.

**Lean:** `MagicSquares/Characters/PowerIndicator.lean`, `PowerExpansion.lean`, and `SplitPowerCount.lean` in the same directory.

Related bridges:

- `MagicSquares/Characters/SignCriterion.lean`: the criterion for `-1` to be an `n`-th power, used in the center-zero family.
- `MagicSquares/Characters/PowerTest.lean`: the executable power test, with its equivalence to the mathematical definition proved.
- `MagicSquares/NormalizedSearch.lean`: correctness of reducing existence to the normalized search families.

### Center zero: the paper's Theorem 11.1

**Uses:**

1. The three power conditions on `x - 1`, `x`, and `x + 1`.
2. The condition that `-1` is an `n`-th power, to handle the negative entries.
3. A lower bound for the total character weight.
4. An upper bound for the contribution of parameters that make entries coincide.

**Result.** The exact sufficient inequality is

`4d^3 + 3d^2 < q - C₀(d)√q`.

If it holds, some parameter remains outside the bad set and gives nine distinct powers.

**Lean:** `MagicSquares/CenterZero/PowerCount.lean` and `MagicSquares/CenterZero/PowerExistence.lean`.

- `MagicSquares.exists_centerZero_magic_of_powers_of_bound`

Numerical specialization in `MagicSquares/CenterZero/Cubes.lean` yields existence for cubes when `q ≥ 1037` in odd characteristic. `PowerBounds.lean` gives the uniform odd-exponent bound.

### Center one: the paper's Theorem 13.1

**Uses:**

1. The affine forms describing the eight noncentral entries.
2. Expansion of their power-indicator product.
3. The sharp multiplicative-character bound, including repeated-root products.
4. Estimates for inadmissible parameters and zero-entry corrections.

**Result.** With `q > 7`, the sufficient inequality is

`9d^8 < q - C₁(d)√q`, where `C₁(d) = d^7(7d - 8) + 1`.

**Lean:** `MagicSquares/CenterOne/PowerCount.lean`, with the existence theorems immediately after the counting argument.

- `MagicSquares.Square3.exists_centerOne_magic_of_powers_of_bound`

The square-specific argument in `MagicSquares/CenterOne/SquareCount.lean` gives the cutoff 553736 used in the complete square classification.

### Finiteness: the paper's Theorem 14.1

**Uses:** the center-one existence inequality, the estimate `d ≤ n`, and elementary bounds on its constants.

**Why this final step matters.** It replaces a field-dependent inequality with an explicit bound depending only on the exponent. Every odd `n`-Parker cardinality lies below that bound, hence there are finitely many.

**Lean:** `MagicSquares/FiniteExceptions.lean`.

## 4. The finite work below the analytic cutoffs

### Positive certificates

**Result.** A concrete field model and concrete entries produce a valid magic square of distinct powers.

**Uses:** verified arithmetic checkers, explicit power witnesses, distinctness checks, and transport from the concrete model to a field of the same cardinality.

**Why the long certificate output is acceptable.** The generator finds data; Lean checks that data. The correctness of the final theorem does not rest on trusting the generator's search procedure. A large collection of certificates is evidence for individual positive cases, while a separate coverage proof shows that the collection suffices.

**Lean:** the certificate infrastructure is under `MagicSquares/Certificates/`, including `NatSquareCertificate.lean`, `DensePolynomial.lean`, `DensePowerCertificate.lean`, and `ExtensionSquareCertificate.lean`. Field transport is in `MagicSquares/FieldTransport.lean`.

For the square classification's `q ≡ 3 (mod 4)` branch, the completed positive data covers 22825 prime cases and 16 extension-field cases. The extension certificates use polynomial identities and invertibility checks to justify the field computations.

### Coverage and negative cases

**Uses:**

1. Finite coverage of the relevant prime candidates below the analytic bound.
2. Prime-power coverage for extension fields.
3. Positive certificates for the nonexceptional cases.
4. Exhaustive or structural negative proofs for the exceptions.

**Why this is separate from certificate checking.** Checking a witness proves one case. Checking coverage proves that no required case was omitted. Negative proofs establish that the displayed exception lists are exact.

**Lean:** `MagicSquares/SquareClassification.lean` assembles `SquareQ1Classification.lean`, the Q3 classification and coverage modules, `SquareExceptions.lean`, and the large-field theorem. `MagicSquares/CubeClassification.lean` assembles the corresponding cube results.

In characteristic two, `MagicSquares/CharacteristicTwo.lean` proves that a magic square must have equal opposite entries, ruling out nine distinct entries for every exponent.

## 5. Suggested reading order

For the paper's conclusions, start with the statements in `SquareClassification.lean`, `CubeClassification.lean`, and `FiniteExceptions.lean`.

For the counting arguments, read `CenterZero/PowerExistence.lean` and its `PowerCount.lean` input; for center one, read the counting and existence arguments together in `CenterOne/PowerCount.lean`.

For the analytic proof, start with `Weil/SharpInterface.lean`, then `Weil/SharpMultiplicative.lean`. Follow its two main inputs separately: the L-function representation and the coarse Stepanov bounds. Read the detailed auxiliary-polynomial algebra only when you want to inspect those foundations.

For the finite classifications, separate three questions: how a positive witness is checked, why all required field orders are covered, and how each exceptional field is ruled out.

## 6. Readability cleanup and validation status

The eight reported warnings concern seven unnecessary section instances and one unnecessarily indirect use of `simpa`. The cleanup uses local `omit ... in` declarations for the seven instances and the suggested `simp [heq] at hcard` for the eighth warning. No linter is disabled.

The user confirmed that the archive with all eight warning fixes builds successfully. The subsequent readability pass adds module summaries and proof-step comments in the square and cube classifications, general-power existence and finiteness files, and the sharp multiplicative Weil proof. The extension-field branches of the cube classification are labeled with their cardinalities and the reason each case is resolved.

The comment-only pass preserved the code from the user-confirmed build. A subsequent consolidation moves the complete namespace blocks from `CenterOne/SharpSquareExistence.lean` into `CenterOne/SquareCount.lean`, and from `CenterOne/SharpPowerExistence.lean` into `CenterOne/PowerCount.lean`. Each counting argument is now followed by its existence conclusions. The old paths remain import-only compatibility files; project imports use the consolidated modules directly.

The moved theorem statements and proofs are unchanged according to the prior consolidation report. All 332 project source paths are preserved. David Lai subsequently reported `Build completed successfully (3767 jobs).` for the latest `lake build`, resolving the previously pending user-side consolidation build. This repository preparation independently checks source preservation, project imports, and import cycles; it does not treat a reported build as a fresh local axiom audit. See [VERIFICATION.md](VERIFICATION.md) for the evidence and outstanding checks.

A further structural pass could extract repeated field-transport arguments into named helper lemmas and replace terse local hypothesis names. Those changes should be made in small batches with a working Lean build.

To check that a local checkout exposes the final classification endpoints, create a temporary `CheckRelease.lean` containing:

```lean
import MagicSquares
#check MagicSquares.squareParker_iff
#check MagicSquares.cubeParker_iff_of_char_ne_two
#check MagicSquares.finite_nParker_cardinalities
```

Then run:

```text
lake env lean CheckRelease.lean
```

These checks are more informative than comparing build-job counts, which can vary with the source set and build configuration.

## Paper consistency review

The principal classifications, hypotheses, and counting constants were compared with the Lean sources at commit `93efc5597843c9da7e5ce26176f90a40ea7508d6`. [CI run 36498472790](https://github.com/jiji7879/magic-squares-fields-lean/actions/runs/36498472790) passed the build and six-endpoint axiom audit. The full three-parameter asymptotic count discussed as future work in the paper is not asserted as a result formalized here.
