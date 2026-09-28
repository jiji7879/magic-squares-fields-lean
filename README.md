# Magic squares of powers over finite fields

A Lean formalization by David Lai of finite-field magic squares with nine distinct power entries. A field is **n-Parker** if it has no such 3 × 3 magic square of n-th powers. The square case is called Parker. Zero is permitted as a power entry for positive exponents.

The formalization proves:

- The complete square-Parker classification: in odd characteristic the exceptional cardinalities are **3, 5, 7, 9, 11, 13, 17, 19, 23, 25, 27, 31, 43, 47, 67, 243**.
- The complete cube-Parker classification in odd characteristic: **3, 5, 7, 13, 19, 25, 31, 37, 43, 61, 67, 79, 127, 343**.
- The characteristic-two obstruction for every exponent.
- General-power existence bounds and finiteness of exceptional odd cardinalities for each positive exponent. These do not give complete exception tables for every exponent.

The analytic development proves the split-polynomial sharp multiplicative-character bounds needed here, including repeated roots, using L-polynomial representations, coarse Stepanov bounds over extensions, and the power-sum lemma. It does not formalize every theorem of Lidl–Niederreiter in full generality. Finite classifications combine positive certificates, negative proofs, and exhaustive coverage.

## Build

Install Git and [Lean's elan version manager](https://lean-lang.org/install/). Python 3 is needed only for the repository audit scripts; it is not needed for `lake build`. Open this directory as the project in VS Code with the Lean 4 extension if using an editor.

The supplied configuration is preserved:

| Component | Pin |
| --- | --- |
| Lean | `leanprover/lean4:v4.32.1` in `lean-toolchain` |
| mathlib | `v4.32.1` in `lakefile.toml` |
| Resolved mathlib commit | `520045ab14e26149ee970e2e617ca04b09bde5d6` in `lake-manifest.json` |
| Transitive dependencies | Exact commits in `lake-manifest.json` |

Keep all three configuration files. Do not run `lake update` or delete the manifest as part of reproducing this version. Elan selects the compiler from `lean-toolchain`; Lake uses the committed dependency manifest.

From the project directory on Linux/macOS:

```sh
lake exe cache get
lake build
python3 scripts/check_source.py
python3 scripts/check_axioms.py
```

For the review archive on Windows, save `magic-square-lean-github-ready.zip` in Downloads, then use PowerShell:

```powershell
Expand-Archive -LiteralPath "$env:USERPROFILE\Downloads\magic-square-lean-github-ready.zip" -DestinationPath "$env:USERPROFILE\Downloads\magic-square-review"
Set-Location "$env:USERPROFILE\Downloads\magic-square-review\magic-square-lean"
lake exe cache get
lake build
py -3 scripts/check_source.py
py -3 scripts/check_axioms.py
```

Check that each command succeeds before continuing. If `lake` is unavailable after installing elan, open a new terminal. For dependency-download failures, check network access; these are not proof failures. The first build needs space for the compiler, mathlib cache, and generated files. Build-job counts vary and are not a verification criterion.

Four legacy entry points are not imported by the root module. To check all of them too:

```sh
lake build MagicSquares.CenterOne.SharpPowerExistence MagicSquares.CenterOne.SharpSquareExistence MagicSquares.Certificates.PolynomialSquareCertificate MagicSquares.MagicSquares.CenterOne.Admissible
```

## Find a theorem

Import `MagicSquares`. Names below are in the `MagicSquares` namespace; the Lean statements provide the complete hypotheses.

| Declaration | Meaning | Source |
| --- | --- | --- |
| `squareParker_iff` | All finite fields: characteristic two or one of the 16 odd exceptions | [SquareClassification](MagicSquares/SquareClassification.lean) |
| `squareParker_iff_of_char_ne_two` | Odd-characteristic square classification | [SquareClassification](MagicSquares/SquareClassification.lean) |
| `cubeParker_iff_of_char_ne_two` | Odd-characteristic cube classification | [CubeClassification](MagicSquares/CubeClassification.lean) |
| `isNParker_of_charTwo` | Characteristic-two obstruction, every exponent | [CharacteristicTwo](MagicSquares/CharacteristicTwo.lean) |
| `finite_nParker_cardinalities` | Finitely many exceptional odd cardinalities for each positive exponent | [FiniteExceptions](MagicSquares/FiniteExceptions.lean) |
| `Square3.exists_magic_of_powers_of_card_gt_bound` | Existence when q > (10 n^8 + 10)^2, n > 0, odd characteristic | [FiniteExceptions](MagicSquares/FiniteExceptions.lean) |

For example:

```lean
import MagicSquares

#check MagicSquares.squareParker_iff
#check MagicSquares.cubeParker_iff_of_char_ne_two
#check MagicSquares.finite_nParker_cardinalities
```

- [THEOREM_MAP.md](THEOREM_MAP.md): paper-to-Lean navigation and hypotheses.
- [PROOF_DEPENDENCIES.md](PROOF_DEPENDENCIES.md): what each result uses and why intermediate proofs are needed.
- [REPRODUCIBILITY.md](REPRODUCIBILITY.md): certificates, missing generators, and source preservation.
- [VERIFICATION.md](VERIFICATION.md): reported build, static checks, and current audit limitations.

The existing mathematical source organization and compatibility imports are retained. Generated certificate tables remain under `MagicSquares/Certificates/`, separate from the counting and analytic arguments.

## Verification

David Lai reported that the latest consolidated source builds successfully (`3767 jobs`). The preparation checks and their scope are recorded in [VERIFICATION.md](VERIFICATION.md). A fresh compiler-derived endpoint axiom report is still required before claiming an independently rechecked audit of this prepared repository.

[GitHub Actions](.github/workflows/lean.yml) runs source checks, fetches the mathlib cache, builds the root and compatibility modules, and checks six endpoint axiom reports on pushes, pull requests, and manual dispatch. The audit permits only `propext`, `Classical.choice`, and `Quot.sound`; it rejects missing reports and any other axiom. No successful CI run is claimed before this workflow is actually run.

## Related research repository

The companion [magic_squares_fields repository](https://github.com/jiji7879/magic_squares_fields) contains Python computations and output files for the paper *Magic Squares of Squares over Finite Fields and an Extension to Arbitrary Powers*. This Lean package is prepared for a separate formalization repository; its final GitHub name and URL are not yet selected.

## Citation and references

[CITATION.cff](CITATION.cff) supplies software citation metadata. When citing this formalization, identify David Lai, the title, and the exact commit used. A repository URL, release date, DOI, and paper publication details have intentionally not been invented; add them when available.

The book abbreviated **LN97** is:

Rudolf Lidl and Harald Niederreiter. *Finite Fields*. Volume 20 of *Encyclopedia of Mathematics and Its Applications*. 2nd edition. Cambridge University Press, 1997.

Book theorem numbers and paper theorem numbers are explicitly distinguished in the guides.

## License

The original code and repository documentation are licensed under the [MIT License](LICENSE), copyright (c) 2026 David Lai. Dependency and any third-party material retain their respective licenses. This software license does not select a license for the separately maintained research paper.
