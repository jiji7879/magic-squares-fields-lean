# Reproducibility and certificate provenance

## Included

The review package preserves all 332 supplied project Lean sources byte for byte: 331 files from the attached `MagicSquares(1).zip` and the separately supplied root `MagicSquares(1).lean`, installed as `MagicSquares.lean`. Although the handoff called the latest archive `MagicSquares_6.zip`, the actual attachment was `MagicSquares(1).zip`; contents, not that historical filename, were inspected. The root module was not inside this attachment's ZIP.

`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` are also preserved byte for byte. `SOURCE_SHA256SUMS` records these 335 original source/configuration files. Documentation and repository-support scripts are additional work and are not part of that source snapshot. `scripts/Audit.lean` adds a separate audit driver; it does not change the library.

The source includes certificate data, arithmetic checkers, correctness proofs, coverage arguments, and negative proofs. In particular:

| Material | Location |
| --- | --- |
| Prime square coverage data, 136 batches | `MagicSquares/Certificates/Q3Prime/Batch*.lean` |
| Joining the prime coverage intervals | `MagicSquares/Certificates/Q3Prime.lean` |
| Positive extension square data, 16 fields | `MagicSquares/Certificates/Q3Extension/Field*.lean` |
| Extension aggregation | `MagicSquares/Certificates/Q3Extension.lean` |
| Prime-power coverage | `MagicSquares/Certificates/Q3PrimePowerCoverage.lean` |
| Verified certificate infrastructure | `NatSquareCertificate.lean`, `DensePolynomial.lean`, `DensePowerCertificate.lean`, `ExtensionSquareCertificate.lean` under `MagicSquares/Certificates/` |
| Classification and exceptional cases | `SquareClassification.lean`, `SquareExceptions.lean`, `CubeClassification.lean`, `CubePrimeClassification.lean` and their imports |

The source tables contain positive witnesses and composite-factor/exception steps. Coverage and negative proofs are essential; a list of positive witnesses alone would not establish a classification. Checking the supplied certificates does not require trusting the search program that found them.

## Not supplied

No Python, Sage, Mathematica, shell, or other certificate-generation/search scripts were included in the attachments. The new `scripts/` files are verification aids, not certificate generators. The original generator versions, invocation commands, search parameters, seeds (if randomized), and raw search logs were not supplied either. The paper itself was not attached; paper theorem numbering follows the supplied source and guides.

The companion [computational repository](https://github.com/jiji7879/magic_squares_fields) supplies search code and computational outputs. Its code has not been established as the generator of the exact Lean certificate tables; the missing generation provenance remains to be supplied.

Thus the package supports rebuilding the formal proofs from the supplied certificate data. It does not yet support reproducing the original search or regenerating every certificate from scratch. To add that capability, supply the original generators with their dependencies, input conventions, exact commands and any seeds, together with a mapping from generated output to the committed Lean data. Keep those tools separate from explanatory mathematics, for example in a future `tools/certificates/` directory.

## Dependency and build records

Commit the manifest even though some dependencies have `main` or `master` as their input revision: each entry also has the exact resolved commit used for reproduction. The workflow checks that build/cache commands do not alter the pins. Compiler, dependency downloads and caches require network access for a fresh checkout; `.lake/` is intentionally excluded.

The workflow uses a GitHub-hosted Ubuntu runner and the elan installer. Those operational tools are not frozen by the Lean/mathlib lockfiles. The mathematical dependencies are pinned; a fully archived execution environment is not included. CI output will supply a fresh build and axiom record once run. Record the tested commit when publishing a release.
