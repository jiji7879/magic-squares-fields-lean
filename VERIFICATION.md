# Verification record

Prepared for David Lai on 2026-09-28 (America/Chicago). The formalization is publicly available at [jiji7879/magic-squares-fields-lean](https://github.com/jiji7879/magic-squares-fields-lean). David Lai approved MIT licensing on 2026-09-28; the license and software citation metadata have been updated.

## Evidence and limits

| Check | Result | Evidence / scope |
| --- | --- | --- |
| Latest consolidated source build | Reported successful by David Lai | `lake build`: `Build completed successfully (3767 jobs).` Supplied with this handoff; no independent full build log was attached. |
| Source preservation | Passed during preparation | All 332 original project Lean files compared byte for byte with the attachments. |
| Configuration preservation | Passed during preparation | All three supplied configuration files compared byte for byte; no version changes. |
| Placeholder / custom-axiom source scan | Passed during preparation | No code tokens `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, or `unsafe` in the project sources, ignoring comments and strings. This is a static hygiene check, not a Lean parser or a transitive axiom computation. |
| Project import resolution / cycles | Passed during preparation | All project imports resolve; no import cycles among 332 source modules. |
| Root import coverage | Checked during preparation | 328 modules reachable; four import-only compatibility modules are built separately in CI. |
| Repository-support files | Basic checks passed | Workflow and citation YAML parsed; local Markdown links checked; axiom parser exercised against accepted, rejected and missing reports. GitHub workflow execution has started; a successful end-to-end result is not yet recorded here. |
| Fresh local compilation | Environment-blocked | The pinned toolchain was installed. `lake --version` reported Lean 4.32.1. The compiler itself failed with `error: failed to locate application`, including with an explicit installation root. This happened before elaborating any project proof. |
| Fresh endpoint axiom audit | Pending | Compiler cannot run here. No current compiler-derived endpoint axiom set is asserted. |
| GitHub Actions run | In progress when checked on 2026-09-28 | [Run 36498472790](https://github.com/jiji7879/magic-squares-fields-lean/actions/runs/36498472790), commit `93efc5597843c9da7e5ce26176f90a40ea7508d6`. The earlier run 36498241220 failed. No successful CI result is asserted in this record. |

The reported successful build supersedes the old dependency-guide statement that the consolidation still awaited a user build. It does not replace a fresh endpoint axiom audit.

## Endpoint axiom status

Earlier endpoint audits were reported to contain only `propext`, `Classical.choice`, and `Quot.sound`. Those are historical reports; the current preparation cannot independently confirm the axiom set of any endpoint below.

| Endpoint in `MagicSquares` | Current compiler audit |
| --- | --- |
| `squareParker_iff` | Pending |
| `squareParker_iff_of_char_ne_two` | Pending |
| `cubeParker_iff_of_char_ne_two` | Pending |
| `finite_nParker_cardinalities` | Pending |
| `isNParker_of_charTwo` | Pending |
| `Square3.exists_magic_of_powers_of_card_gt_bound` | Pending |

Run `lake build`, then `lake env lean scripts/Audit.lean` to print the actual transitive axioms. `python3 scripts/check_axioms.py` (Windows: `py -3 scripts/check_axioms.py`) runs that command and checks that each of the six reports is present and contains no axioms outside the permitted set. `sorryAx`, `Lean.ofReduceBool`, or any other unlisted axiom will fail the check. Reports with no axioms are also accepted. If Lean changes the output format, the script fails on missing reports rather than silently passing.

The audit driver and workflow have not been verified end to end in the preparation environment. GitHub execution is tracked separately above. Successful parser fixtures do not establish theorem verification.

## Changes in this preparation

- Preserved mathematical Lean sources, legacy imports, and all dependency pins.
- Updated two theorem-map links to the consolidated `CenterOne/SquareCount.lean` and `CenterOne/PowerCount.lean` files.
- Replaced the stale consolidation-build note with the user-reported successful result and this explicit audit status.
- Added README, reproducibility notes, this record, software citation metadata, source hashes, Git exclusions/line-ending rules, source/audit scripts, and a GitHub Actions workflow.
- Kept generated Lean certificates committed. No generator or missing paper metadata was invented.
- Added the MIT license after David Lai explicitly approved it. The preparation assistant did not publish the package. David subsequently created the public repository and uploaded the files; the repository URL is now included in the citation metadata.

## Updating this record

The CI row is a dated observation, not a live status display. After a run completes, record its final conclusion and tested commit. Mark endpoint audits as passed only after inspecting the successful axiom-check step; retain the actual reports. The earlier source-preservation and static checks describe the prepared source snapshot, not every subsequent GitHub commit.
