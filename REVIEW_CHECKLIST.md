# Repository and release checklist

The formalization is public at [jiji7879/magic-squares-fields-lean](https://github.com/jiji7879/magic-squares-fields-lean). This checklist tracks the remaining verification and release work.

- [x] David approved MIT; `LICENSE`, README scope, and `CITATION.cff` are updated. The paper license remains a separate decision.
- [x] David created the public repository as `jiji7879/magic-squares-fields-lean`.
- [x] The README uses the actual repository URL and clone instructions; `CITATION.cff` includes `repository-code`.
- [x] GitHub Actions has started running. See [VERIFICATION.md](VERIFICATION.md) for the dated observation and run link.
- [ ] Confirm a successful build of the root and all four compatibility targets and a successful six-endpoint axiom audit; retain the actual axiom output.
- [ ] Update `VERIFICATION.md` with the successful run URL, tested commit, and actual endpoint axiom reports. Do not claim a passing result before checking it.
- [ ] Add a software release version/date only when an actual release is chosen. The Lake package version `0.1.0` alone is not a published release.
- [ ] If available, add original certificate generators and exact reproduction instructions separately. Their absence does not prevent checking the committed formal proofs.
- [ ] Add a stable link to the paper when available. Its title is recorded in the companion computational repository; publication details must be supplied rather than inferred.

For further updates, work in the existing clone, inspect `git diff`, and commit only the intended files. Do not reinitialize the repository. A local commit remains local until pushed.
