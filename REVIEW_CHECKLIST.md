# Review before publishing

The working package is prepared for review, not published.

- [x] David approved MIT; `LICENSE`, README scope, and `CITATION.cff` are updated. The paper license remains a separate decision.
- [ ] Run the build, the four compatibility targets, and the endpoint audit using the README commands; retain the actual axiom output.
- [ ] Confirm the intended GitHub owner, repository name, and visibility; obtain explicit approval before publishing.
- [ ] After the first real GitHub Actions run, update `VERIFICATION.md` with the tested commit and result. Do not add a passing badge before then.
- [ ] Once the repository URL is known, add it to `CITATION.cff`. Add a software release version/date only when an actual release is chosen. The supplied Lake package version `0.1.0` alone is not a published release.
- [ ] If available, add original certificate generators and exact reproduction instructions separately. Their absence does not prevent checking the committed formal proofs.
- [ ] If the paper is to be linked or cited, supply its actual title and stable link or publication metadata.

Suggested initial commit description: `Prepare finite-field magic-square formalization for review`.

The review archive includes no Git metadata. A local repository can be initialized after review with `git init -b main`, followed by `git add .` and `git diff --cached --stat`. Committing locally does not publish anything; do not add a remote or push until publication has been approved.
