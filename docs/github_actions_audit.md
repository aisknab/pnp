# GitHub Actions audit

This repository uses read-only verification workflows instead of temporary self-mutating finalizer workflows.

## Durable workflows

- `.github/workflows/ci.yml` is the automatic read-only PR, `main` push, and manual smoke workflow.
- `.github/workflows/full-verification.yml` is the manual expensive path for the complete test suite and optional full release audit.

Both workflows use `permissions: contents: read`. Neither workflow commits, pushes, tags, patches branches, removes its own files, or uploads a transformed checkout.

## Automatic `ci / online-verification` gates

The automatic workflow runs these independent gates in order:

1. lockfile-preserving install with `npm ci`;
2. core syntax check with `npm run check`;
3. targeted unit tests for the core codec, kernel, GPack, final framework, and package-sufficiency checkers;
4. the eight named negative invariants with `npm run test:negative`;
5. the eight minimal reviewer examples with `npm run examples:minimal`;
6. a sealed-release reproducibility smoke that verifies both pinned tag commits, every `SHA256SUMS` entry, the detached ledger hash, and the summary/full claim fields;
7. a local-link check over the reviewer-facing Markdown set;
8. public API and public-surface freeze tests;
9. the lightweight release-audit gate;
10. a final dirty-tree check.

The targeted unit suite is deliberately not the complete repository test inventory. `npm test` and the full release audit remain manual because the frozen 7072f8d validation took about 34 minutes and ordinary pull-request CI should stay bounded.

The consolidated gate was exercised on PR #9. Its targeted unit, negative, example, reproducibility, documentation-link, public-surface, release-audit, and dirty-tree steps all completed successfully.

## Retired workflow patterns

- `check-minimal-examples-step-5.yml` was branch-scoped to `examples/minimal-step-5` and duplicated checks that now live in the main CI smoke path.
- `check-reviewer-negative-step-6.yml` mixed verification with branch mutation. The finalizer passed tests in one run, then failed to push because the branch advanced while the long test suite was running. A later run failed because it tried to remove a workflow file that had already been removed.
- `export-main.yml` uploaded a complete checkout artifact. That was useful for a release branch handoff, but it is not a durable CI gate.
- The public-access documentation release workflows built and sealed release artifacts, but one build rejected its own `deterministic-build-diagnostics/` artifact directory in the changed-path boundary. Those release flows should stay separate from ordinary CI.
- `apply-reviewer-first-readme-step-10` patched a branch, committed the result, and attempted to clean up its own tooling. Its verification steps passed, but its self-mutation pattern violated repository policy and produced misleading failed-run notifications.

Some retired workflows also used older action majors that targeted a deprecated GitHub Actions runtime. That warning was noisy but was not the main reason the self-mutating workflows failed.

## Replacement policy

- Automatic online CI is lightweight and read-only.
- Generated or mechanical edits are applied before a branch is pushed; CI verifies the final diff rather than transforming it.
- Full `npm test` and the full release audit are available through a manual workflow dispatch, not on every push.
- Workflows do not commit, push, tag, delete themselves, or enforce untracked artifact directories as changed-path failures.
- Workflow permissions are `contents: read` unless a future user-requested release workflow has a specific write requirement.

## Flow-on effects

- Branch protection should require `ci / online-verification`, not retired temporary workflow names.
- Historical workflow records may remain visible in GitHub's Actions UI until disabled or aged out.
- Documentation release automation should be rebuilt as a separate manual release workflow if needed; it should not be part of normal push or pull-request CI.
- The reproducibility smoke verifies provenance and recorded acceptance fields only. It does not establish theorem correctness, checker soundness, or external mathematical acceptance.
