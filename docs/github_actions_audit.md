# GitHub Actions audit

This repository now uses read-only verification workflows instead of temporary
self-mutating finalizer workflows.

## Retired workflow patterns

- `check-minimal-examples-step-5.yml` was branch-scoped to
  `examples/minimal-step-5` and duplicated checks that now live in the main CI
  smoke path.
- `check-reviewer-negative-step-6.yml` mixed verification with branch mutation.
  The finalizer passed tests in one run, then failed to push because the branch
  advanced while the long test suite was running. A later run failed because it
  tried to remove a workflow file that had already been removed.
- `export-main.yml` uploaded a complete checkout artifact. That was useful for a
  release branch handoff, but it is not a durable CI gate.
- The public-access documentation release workflows built and sealed release
  artifacts, but one build rejected its own `deterministic-build-diagnostics/`
  artifact directory in the changed-path boundary. Those release flows should
  stay separate from ordinary CI.

All of those workflows also used older action majors that target the deprecated
GitHub Actions Node 20 runtime. That warning was noisy but was not the root cause
of the failed runs.

## Replacement policy

- Automatic online CI is lightweight and read-only. It runs syntax checks,
  named negative tests, minimal reviewer examples, public-surface smoke tests,
  and a lightweight release-audit gate.
- Full `npm test` and the full release audit are available through a manual
  workflow dispatch, not on every push.
- Workflows do not commit, push, tag, delete themselves, or enforce untracked
  artifact directories as changed-path failures.
- Workflow permissions are `contents: read` unless a future release workflow has
  a specific write requirement.

## Flow-on effects

- Branch protection should require `ci / online-verification`, not the retired
  temporary workflow names.
- The historical workflow records may still appear in GitHub's Actions UI until
  they are disabled or aged out.
- Documentation release automation should be rebuilt as a separate manual release
  workflow if it is needed again; it should not be part of normal push/PR CI.
