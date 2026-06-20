# Agent Instructions

These instructions apply to the whole repository.

## GitHub Actions Policy

Do not create temporary self-mutating GitHub Actions workflows.

Specifically, do not add workflows that:

- commit, push, tag, or delete files from inside GitHub Actions;
- patch the branch and then try to clean up their own tooling;
- use `git commit`, `git push`, `git rm`, `gh workflow`, or write-capable repository automation;
- use `permissions: contents: write` unless the user explicitly asks for a release/publishing workflow;
- run only on one temporary step branch such as `*-step-*`;
- have names like `finalize-*`, `diagnose-*`, `check-*-step-*`, or similar temporary branch automation.

This repository already has the durable online workflow shape:

- `.github/workflows/ci.yml` is the automatic read-only PR/push verification.
- `.github/workflows/full-verification.yml` is the manual expensive verification path.

Prefer those workflows. If more CI coverage is needed, extend the durable workflow in
a small read-only way instead of adding branch-specific finalizer workflows.

## How To Apply Generated Changes

If a task needs generated or mechanical edits:

- run the generator locally or in the agent environment;
- commit only the final source/documentation changes that should be reviewed;
- do not commit temporary generators, diagnostics, or one-off workflow files;
- do not rely on GitHub Actions to transform the PR branch into its final form.

Before finishing a PR branch, make sure its diff contains only the intended files.
Temporary files under `.github/workflows/`, `tools/`, diagnostics directories, or
generated helper scripts must be removed unless the user explicitly asked to keep
them as product code.

## Workflow Version And Permission Rules

When editing workflows:

- use current action majors already used by this repo, such as `actions/checkout@v7`
  and `actions/setup-node@v6`;
- keep default permissions read-only with `permissions: contents: read`;
- do not use artifact upload for normal CI unless the artifact is genuinely needed
  for a manual/debug workflow;
- never make an artifact/debug directory part of a changed-path gate.

## Verification Expectations

For ordinary PRs, the online CI should stay lightweight. Prefer:

- `npm run check`
- `npm run test:negative`
- `npm run examples:minimal`
- public-surface smoke tests used by `.github/workflows/ci.yml`
- the lightweight release-audit gate used by `.github/workflows/ci.yml`

Full `npm test` and the full release audit are expensive. Use them locally or through
the manual `full-verification` workflow when the change is broad, risky, or release
oriented.

## Comment-Only Or Documentation-Like Source Changes

For comment-only source changes, prove that the JavaScript diff is comment-only
before pushing:

- compare against `origin/main`;
- reject deletions in the touched source files;
- allow only blank lines or lines beginning with `/**`, `*`, `*/`, or `//`;
- run syntax checks for every touched module.

Do this locally. Do not create a `finalize-*` workflow to apply comments, validate
them, commit them, and remove itself.

## If A Temporary Workflow Already Exists

If a branch already contains temporary workflows or tooling from another agent:

- do not try to repair the self-mutating workflow unless the user explicitly asks;
- apply the intended final source changes directly;
- remove the temporary workflow/tooling files from the branch;
- push the cleaned branch and rely on the durable `ci / online-verification` check;
- if the workflow was registered in GitHub Actions, disable it after it is no longer
  needed.
