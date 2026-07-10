# GitHub Actions audit

The repository uses read-only verification workflows and keeps historical checker execution separate
from current theorem status.

## Durable workflows

- `.github/workflows/ci.yml` automatically checks the current package/status boundary on pull
  requests and `main` pushes.
- `.github/workflows/pnp-verify-all.yml` runs the conservative one-command verifier.
- `.github/workflows/proof-development.yml` checks the formal status, closed public surface, and
  archive integrity.
- `.github/workflows/lean-bridge.yml` verifies the pinned Elan archive and exact Lean/Lake versions,
  audits the complete Lean source closure, builds the explicit `PNP` root, and prints its axiom
  inventory when Lean inputs change.
- `.github/workflows/legacy-v0-replay.yml` is manual only. It replays the immutable historical
  checker coordinates and uploads a non-authoritative transcript.

All workflows use `contents: read`. None commits, pushes, tags, patches branches, or transforms the
checkout.

## Automatic current-authority gate

The `ci / current-authority` job performs:

1. `npm ci --ignore-scripts` with full tag/history availability;
2. syntax checks over the active JavaScript surface;
3. the explicitly scoped current-authority and archive-boundary tests;
4. the conservative verifier, which does not execute legacy replay;
5. local Markdown-link checking; and
6. a final clean-tree check.

The automatic gate does not execute `RunAll0`, release audits, materialized theorem routes, or the
historical 1,121-test suite. Those routes are not current package exports, scripts, or bins.

The Lean workflow's successful build is not a theorem-release signal. Its root status is
assumption-free non-theorem data, `PNP.Main.p_eq_np` is absent, and the conditional bridge's five
project-specific axioms remain visible in the workflow log.

## Manual legacy-v0 replay

The manual `legacy-v0-replay` workflow fetches all tags, verifies the exact annotated tag objects,
peeled commits, trees, and archived digests, then creates detached worktrees. Its default mode runs
the ten-file hardened smoke set; the explicit `full` input instead runs the recorded source
validation suite. Output is written outside the checkout and uploaded as a short-lived transcript.

The three annotated tags are unsigned. Replay establishes pinned Git identity and implemented
predicate behavior only. It is not current status authority, a mathematical proof, or permission to
emit a theorem conclusion.

## Retired workflow patterns

Former per-checker, release, public-review, external-review, theorem-activation, branch-finalizer,
and self-mutating workflows are retired. Historical runs may remain visible in the Actions UI, but
they are not current gates.

## Policy

- Automatic CI stays bounded, deterministic, and read-only.
- Generated edits are applied before push; workflows verify rather than mutate.
- Historical execution remains manual and pinned.
- Branch protection should require current workflow job names, not retired checker or finalizer jobs.
- No checker, replay, checksum, or workflow result can upgrade the formal theorem status.
