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
  audits the complete Lean source closure, builds the explicit `PNP` root, generates its public
  declaration inventory from `Lean.Environment.constants` plus `Lean.collectAxioms`, and prints
  the focused axiom transcripts for the 41-declaration concrete bitstring/polynomial kernel, the
  38-declaration finite-rule machine kernel, and enforced zero-axiom direct-wire semantics, enumerator, finite truth-table,
  exhaustive reference-minimum, concrete framed composition/slack, typed locked-NAND candidate,
  semantic output-lower-bound, source-accounting, finite local-baseline, and conditional
  threshold-boundary audits plus the explicit-list residual-route audit when Lean inputs change.
  Each transcript has an exact declaration count, so a truncated audit fails closed. The five
  locked-NAND transcripts require exactly 48, 25, 23, 30, and 32 clean declarations; residual
  routes require 30. The workflow also checks the byte-identical inventory mirrors, derives the
  false concrete publication gate and status/report outputs, and verifies same-environment
  double-build determinism plus exact committed bytes for the current concise six-page PDF. The
  hosted runner's apt-installed TeX and Poppler versions are not cryptographically pinned, so this
  is not a universal cross-toolchain reproducibility claim.
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
project-specific axioms remain visible in the workflow log. The locked-NAND threshold-boundary
audit proves deductions only from six explicit premises; it does not instantiate the global
builder, carrier layout, cross-instance baseline distinctness, trace/final laws, report threshold,
unconditional residual-slack-at-most-four bound, or polynomiality.

The compiled inventory is likewise not a theorem-release signal. Publication uses a separate
fail-closed gate for `PNP.Main.p_eq_np : PNP.Main.ConcretePEqualsNP`. Both declarations are absent,
the abstract `PNP.PEqualsNP` proposition is ineligible, and all five expected kernel/closure
fingerprints are intentionally unset. CI checks that unset fingerprints fail rather than matching
one another, and that every theorem-emission field remains derived from the false gate.

The publication checks run the equivalent of:

```bash
node scripts/export-lean-theorem-inventory.mjs --check
node scripts/generate-formal-publication.mjs --check
npm run report:check
```

The current root PDF is the generated six-page formal-reconstruction report. The historical
56-page claim artifact is not a current workflow output and is available only at the pinned legacy
coordinate recorded under `archive/legacy-v0/`.

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
