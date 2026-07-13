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
  38-declaration finite-rule machine kernel, the 14-declaration blank-delimited output/handoff
  boundary, the 20-declaration boundary-marked pipeline tape geometry, the 70-declaration
  executable all-input framer, the 39-declaration collision-free pipeline state namespace, the
  56-declaration executable pipeline stage-bridge surface, the framed
  raw-machine simulation surface, the 48-declaration finite
  charged-pipeline complexity interface, the
  six-declaration raw-pipeline refinement boundary, the two-declaration inactive
  concrete target, the 29-declaration all-input four-stage compiler, the concrete CNF semantics/codec,
  paired work-input bridge, direct verifier bridge, and complete work-machine correctness closure,
  and enforced zero-axiom direct-wire semantics, enumerator, finite truth-table,
  exhaustive reference-minimum, concrete framed composition/slack, typed locked-NAND candidate,
  semantic output-lower-bound, source-accounting, finite local-baseline, and conditional
  threshold-boundary audits plus the explicit-list residual-route audit when Lean inputs change.
  Each transcript has an exact declaration count, so a truncated audit fails closed. The five
  locked-NAND transcripts require exactly 48, 25, 23, 30, and 32 clean declarations; residual
  routes require 30. The workflow also checks the byte-identical inventory mirrors, derives the
  false concrete publication gate and status/report outputs, and verifies same-environment
  double-build determinism plus exact committed bytes for the current concise nine-page PDF. The
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
assumption-free non-theorem data, `PNP.Main.p_eq_np` is absent, and the conditional bridge's four
project-specific axioms remain visible in the workflow log. The locked-NAND threshold-boundary
audit proves deductions only from six explicit premises; it does not instantiate the global
builder, carrier layout, cross-instance baseline distinctness, trace/final laws, report threshold,
unconditional residual-slack-at-most-four bound, or polynomiality. The concrete-complexity audit
checks finite machine-leaf syntax, certificate and runtime bounds, output handoff costs, reduction
composition, and the inactive target. The refinement audit adds exact proof-bearing contracts, raw
machine-leaf witnesses, output-bound transport, and a decider bridge from a supplied refinement; it
does not construct composition/precomposition refinements or supply the missing general compiler
to one raw machine.

The tape-handoff audit corrects the earlier list-boundary-sensitive output convention: explicit and
implicit blanks now terminate output identically. Its `handoffTarget` is a pure canonical data target,
not a machine, rule list, or paid copy algorithm. The separate pipeline-output-handoff module now
implements one exact internal represented handoff to that target. The state-namespace audit now
checks injective three-stage renaming, first-match preservation, lookup-isolated concatenation, and
transport of all three exact stage-local traces. The stage-bridge audit checks literal
symbol-preserving launches, verdict-indexed handoff copies, bridge-first dispatch isolation,
cumulative exact work traces, six-for-one compiled raw traces, and supplied-exact-run
accept/reject/timeout classification. The terminal-bridge audit separately checks two disjoint
packer copies, first-match isolation, preservation of every successful earlier bridge step, exact
supplied accepting/rejecting four-stage traces, terminal halts, raw output equality, timeout
behavior, and the local `18*n^2 + 36*n + 12` suffix bound. The supplied-trace theorem still requires
a caller-supplied exact target execution. `PipelinePairedCompiler` separately derives termination
and an external polynomial for proof-bearing targets on canonical pairs. `PipelineCompiler` then
extracts the target prefix internally and proves the same literal table correct for every raw
bitstring, including exact verdict/output and no-timeout at an external polynomial. Recursive
charged-program refinement remains unproved.

The pipeline-tape geometry audit proves a two-track representation with distinct data/left/right
tags, arbitrary stale cells outside the first markers, and exact preservation under data writes,
interior moves, and empty-side boundary expansion. The expansion terms are pure `WorkTape` data
functions. They do not supply rules, machine states, a simulation run, or a transition-count bound.

The pipeline-machine simulation audit covers the separate executable local layer. It checks that
ordered raw rules preserve first-match behavior, terminal-source entries are omitted, boundary
growth tolerates every exterior work symbol, and every supplied exact `n`-step successful raw run
becomes exactly `3 * n` successful work steps. An ordinary raw run with fuel `F` yields an exact
prefix of length `k ≤ F` reaching the same endpoint. If that endpoint is designated halting,
`workRun` with fuel `3 * F` and compiled `run` with fuel `18 * F` reach the represented endpoint
and its encoding. CI keeps the premise and accounting explicit: this does not prove termination, the full
budgets are not successful-step counts or input-size bounds, and a stuck nonhalting stop is not a
verdict. The local theorems start from an already represented configuration. The separate bridge
module supplies canonical paired framing, exact launches, and target verdict preservation for a
supplied exact run. The terminal bridge preserves that trace in its extended machine and, for a
caller-supplied exact accepting or rejecting target execution, composes the subsequent raw-output
suffix. `PipelinePairedCompiler` adds target termination and an external polynomial for canonical
pairs. `PipelineCompiler` proves arbitrary-input complete behavior for the same raw table; only
the general composition/precomposition refinement remains unproved at this layer.

The pipeline-input-framer audit covers a different literal finite machine. Its compiled theorem
starts from every ordinary raw input, including empty and odd words, reaches an accepting
represented frame with permitted exterior garbage, and pins exact branch costs plus the uniform
raw bound `6 * m * m + 39 * m + 75`. CI closes all 70 public declarations, requires empty axiom
closures, and mutates the empty/partial transitions, costs, endpoint, and one-step-short behavior.
It also keeps the successor boundary explicit: `PipelineCompiler` now carries arbitrary non-pair
input through the simulator, handoff, and terminal packer for an already-raw target, but does not
compile charged function/decision composition into a complete refinement, class equality, or
`P = NP`.

The pipeline-output-handoff audit covers a third literal finite machine. From an already represented
logical tape `raw`, it reaches an accepting representation of `raw.handoffTarget` after exactly
`2 * raw.outputBits.length + 4` work steps and `12 * raw.outputBits.length + 24` compiled steps.
CI requires the compiled theorem to start at an encoded internal work configuration and rejects an
ordinary-`startConfig` or raw-visible-`machineOutput` claim for that module. The handoff now has a disjoint renamed
state image and two verdict-indexed bridge copies. The cumulative theorem begins at ordinary paired
`startConfig` and preserves accept/reject for supplied exact target runs. The terminal bridge proves
the local launch from either resulting endpoint into a packer copy and raw-visible output with a
local quadratic bound, while requiring earlier-trace transport, target termination, the complete
pipeline run, and the external-size result from later modules. `PipelineCompiler` supplies those
facts for an already-raw proof-bearing target; the general charged-program refinement stays false.

The concrete-CNF checks do establish a narrower raw-machine result. They require complete axiom
transcripts for the canonical CNF codec and semantics, paired work-input layout, generic direct
verifier bridge, and universal work-machine correctness. The final theorems prove that the finite
compiled machine accepts exactly the true encoded certificate checks, rejects the false checks,
cannot time out at the explicit polynomial fuel bound, and yields
`PNP.Concrete.FinalUniversalDesign.cnfSATInNP : InNP CNFSAT`. CI must keep this boundary explicit:
it proves `CNFSAT ∈ NP`, not `CNFSAT ∈ P`, NP-hardness, NP-completeness, or `P = NP`.

The compiled inventory is likewise not a theorem-release signal. Publication uses a separate
fail-closed gate for `PNP.Main.p_eq_np : PNP.Main.ConcretePEqualsNP`. The concrete target now exists
as an axiom-free definition, but the compatibility/root theorem is absent, the abstract
`PNP.PEqualsNP` proposition is ineligible, the general charged-pipeline-to-raw-machine linkage
remains blocked, and the activation kernel/closure fingerprints are intentionally unset. CI checks that unset fingerprints
fail rather than matching one another, and that every theorem-emission field remains derived from
the false gate.

The publication checks run the equivalent of:

```bash
node scripts/export-lean-theorem-inventory.mjs --check
node scripts/generate-formal-publication.mjs --check
npm run report:check
```

The current root PDF is the generated nine-page formal-reconstruction report. The historical
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
