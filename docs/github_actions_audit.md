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
  26-declaration sequential whole-component state namespace, the
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
  The Cook--Levin lane additionally audits the 79-declaration rectangular formula schedule, the
  136-declaration direct formula cursor, the 39-declaration literal input-length tally machine, the
  40-declaration executable framer-to-tally prefix, the 68-declaration standalone four-token
  appender, the 37-declaration composed first-token prefix, the 74-declaration unary polynomial
  evaluator, the 84-declaration complete-header composition, the 60-declaration body-start
  composition, the 74-declaration first-literal composition, the combined 80-declaration
  first-clause audit, the 45-declaration literal token-cursor padding step, the combined
  84-declaration first-clause remaining-padding run, and their
  empty/one-bit/odd/even
  regression instantiations. The appender checks all four state-selected token traces and its local
  `24*n + 48` first-token raw bound. The composed audit checks the exact 184-rule table, disjoint
  state images, nine-rule bridge, all-input exact trace, final `T` token, external
  `18*n^2 + 87*n + 147` bound, malformed phases, one-step-short timeout, and the first two
  direct/canonical formula bits in both verifier input modes. The first-literal audit additionally
  checks four disjoint state images, three total bridges, exact `T^FormulaWidth F Sep T F` output,
  the constructive positive-variable-zero schedule proof, retained coordinate
  `FormulaVariableSlotBound + 4`, the external compiled polynomial, malformed phases, and all
  endpoint/one-step-short timeout boundaries. The token-cursor-step audit checks the exact fixed
  45-rule suffix table, total launch, first valid-padding outcome, unchanged first-clause output,
  advancement from `FormulaVariableSlotBound + 12` to `+ 13`, external compiled bound, malformed
  scratch timeout, and one-step-short total timeout without claiming a complete cursor loop.
  The remaining-padding audit additionally checks the fixed 25-rule loop, three total launches,
  exact input-dependent padding count, no-emission specification traversal, second-clause `Sep`
  target, external polynomial bound, malformed countdown timeouts, and one-step-short total timeout
  without claiming a general dynamic cursor. The second-clause-separator audit then checks the
  selected 59-rule `Sep` appender, both total launches, the fixed cursor suffix, exact canonical
  prefix through clause two's separator, retained following-`F` coordinate, external polynomial,
  malformed appender/cursor phases, both unlaunched endpoints, and one-step-short timeout. Its exact
  56-line closure split is 15 empty, 11 `propext`, and 30 `propext`/`Quot.sound` declarations.
  The second-clause-first-literal audit checks both selected `F` appenders, both cursor copies, all
  four total launches, the exact negative-variable-zero formula prefix, the three direct `F`
  schedule outcomes, the external polynomial, every malformed copy and pre-launch boundary, and
  the exact 87-line closure split of 25 empty, 18 `propext`, and 44 `propext`/`Quot.sound`
  declarations without claiming a complete clause-two emitter or general dynamic cursor.
  The second-clause-second-literal audit checks the selected `F`, `T`, and `F` appenders, all three
  cursor copies, all six total launches, the exact negative-variable-one formula prefix, the direct
  `F`/`T`/`F` outcomes and retained `Finish`, the external polynomial, every malformed copy and
  pre-launch boundary, and the exact 115-line closure split of 34 empty, 25 `propext`, and 56
  `propext`/`Quot.sound` declarations without claiming that the terminator or complete clause two
  is emitted. The complete-second-clause audit checks the selected 59-rule `Finish` appender, the
  two total launches, one fixed cursor advance, the exact 113-rule suffix and symbolic 2098-rule
  global base, the canonical formula prefix through the complete second clause, direct `Finish`
  execution, the retained first padding coordinate, the external polynomial, malformed phases,
  both unlaunched endpoints, and one-step-short timeout. Its exact 57-line closure split is 15
  empty, 10 `propext`, and 32 `propext`/`Quot.sound` declarations; it does not traverse clause-two
  padding or claim a general cursor or complete formula builder. The second-clause-padding audit
  checks both fixed unary evaluators, all three total `WorkChain` bridges, reuse rather than
  duplication of the 25-rule countdown, the symbolic 2150-rule global base, the exact `C - 7`
  positive count, every direct padding opportunity, the retained third-clause `Sep` coordinate,
  unchanged canonical output, the external polynomial, malformed countdown phases, the unlaunched
  predecessor endpoint, and one-step-short timeout. Its exact 68-line closure split is 26 empty, 9
  `propext`, and 33 `propext`/`Quot.sound` declarations; it does not emit clause three or claim a
  general cursor or complete formula builder. The third-clause-separator audit checks reuse of the
  selected 59-rule `Sep` appender and fixed 45-rule cursor table, both total launches, the symbolic
  2272-rule global base, the exact canonical prefix through the third clause's opening separator,
  the following direct `F`, the external polynomial, malformed phases, both unlaunched endpoints,
  and one-step-short timeout. Its exact 56-line closure split is 14 empty, 11 `propext`, and 31
  `propext`/`Quot.sound` declarations; it does not emit that `F` or claim a general cursor or
  complete formula builder.
  The third-clause-first-literal audit checks reuse of the complete 235-rule two-`F`
  appender/cursor suffix behind one total bridge, all four internal launches, the symbolic
  2516-rule global base, the exact canonical prefix through negative variable zero in clause
  three, constructive identification of excluded pair `(0,2)`, the direct `F` sign, terminator,
  and following-sign outcomes, the external polynomial, every malformed appender/cursor copy,
  all four unlaunched endpoints, and one-step-short timeout. Its exact 87-line closure split is
  24 empty, 18 `propext`, and 45 `propext`/`Quot.sound` declarations; it does not emit that next
  `F`, complete clause three, or claim a general cursor or complete formula builder.
  The third-clause-second-literal audit checks the complete fixed 479-rule `F T T F`
  appender/cursor suffix behind one total bridge, all eight internal launches, the symbolic
  3004-rule global base, the exact canonical prefix through negative variable two in clause
  three, the direct `F`/`T`/`T`/`F` and following-`Finish` outcomes, the external polynomial,
  every malformed appender/cursor copy, all eight unlaunched endpoints, and one-step-short
  timeout. Its exact 145-line closure split is 46 empty, 32 `propext`, and 67
  `propext`/`Quot.sound` declarations; it does not emit `Finish`, complete clause three, or claim
  a general cursor or complete formula builder.
  The complete-third-clause audit checks the selected 59-rule `Finish` appender, both total
  launches, one fixed cursor advance, the exact 113-rule suffix and symbolic 3126-rule global
  base, the canonical formula prefix through the complete third clause, direct `Finish` execution,
  the retained first padding coordinate, the external polynomial, malformed phases, both
  unlaunched endpoints, and one-step-short timeout. Its exact 57-line closure split is 14 empty,
  10 `propext`, and 33 `propext`/`Quot.sound` declarations. The third-clause-padding audit checks
  both fixed unary evaluators, all three total `WorkChain` bridges, reuse rather than duplication
  of the 25-rule countdown, the symbolic 3178-rule global base, the exact `C - 8` positive count,
  every direct padding opportunity, the retained fourth-clause `Sep` coordinate, unchanged
  canonical output, the external polynomial, malformed countdown phases, the unlaunched
  predecessor endpoint, and one-step-short timeout. Its exact 68-line closure split is 26 empty,
  9 `propext`, and 33 `propext`/`Quot.sound` declarations; it does not emit clause four or claim a
  general cursor or complete formula builder.
  The fourth-clause-separator audit checks the reused selected 59-rule `Sep` appender and fixed
  45-rule cursor table, the reused inner launch and new outer total bridge, the exact 113-rule
  suffix and symbolic 3300-rule global base, the canonical output through clause four's opening
  separator, the retained following `F`, the external polynomial, malformed appender and cursor
  phases, both unlaunched endpoints, and one-step-short timeout. Its exact 56-line audit covers all
  48 new public declarations plus eight reused interfaces, with 14 empty, 11 `propext`, and 31
  `propext`/`Quot.sound` closures; it does not emit the following `F`, complete clause four, or
  claim a general cursor or complete formula builder.
  The fourth-clause-first-literal audit checks the reused 357-rule `F T F` suffix, all six
  launches, the symbolic 3666-rule global base, exact output through the first negative literal
  on variable one, the retained following `F`, the external polynomial, malformed tally/output/
  scratch phases, all six unlaunched endpoints, and one-step-short timeout. Its exact 115-line
  audit covers 97 new declarations, 16 reused suffix interfaces, and two dead-state facts, with
  33 empty, 25 `propext`, and 57 `propext`/`Quot.sound` closures; it does not emit the second
  literal, complete clause four, or claim a general cursor or complete formula builder.
  The fourth-clause-second-literal audit checks the reused 479-rule `F T T F` suffix, all eight
  launches, the symbolic 4154-rule global base, exact output through the complete negative literal
  on variable two, the retained following `Finish`, the external polynomial, malformed tally/
  output/scratch phases, all eight unlaunched endpoints, and one-step-short timeout. Its exact
  147-line audit covers 124 new declarations, 21 reused suffix interfaces, and two dead-state
  facts, with 46 empty, 32 `propext`, and 69 `propext`/`Quot.sound` closures; it does not emit the
  following `Finish`, complete clause four, or claim a general cursor or complete formula builder.
  The complete-fourth-clause audit checks the selected 59-rule `Finish` appender, fixed 45-rule
  cursor, both launches, exact 113-rule suffix and symbolic 4276-rule global base, exact output
  through the complete fourth clause, the retained first-padding coordinate, external polynomial,
  malformed appender and cursor phases, both unlaunched endpoints, and one-step-short timeout. Its
  exact 57-line audit covers 55 new public declarations and two dead-state facts, with 14 empty, 10
  `propext`, and 33 `propext`/`Quot.sound` closures; it does not traverse clause-four padding or
  claim a general cursor or complete formula builder.
  Each transcript has an exact declaration count,
  so a truncated audit fails closed. The five
  locked-NAND transcripts require exactly 48, 25, 23, 30, and 32 clean declarations; residual
  routes require 30. The workflow also checks the byte-identical inventory mirrors, derives the
  false concrete publication gate and status/report outputs, and verifies same-environment
  double-build determinism plus exact committed bytes for the current concise PDF. The
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

The sequential state-namespace audit checks two nested complete component tables rather than
individual stages. It requires disjoint outer images, isolated first-match lookup, exact local-run
transport, and the two literal first-verdict-to-second-simulator launches, with exactly 26 empty
axiom closures. CI does not treat those local facts as an end-to-end sequential compiler.

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

The current root PDF is the generated concise formal-reconstruction report. The historical
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
