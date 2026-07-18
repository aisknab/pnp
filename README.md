# pnp

**Public source and checker repository for a claimed proof that `P = NP`.**

> [!IMPORTANT]
> **Formal reconstruction is in progress. The repository does not currently establish `P = NP`,
> and public theorem emission is disabled.** The previous activated checker status has been
> withdrawn as proof authority because assertion-bearing records and trust objects do not replace
> derivations of their named mathematical propositions. See the
> [formal reconstruction notice](./docs/FORMAL_RECONSTRUCTION.md) and the active
> [machine-readable status](./status/FORMAL_RECONSTRUCTION_STATUS.json).

This repository contains the current Lean reconstruction, compiled theorem inventory,
fail-closed publication gate, generated nonclaiming canonical report, historical JavaScript checker
and replay records, tests, and reviewer documentation for a proposed
SAT-to-exact-NAND-minimization route. The claim is extraordinary and has not received independent
mathematical validation.

## Read this first

| Question | Current answer |
| --- | --- |
| **What is this repository?** | Source code, finite certificate records, checker and replay machinery, tests, release artefacts, and audit documentation for the author's claimed `P = NP` result. |
| **What extraordinary claim was proposed?** | The historical report claimed a deterministic polynomial-time SAT algorithm by reducing SAT to exact minimization of specially locked multi-output NAND words with residual slack at most four, then applying a claimed polynomial exact minimizer for that residual band. |
| **What is the current verification status?** | Formal reconstruction is in progress. Lean proves `PNP.Concrete.FinalUniversalDesign.cnfSATInNP : InNP CNFSAT` using a literal finite raw-machine verifier with an explicit polynomial bound. It recursively compiles every finite charged function/decision program into one literal raw machine, discharging `Formal.ConcreteComplexityMachineLink`. The concrete Cook–Levin formula is semantically equivalent to raw verifier execution; its canonical encoding has an explicit polynomial size bound and exact answer-independent schedule/cursor. The builder emits the canonical `T^FormulaWidth F Sep T F T T F T T T F Finish Sep F F F T F` prefix through the complete negative literal on variable one in clause two and retains the following `Finish` coordinate. Lean still does **not** emit that terminator, complete clause two, implement a general dynamic cursor or arbitrary raw slot decoder, emit the remaining formula body, provide a complete polynomial-time raw formula builder or concrete `PolynomialReduction`, prove `CNFSAT ∈ P`, prove NP-hardness/NP-completeness, or prove `P = NP`. `PNP.Main.p_eq_np` remains absent and the publication gate stays false. |
| **What can a hash check establish?** | That retrieved bytes match a published checksum ledger, subject to the hash implementation and collision assumptions. It does **not** establish theorem correctness, checker soundness, or correct generation. |
| **What can the checker establish?** | That the supplied records satisfy the predicates implemented by the named checker and its linkage rules. Checker acceptance does **not** independently establish that those predicates are mathematically sufficient or correctly implemented. |
| **What remains formally?** | The Lean toolchain/root, concrete machine kernel, all executable pipeline stages, the complete all-input and sequential compilers, recursive function/decision `RawRefinement`, the finite charged-pipeline P/NP/reduction interface, direct proof that `CNFSAT ∈ NP`, concrete Cook–Levin semantic equivalence, external formula-size and exact-width polynomials, rectangular schedule, direct formula cursor, literal input-length tally, raw-input prefix, unary polynomial evaluator, complete width-header and first-clause machines, one padding-coordinate cursor step, the complete remaining-padding run, and the first two complete negative literals of clause two, direct-wire layers, local locked-NAND baselines, conditional threshold deduction, and fail-closed explicit-list gain scanner are formalized and axiom-audited. Emitting the retained clause terminator, completing clause two, a general dynamic raw cursor/arbitrary slot decoder, remaining formula-body emission, composition into a complete raw formula builder with a construction-runtime polynomial, a concrete CNFSAT reduction and NP-hardness/NP-completeness proof, a deterministic decider proving `CNFSAT ∈ P`, global locked-NAND construction and threshold, residual-band minimization, global `ZeroSlack`, assumption elimination, and root-theorem audit remain. `PNP.Main.ConcretePEqualsNP` is only an inactive definition; `PNP.Main.p_eq_np` is absent. |
| **What is the current canonical report?** | The root TeX/PDF is a generated, concise formal-reconstruction report with theorem emission disabled. The historical 56-page claim manuscript is available only at the pinned legacy coordinate recorded under `archive/legacy-v0/`. |
| **How do I run the current verification?** | Run `npm ci --ignore-scripts` and `npm run pnp:verify -- --no-write`. This checks the non-claiming formal status, current package surface, pinned archive identity, and the small current-authority test suite; it is not a proof verification. |
| **Where should reviewers start?** | Start with the current-authority [compiled Lean theorem inventory](./docs/lean_theorem_inventory.md) and [formal reconstruction notice](./docs/FORMAL_RECONSTRUCTION.md). The reviewer guide, proof pipeline, terminology crosswalk, trust model, and audit questions are historical checker-route review aids whose numbered report citations target the pinned 56-page manuscript. |

## Current claim boundary

The project targets:

```text
P = NP
```

The target is not currently established. Legacy checker records preserve the earlier conditional
assertion and its replay history, but neither those records nor their hashes are active theorem
authority. Future public theorem emission requires the concrete, assumption-audited Lean gate in
[the reconstruction notice](./docs/FORMAL_RECONSTRUCTION.md).

The completed concrete CNF layer is a verifier result: a finite raw machine decides whether a
supplied bounded assignment certificate satisfies a canonically encoded CNF formula. Universal
machine correctness and the explicit polynomial runtime bound prove `CNFSAT ∈ NP`. Existentially
guessing a certificate is not a deterministic polynomial-time SAT algorithm, so this result does
not prove `CNFSAT ∈ P`, NP-hardness, NP-completeness, or `P = NP`.

The framed simulator is a local configuration theorem. If `rawRunExact?` supplies `n` successful
raw transitions and the starting work tape satisfies `PipelineTape.Represents`, Lean constructs
exactly `3 * n` successful work steps to a represented endpoint. For an ordinary raw `run` with
fuel `F`, Lean extracts an exact successful prefix of some length `k ≤ F` reaching the same
endpoint. If that endpoint is a designated accept or reject state, `workRun` with fuel
`3 * F` and compiled raw `run` with fuel `18 * F` reach its representation and encoding. This is
conditional padding, not a termination theorem: `3 * F` and `18 * F` are at-most budgets, not
successful-transition counts, and a stuck nonhalting endpoint is not a verdict. It does not connect
canonical `Tape.ofInput` to the frame inside the simulator theorem or prove target termination. The
separate bridge module composes every supplied exact run with the paired-input framer and a
verdict-indexed internal handoff, preserving accept/reject and reporting a supplied stuck
nonhalting endpoint as timeout at the exact prefix budget. Its cost still depends on the supplied
source-transition count and final output length, and the two-track blank tags are not a canonical
`machineOutput` encoding or an external-input-size polynomial.

The input framer is a separate executable machine. Its all-input theorem starts from ordinary
`startConfig (compileWorkMachine pairedInputFramer) input`, handles empty input, complete two-bit
work cells, and an odd final raw bit through literal transitions, and reaches a represented frame
with permitted exterior garbage. Its exact work costs are `4` for empty input,
`4 * k * k + 9 * k + 7` for `k` complete cells, and `4 * k * k + 9 * k + 5` when the final cell is
partial. The compiled run accepts without timeout within `6 * m * m + 39 * m + 75` for raw length
`m`. The earlier canonical-pair theorem retains its sharper exact bound `6 * m * m + 27 * m + 42`.
`PipelineCompiler` now consumes this endpoint. For every raw bitstring it composes the same literal
framer, simulator, represented-output handoff, and terminal packer table used by the paired
compiler. From the target's proof-bearing termination theorem it extracts an exact target prefix,
preserves accept/reject/timeout classification and ordinary `machineOutput`, and proves no timeout
at an explicit external-input-size polynomial. Thus empty, odd, even, and other non-pair words are
covered by the complete raw pipeline, not merely by the local framer.

The internal output handoff is another separate executable machine. From an already represented
logical tape `raw`, it retains the prefix `raw.outputBits`, installs a fresh represented frame for
`raw.handoffTarget`, and halts accepting after exactly `2 * raw.outputBits.length + 4` work steps.
The compiled theorem uses exactly `12 * raw.outputBits.length + 24` steps, but starts from
`encodeWorkConfiguration` of the internal represented configuration. The bridge module launches
simulator accept and reject sentinels into two disjoint copies and compiles that cumulative trace
from ordinary paired `startConfig`. The new terminal bridge extends the finite rule table with two
further disjoint packer copies and, from either represented handoff endpoint, proves one exact
launch, exact terminal packing, distinct terminal verdicts, and raw-visible output equality under
the local bound `18*n^2 + 36*n + 12`. It also preserves every successful earlier bridge trace in
`terminalBridgeMachine` and composes a complete four-stage trace for each caller-supplied exact
accepting or rejecting target execution. `PipelinePairedCompiler` obtains target termination on
canonical pairs. Its successor `PipelineCompiler` proves the corresponding result on every raw
bitstring with output bound `B(m) = m + p(m) + 1` and complete runtime bound
`R(m) = totalInputFramerRawTimeBound(m) + 6 + 18*p(m) + 6 +
framedOutputHandoffRawTimeBound(B(m)) + terminalBridgeRawTimeBound(B(m))`. This wraps one
already-raw `PolynomialTimeMachine`; it does not yet compile recursive charged function/decision
program composition into the `RawRefinement` contracts.

The next composition layer now nests two such component machines in pairwise-disjoint outer state
images. `PipelineSequentialStateNamespace` proves injective renaming, first-match lookup isolation,
exact local-trace transport, and literal accept/reject launches from the first component into the
second component's internal simulator start. This is the namespace and dispatch milestone only:
an end-to-end two-machine trace, terminal output theorem, external polynomial, and recursive
`RawRefinement` constructors remain to be proved.

## Quick start for reviewers

Requirements: Node.js 20 or newer and npm 10 or newer.

```bash
git clone https://github.com/aisknab/pnp.git
cd pnp
npm ci --ignore-scripts
npm run pnp:verify -- --no-write
```

The verifier must keep every theorem-status flag false while checking the current status/surface and
the byte-exact archive coordinates. Success does not validate the general mathematics.

Run the current-tree validation suite with:

```bash
npm run validate
```

For the frozen 7072f8d release, use the designated command in
[`REPRODUCE.md`](./REPRODUCE.md). Current `main` intentionally runs a small authority-and-archive
suite; it must not be confused with the frozen 1,121-test source release.

## What each verification layer means

| Layer | Command or artefact | What success establishes | What success does not establish |
| --- | --- | --- | --- |
| Current test suite | `npm test` | The formal status, package boundary, archive pins, and replay guards pass in the selected environment. | Legacy checker validation, exhaustive correctness, or polynomial asymptotics. |
| Pinned Lean root | `lake build PNP` and `lake env lean -DwarningAsError=true lean-audit/PNPBridgeAxiomAudit.lean` | Lean 4.31.0 compiles the explicit `PNP` root; the non-theorem root-status data is assumption-free; the conditional bridge's dependencies are printed. | A root theorem or a proof of `P = NP`; four disclosed project-specific axioms remain. |
| Compiled theorem inventory | `node scripts/export-lean-theorem-inventory.mjs --check` | `Lean.Environment.constants` and `Lean.collectAxioms` reproduce the canonical, byte-identical status and public inventory mirrors from the compiled `PNP` environment. Declaration, theorem, module, and private-auxiliary counts come from that generated inventory rather than this prose. | Source-level proof review, a general compiler/refinement from charged pipelines to raw machines, or a publication-eligible theorem. |
| Concrete publication gate and report | `node scripts/generate-formal-publication.mjs --check` and `npm run report:check` | Status and the concise canonical report match the compiled inventory and the false, fail-closed gate. | `P = NP`, permission to emit a theorem, or validation of the historical claim report. |
| Concrete machine and cost kernel | `lean-audit/PNPConcreteBitStringAxiomAudit.lean`, `lean-audit/PNPConcreteMachineAxiomAudit.lean`, and `audits/lean-concrete-machine0.test.mjs` | Canonical bitstring codecs, natural-polynomial syntax, finite rule-list machine semantics, bounded execution, and proof-bearing deterministic runtime witnesses are axiom-free. | The general charged-pipeline interface's compiler/refinement to one raw machine, `CNFSAT ∈ P`, NP-completeness, or `P = NP`. |
| Blank-delimited output and pure handoff target | `lean-audit/PNPConcreteTapeHandoffAxiomAudit.lean` and `audits/lean-concrete-tape-handoff0.test.mjs` | Output stops at the first observable blank; canonical input round trips, explicit/implicit boundaries agree, head-movement round trips preserve output, and the pure canonical handoff target preserves output idempotently. | The target is not an executable normalization/handoff machine and supplies no boundary frame, state reset, composition compiler, runtime theorem, class equivalence, or `P = NP`. |
| Blank-materialization equivalence | `lean-audit/PNPConcreteTapeBlankEquivalenceAxiomAudit.lean` and `audits/lean-concrete-tape-blank-equivalence0.test.mjs` | Finite tapes with different materialized exterior blanks have identical raw execution and observable output; every empty, odd, or even raw input agrees with its packed work view. | This theorem is representation invariance. The input framer now consumes it, but it does not itself establish complete pipeline refinement, a class result, or `P = NP`. |
| Boundary-marked pipeline tape geometry | `lean-audit/PNPConcretePipelineTapeGeometryAxiomAudit.lean` and `audits/lean-concrete-pipeline-tape-geometry0.test.mjs` | Two-track data and distinct left/right markers represent every raw tape with arbitrary exterior garbage; writes, interior moves, and empty-side boundary expansions preserve the representation. | These are pure tape identities, not transition rules, a handoff machine, compiler, runtime proof, class equivalence, or `P = NP`. |
| Executable all-input framer | `lean-audit/PNPConcretePipelineInputFramerAxiomAudit.lean` and `audits/lean-concrete-pipeline-input-framer0.test.mjs` | One literal finite work machine handles every raw bitstring, including empty and odd inputs; reaches a represented boundary frame; proves exact branch costs, the uniform bound `6*m^2 + 39*m + 75`, ordinary-start acceptance/no-timeout, and 70 empty axiom closures. | This module itself ends at the frame. `PipelineCompiler` consumes the endpoint, but general charged-program refinement and class results remain outside the framer theorem. |
| Executable internal represented-output handoff | `lean-audit/PNPConcretePipelineOutputHandoffAxiomAudit.lean` and `audits/lean-concrete-pipeline-output-handoff0.test.mjs` | One literal finite work machine turns an already represented tape into a represented `Tape.handoffTarget`, preserves blank-delimited logical output, halts accepting, and has exact `2 * n + 4` work and `12 * n + 24` compiled costs. | Its theorem is an internal-stage result. The terminal and all-input compilers consume it; this module alone does not prove target termination, an external polynomial, or charged-program refinement. |
| Collision-free pipeline state namespace | `lean-audit/PNPConcretePipelineStateNamespaceAxiomAudit.lean` and `audits/lean-concrete-pipeline-state-namespace0.test.mjs` | Injective renaming preserves first-match lookup and execution; three disjoint stage images give a lookup-isolated rule namespace. | This module is the namespace prerequisite; launch execution is proved separately and terminal output/refinement remain missing. |
| Sequential pipeline component namespace | `lean-audit/PNPConcretePipelineSequentialStateNamespaceAxiomAudit.lean` and `audits/lean-concrete-pipeline-sequential-state-namespace0.test.mjs` | Two complete component rule tables occupy disjoint outer images; first-match dispatch and exact local traces are preserved, and both first-component verdicts launch the second simulator literally. All 26 audited declarations have empty axiom closure. | No end-to-end two-machine run, terminal output equality, external polynomial, or recursive `RawRefinement` is claimed. |
| Executable verdict-preserving stage bridges | `lean-audit/PNPConcretePipelineStageBridgesAxiomAudit.lean` and `audits/lean-concrete-pipeline-stage-bridges0.test.mjs` | One finite bridge-first work machine launches framer to simulator and simulator accept/reject to disjoint handoff copies, preserves ordinary stage dispatch and bounded verdicts, composes supplied exact target traces, and compiles from canonical paired raw input at exactly six times the cumulative work cost. | It assumes a supplied exact target run and ends in internal represented output. Later modules supply the terminal suffix, target termination, and external polynomial; this module itself does not prove charged-program refinement or a complexity-class result. |
| Executable terminal raw-output packer | `lean-audit/PNPConcreteTerminalOutputPackerAxiomAudit.lean` and `audits/lean-concrete-terminal-output-packer0.test.mjs` | One literal finite work machine uniformly packs every logical output word, including empty/odd/even edge cases and arbitrary exterior garbage, into ordinary blank-delimited raw output. It proves exact work and compiled traces, halt/output equality, local bound `18*n^2 + 36*n + 6`, and one-step-short timeout; all 69 public declarations have empty axiom closure. | It starts from an encoded internal configuration. Later modules supply launches, target termination, and an external polynomial; this local theorem does not itself provide charged-program refinement, a class result, or `P = NP`. |
| Executable handoff-to-terminal bridge | `lean-audit/PNPConcretePipelineTerminalBridgeAxiomAudit.lean` and `audits/lean-concrete-pipeline-terminal-bridge0.test.mjs` | One extended finite rule table contains both earlier bridge rules and two disjoint packer copies. It preserves all successful earlier bridge steps and, for each supplied exact accepting or rejecting target run, proves a complete trace from ordinary paired input, the exact verdict, six-for-one compiled execution, raw output equality, and the local suffix bound `18*n^2 + 36*n + 12`; all 59 public declarations have empty axiom closure. | The theorem requires a caller-supplied exact target execution. Downstream compiler/refinement modules supply target termination, every-input behavior, an external polynomial, and recursive charged-program refinement; CNF-SAT class results and `P = NP` remain absent. |
| All-input four-stage compiler | `lean-audit/PNPConcretePipelineCompilerAxiomAudit.lean`, `lean-regression/PNPConcretePipelineCompiler.lean`, and `audits/lean-concrete-pipeline-compiler0.test.mjs` | The same literal compiled table handles every raw bitstring for an already-raw `PolynomialTimeMachine`; target termination is extracted internally, verdict and ordinary output are exact, timeout is excluded at the explicit polynomial bound, stuck nonhalting prefixes remain timeout, and all 29 public declarations have empty axiom closure. | This module supplies one raw target wrapper. The recursive refinement layer consumes it, but neither module proves `CNFSAT ∈ P`, NP-completeness, or `P = NP`. |
| Local framed raw-machine simulation | `lean-audit/PNPConcretePipelineMachineSimulationAxiomAudit.lean` and `audits/lean-concrete-pipeline-machine-simulation0.test.mjs` | Ordered finite rules preserve raw first-match selection, omit terminal-source entries, shift markers across arbitrary exterior garbage, lift every supplied exact `n`-step successful raw execution to exactly `3 * n` successful work steps, and extract a `k ≤ F` exact prefix from an ordinary `F`-fuel raw run. If its endpoint is designated halting, `workRun` with fuel `3 * F` and compiled `run` with fuel `18 * F` reach the representation and encoding. | It starts from an already represented frame and does not prove that the raw run halts. The full budgets are not successful-step counts or input-size bounds; a stuck nonhalting endpoint is not a verdict. It supplies no frame creator, `boundedDecide` or output theorem, connection to the separate handoff machine, composition/precomposition refinement, input-size polynomial end-to-end bound, class equivalence, or `P = NP`. |
| Finite charged-pipeline P/NP interface | `lean-audit/PNPConcreteComplexityAxiomAudit.lean`, `lean-audit/PNPConcreteTargetAxiomAudit.lean`, and `audits/lean-concrete-complexity0.test.mjs` | Finite machine-leaf function/decision syntax, polynomial runtime/output/certificate bounds, canonical paired verification, P contained in NP, polynomial-reduction closure, the NP-complete-in-P implication, and the inactive concrete target are axiom-free. | The machine link is now compiled downstream, but `CNFSAT ∈ P`, concrete NP-hardness, a root theorem, gate activation, and `P = NP` remain absent. |
| Recursive raw charged-pipeline refinement | `lean-audit/PNPConcretePipelineRefinementAxiomAudit.lean`, `lean-regression/PNPConcretePipelineRefinementRecursive.lean`, and `audits/lean-concrete-pipeline-refinement0.test.mjs` | Exact machine leaves, literal two-machine function composition and decision precomposition, recursive compilation of every finite program tree, exact output/verdict preservation, and `PolynomialTimeDecider.compileToMachine` are axiom-free across all 16 public declarations. The recursive bound uses `PipelineRaw(p)(m) + 6 + PipelineRaw(q)(m + p(m) + 1)` at each composition node. | This closes `Formal.ConcreteComplexityMachineLink` only. It does not establish `CNFSAT ∈ P`, CNF-SAT NP-completeness, or `P = NP`; the publication gate remains false. |
| Direct concrete CNF verifier | `node --test audits/lean-concrete-cnf0.test.mjs` plus the four `PNPConcreteCNF*AxiomAudit.lean` transcripts | Canonical CNF and assignment codecs, bounded certificate semantics, exact paired-tape compilation, universal accept/reject/no-timeout correctness for a finite raw machine, an explicit polynomial runtime bound, and `PNP.Concrete.FinalUniversalDesign.cnfSATInNP : InNP CNFSAT` are axiom-free. | A deterministic polynomial-time CNF-SAT decider, `CNFSAT ∈ P`, NP-hardness, NP-completeness, or `P = NP`. |
| External Cook–Levin encoded-formula size | `lean-audit/PNPConcreteCookLevinFormulaSizeAxiomAudit.lean`, `lean-regression/PNPConcreteCookLevinFormulaSize.lean`, and `audits/lean-concrete-cook-levin-formula-size0.test.mjs` | Exact canonical codec lengths and all concrete tableau constraint families yield an explicit fixed-verifier polynomial bounding `BitString.size problem.encodedFormula` solely in `BitString.size problem.input`; a second mode-sensitive polynomial evaluates exactly to `problem.FormulaWidth`. Both verifier input modes are covered, and all 110 declarations reach only `propext` and `Quot.sound`. | A raw finite formula builder, a construction-runtime polynomial, a concrete `PolynomialReduction`, CNFSAT NP-completeness, CNFSAT in P, or `P = NP`. |
| Rectangular Cook–Levin formula schedule | `lean-audit/PNPConcreteCookLevinFormulaScheduleAxiomAudit.lean`, `lean-regression/PNPConcreteCookLevinFormulaSchedule.lean`, and `audits/lean-concrete-cook-levin-formula-schedule0.test.mjs` | Exact answer-independent constraint, clause, token, and raw-bit rectangles reproduce the existing canonical program and encoding after empty slots are filtered. The raw-bit slot count equals `encodedFormulaSizePolynomial` at external input length; all 79 declarations reach only `propext` and `Quot.sound`. | Treating a slot as constant-time execution, a raw formula builder, a construction-runtime polynomial, `RawRefinement`, a concrete `PolynomialReduction`, CNFSAT NP-completeness, CNFSAT in P, or `P = NP`. |
| Direct Cook–Levin formula cursor | `lean-audit/PNPConcreteCookLevinFormulaCursorAxiomAudit.lean`, `lean-regression/PNPConcreteCookLevinFormulaCursor.lean`, and `audits/lean-concrete-cook-levin-formula-cursor0.test.mjs` | Direct constraint, clause, token, and bit decoders preserve out-of-range versus valid-padding semantics and agree pointwise with the canonical schedules. Exact prefix, full, one-step-short, terminal, and excess-fuel bit-cursor theorems yield the canonical encoded output; a token-level cursor exposes exact in-range, done, and terminal step laws. All 136 declarations reach only `propext` and `Quot.sound`. | Constant-time raw interpretation, a raw finite formula builder, a construction-runtime polynomial, `RawRefinement`, a concrete `PolynomialReduction`, CNFSAT NP-completeness, CNFSAT in P, or `P = NP`. |
| Literal Cook–Levin input-length tally | `lean-audit/PNPConcreteCookLevinBuilderInputLengthAxiomAudit.lean`, `lean-regression/PNPConcreteCookLevinBuilderInputLength.lean`, and `audits/lean-concrete-cook-levin-builder-input-length0.test.mjs` | One fixed 19-rule machine preserves every source bit, appends an exact unary length tally in fresh workspace, accepts in `2*n^2 + 4*n + 2` work steps, compiles to exactly `12*n^2 + 24*n + 12` raw steps, times out on malformed scan symbols and one-step-short fuel, and connects definitionally to the all-input framer endpoint. All 39 public declarations reach only `propext` and `Quot.sound`. | Formula-bit emission, raw cursor interpretation, a complete builder or `RawRefinement`, a concrete `PolynomialReduction`, CNFSAT NP-completeness, CNFSAT in P, or `P = NP`. |
| Executable Cook–Levin builder input prefix | `lean-audit/PNPConcreteCookLevinBuilderInputPrefixAxiomAudit.lean`, `lean-regression/PNPConcreteCookLevinBuilderInputPrefix.lean`, and `audits/lean-concrete-cook-levin-builder-input-prefix0.test.mjs` | One collision-free finite table composes the total raw-input framer, a total nine-symbol launch, and the fixed unary tally. Every `BitString` reaches the exact preserved-input tally endpoint within `18*n^2 + 63*n + 93` compiled steps; a scan configuration headed by the unused `zeroOne` symbol and one-step-short fuel time out. All 40 public declarations reach only `propext` and `Quot.sound`. | Formula-bit emission, raw cursor interpretation, a complete builder or construction-time `RawRefinement`, a concrete `PolynomialReduction`, CNFSAT NP-completeness, CNFSAT in P, or `P = NP`. |
| Standalone Cook–Levin builder token appender | `lean-audit/PNPConcreteCookLevinBuilderTokenAppenderAxiomAudit.lean`, `lean-regression/PNPConcreteCookLevinBuilderTokenAppender.lean`, and `audits/lean-concrete-cook-levin-builder-token-appender0.test.mjs` | One fixed 59-rule state-selected machine appends any of the four canonical two-bit CNF tokens after the exact tally while preserving the source and arbitrary exterior garbage. Its start state appends the first `T` header token within `24*n + 48` compiled steps and proves those bits equal the first two direct/canonical Cook–Levin formula bits; malformed phases and one-step-short fuel time out. All 68 declarations reach only `propext` and `Quot.sound`. | This module audits the appender independently of its composed use. The remaining header, dynamic cursor interpreter, complete builder, construction-time `RawRefinement`, concrete `PolynomialReduction`, CNFSAT NP-completeness, CNFSAT in P, and `P = NP` remain absent. |
| Composed Cook–Levin first-token prefix | `lean-audit/PNPConcreteCookLevinBuilderFirstTokenPrefixAxiomAudit.lean`, `lean-regression/PNPConcreteCookLevinBuilderFirstTokenPrefix.lean`, and `audits/lean-concrete-cook-levin-builder-first-token-prefix0.test.mjs` | One literal 184-rule machine places all 116 input-prefix rules and all 59 appender rules in disjoint injective state images behind nine total bridge rules. Every raw `BitString` reaches the preserved input/tally workspace containing exactly `[T]`; its two bits equal `encodedFormula.take 2`, and the compiled run is bounded by `18*n^2 + 87*n + 147`. All 37 declarations reach only `propext` and `Quot.sound`. | Exactly two fixed formula bits are emitted. The rest of the width header, dynamic cursor, complete builder, builder `RawRefinement`, concrete `PolynomialReduction`, CNFSAT NP-completeness, CNFSAT in P, and `P = NP` remain absent. |
| Composed Cook–Levin complete width header | `lean-audit/PNPConcreteCookLevinBuilderUnaryPolynomialAxiomAudit.lean`, `lean-audit/PNPConcreteCookLevinBuilderCompleteHeaderAxiomAudit.lean`, `lean-regression/PNPConcreteCookLevinBuilderCompleteHeader.lean`, and `audits/lean-concrete-cook-levin-builder-complete-header0.test.mjs` | A literal unary evaluator compiles the verifier-fixed width polynomial without calling `NatPolynomial.eval` from executable rules. One finite table with `363 + evaluator.ruleCount` rules composes it with the raw-input/first-token prefix, five total bridges, a 16-rule controller, and two 59-rule appenders. Every raw input emits exactly `T` repeated `FormulaWidth` times followed by `F`; those bits equal the complete canonical width header, and the compiled trace is bounded by an external `NatPolynomial`. The evaluator's 74 and composition's 84 public declarations reach only `propext` and `Quot.sound`. | Dynamic raw cursor/body emission, a complete formula builder or builder `RawRefinement`, a concrete `PolynomialReduction`, CNFSAT NP-completeness, CNFSAT in P, and `P = NP` remain absent. |
| Composed Cook–Levin body-start prefix | `lean-audit/PNPConcreteCookLevinBuilderBodyStartPrefixAxiomAudit.lean`, `lean-regression/PNPConcreteCookLevinBuilderBodyStartPrefix.lean`, and `audits/lean-concrete-cook-levin-builder-body-start-prefix0.test.mjs` | One literal table with `440 + Unary.ruleCount(widthPolynomial) + Unary.ruleCount(nextTokenSlotPolynomial)` rules composes the complete header, a unary next-slot evaluator, two total nine-symbol bridges, and a 59-rule separator appender in disjoint state images. Every raw input emits exactly `T^FormulaWidth F Sep`, retains token coordinate `FormulaVariableSlotBound + 2` and its doubled bit cursor, and obeys the external compiled bound `CompleteHeader.rawTimeBound + 72 + 6*Unary.workSteps(nextTokenSlotPolynomial) + 24*n + 12*width`. All 60 public declarations reach only `propext` and `Quot.sound`. | The retained coordinate is data, not a dynamic cursor. Subsequent body emission, a complete builder or builder `RawRefinement`, a concrete `PolynomialReduction`, CNFSAT NP-completeness, CNFSAT in P, and `P = NP` remain absent. |
| Composed Cook–Levin first-literal prefix | `lean-audit/PNPConcreteCookLevinBuilderFirstLiteralPrefixAxiomAudit.lean`, `lean-regression/PNPConcreteCookLevinBuilderFirstLiteralPrefix.lean`, and `audits/lean-concrete-cook-levin-builder-first-literal-prefix0.test.mjs` | One literal table with `585 + Unary.ruleCount(widthPolynomial) + Unary.ruleCount(bodyStartNextSlotPolynomial) + Unary.ruleCount(firstLiteralNextSlotPolynomial)` rules composes the complete body-start prefix, a unary next-slot evaluator, three total nine-symbol bridges, and fixed `T`/`F` appenders in four disjoint state images. Every raw input emits exactly `T^FormulaWidth F Sep T F`, constructively pins the final pair to positive variable zero, retains token coordinate `FormulaVariableSlotBound + 4` and its doubled bit cursor, and obeys the external compiled bound `BodyStartPrefix.rawTimeBound + 174 + 6*Unary.workSteps(nextTokenSlotPolynomial) + 48*n + 24*width`. Its 74 public declarations, including halt-source separation for safe downstream composition, reach only `propext` and `Quot.sound`. | The retained coordinate is data, not a dynamic cursor. Remaining body emission, a complete builder or builder `RawRefinement`, a concrete `PolynomialReduction`, CNFSAT NP-completeness, CNFSAT in P, and `P = NP` remain absent. |
| Composed Cook–Levin complete first-clause prefix | `lean-audit/PNPConcreteCookLevinBuilderFirstClausePrefixAxiomAudit.lean`, `lean-regression/PNPConcreteCookLevinBuilderFirstClausePrefix.lean`, and `audits/lean-concrete-cook-levin-builder-first-clause-prefix0.test.mjs` | One literal table with `1138` plus four unary-evaluator rule counts composes the complete first-literal prefix, a fresh next-coordinate evaluator, and a fixed 535-rule eight-token tail. Every raw input emits exactly `T^FormulaWidth F Sep T F T T F T T T F Finish`, constructively identifies the three literals as positive variables zero, one, and two, retains token coordinate `FormulaVariableSlotBound + 12`, and proves its direct outcome is valid padding. The compiled bound evaluates to `FirstLiteralPrefix.rawTimeBound + 1158 + 6*Unary.workSteps(next) + 192*n + 96*width`. All 79 new declarations, and the 80-declaration combined audit including the predecessor separation theorem, reach only the approved Lean-standard closure. | Exactly the first canonical clause is emitted. The retained coordinate alone is data, not a dynamic cursor. Remaining body emission, a complete builder or builder `RawRefinement`, a concrete `PolynomialReduction`, CNFSAT NP-completeness, CNFSAT in P, and `P = NP` remain absent. |
| Literal Cook–Levin token-cursor padding step | `lean-audit/PNPConcreteCookLevinBuilderDynamicTokenCursorStepAxiomAudit.lean`, `lean-regression/PNPConcreteCookLevinBuilderDynamicTokenCursorStep.lean`, and `audits/lean-concrete-cook-levin-builder-dynamic-token-cursor-step0.test.mjs` | One literal table with `1192` plus the four inherited unary-evaluator rule counts composes the complete first clause, nine launch rules, and a fixed 45-rule cursor advance. Every raw input preserves the formula output, consumes the proved first in-range padding opportunity, and changes the retained unary coordinate from `FormulaVariableSlotBound + 12` to `+ 13`. The suffix costs exactly `2*cursorWord.length + 8` work steps including launch and fits `FirstClausePrefix.rawTimeBound + 48 + 12*cursorWord.length` compiled steps. All 47 public declarations, including two reviewed dead-state dispatch facts, reach only `propext` and `Quot.sound`. | This is one padding transition, not a general dynamic cursor loop or arbitrary raw slot decoder. It emits no token and supplies no remaining body, complete builder, builder `RawRefinement`, concrete `PolynomialReduction`, CNFSAT NP-completeness, CNFSAT in P, or `P = NP`. |
| Cook–Levin first-clause remaining-padding run | `lean-audit/PNPConcreteCookLevinBuilderFirstClausePaddingRunAxiomAudit.lean`, `lean-regression/PNPConcreteCookLevinBuilderFirstClausePaddingRun.lean`, and `audits/lean-concrete-cook-levin-builder-first-clause-padding-run0.test.mjs` | One literal table with `1244` plus six unary-evaluator rule counts composes the prior cursor step, three total bridges, two new evaluators, and a fixed 25-rule countdown loop. For `V = formulaVariableSlotBound`, every raw input traverses exactly `(V-1)*(V+6) = formulaTokensPerClause-12` proved padding opportunities and materializes coordinate `V+1+formulaTokensPerClause`, whose direct outcome is the second clause's `Sep`. The output remains the exact first-clause prefix. The complete 84-declaration audit reaches only `propext` and `Quot.sound`. | This consumes one specifically proved padding block but does not emit clause two or implement a general dynamic cursor/arbitrary decoder, remaining body, complete builder, builder `RawRefinement`, concrete `PolynomialReduction`, CNFSAT NP-completeness, CNFSAT in P, or `P = NP`. |
| Cook–Levin second-clause separator step | `lean-audit/PNPConcreteCookLevinBuilderSecondClauseSeparatorStepAxiomAudit.lean`, `lean-regression/PNPConcreteCookLevinBuilderSecondClauseSeparatorStep.lean`, and `audits/lean-concrete-cook-levin-builder-second-clause-separator-step0.test.mjs` | One literal table with `1366` plus six unary-evaluator rule counts composes the complete padding run, a selected 59-rule `Sep` appender, two total bridges, and the fixed 45-rule cursor advance. Every raw input emits `T^FormulaWidth F Sep T F T T F T T T F Finish Sep`, advances the retained coordinate by one, proves the following direct token is `F`, and runs within `BuilderFirstClausePaddingRun.rawTimeBound + 246 + 24*n + 12*FormulaWidth + 12*cursorWord.length`. The 56-declaration combined audit has exactly 15 empty, 11 `propext`, and 30 `propext`/`Quot.sound` closures. | This emits only the separator beginning clause two. It does not emit the following `F`, implement a general dynamic cursor/arbitrary decoder, supply the remaining body, complete builder, builder `RawRefinement`, concrete `PolynomialReduction`, CNFSAT NP-completeness, CNFSAT in P, or `P = NP`. |
| Cook–Levin second-clause first negative literal | `lean-audit/PNPConcreteCookLevinBuilderSecondClauseFirstLiteralPrefixAxiomAudit.lean`, `lean-regression/PNPConcreteCookLevinBuilderSecondClauseFirstLiteralPrefix.lean`, and `audits/lean-concrete-cook-levin-builder-second-clause-first-literal-prefix0.test.mjs` | One literal table with `1610` plus six unary-evaluator rule counts composes the separator prefix, two selected 59-rule `F` appenders, four total bridges, and two fixed 45-rule cursor advances. Every raw input emits `T^FormulaWidth F Sep T F T T F T T T F Finish Sep F F`, retains the next negative-sign coordinate, and runs within `BuilderSecondClauseSeparatorStep.rawTimeBound + 564 + 48*n + 24*FormulaWidth + 24*cursorWord.length`. The 87-declaration combined audit has exactly 25 empty, 18 `propext`, and 44 `propext`/`Quot.sound` closures. | This completes only negative variable zero in clause two. It does not emit the next literal sign, complete clause two, implement a general dynamic cursor/arbitrary decoder, supply the remaining body, complete builder, builder `RawRefinement`, concrete `PolynomialReduction`, CNFSAT NP-completeness, CNFSAT in P, or `P = NP`. |
| Cook–Levin second-clause second negative literal | `lean-audit/PNPConcreteCookLevinBuilderSecondClauseSecondLiteralPrefixAxiomAudit.lean`, `lean-regression/PNPConcreteCookLevinBuilderSecondClauseSecondLiteralPrefix.lean`, and `audits/lean-concrete-cook-levin-builder-second-clause-second-literal-prefix0.test.mjs` | One literal table with `1976` plus six unary-evaluator rule counts composes the first-literal prefix, selected 59-rule `F`, `T`, and `F` appenders, six total bridges, and three fixed 45-rule cursor advances. Every raw input emits `T^FormulaWidth F Sep T F T T F T T T F Finish Sep F F F T F`, retains the following `Finish` coordinate, and runs within `BuilderSecondClauseFirstLiteralPrefix.rawTimeBound + 1026 + 72*n + 36*FormulaWidth + 36*cursorWord.length`. The 115-declaration combined audit has exactly 34 empty, 25 `propext`, and 56 `propext`/`Quot.sound` closures. | This completes only negative variable one in clause two. It does not emit the clause terminator, complete clause two, implement a general dynamic cursor/arbitrary decoder, supply the remaining body, complete builder, builder `RawRefinement`, concrete `PolynomialReduction`, CNFSAT NP-completeness, CNFSAT in P, or `P = NP`. |
| Direct-wire NAND semantics | `lake env lean -DwarningAsError=true lean-audit/PNPNANDSemanticsAxiomAudit.lean` | The typed topological NAND syntax, Boolean evaluation, output-wiring laws, and small semantic examples are assumption-free. | Enumeration, minimum size, replacement/slack, the locked builder or threshold, SAT, or `P = NP`. |
| Exact-width NAND enumerator | `lake env lean -DwarningAsError=true lean-audit/PNPNANDEnumeratorAxiomAudit.lean` | Every typed source, ordered gate, topological program, and output tuple appears; every existing program/word pair has an enumerated reification with the same program and pointwise output sources. | Canonical or duplicate-free enumeration, semantic equivalence, minimum size, replacement/slack, threshold, SAT, or `P = NP`. |
| Exhaustive direct-wire reference minimum | `lake env lean -DwarningAsError=true lean-audit/PNPNANDMinimumAxiomAudit.lean` | Finite truth tables decide semantic equivalence; exact candidate sizes are scanned from zero through the target size; the selected size has an equivalent witness and is a global lower bound; residual slack is zero exactly at semantic minimum. | Any practical or polynomial runtime, the report's residual-band minimizer, locked-NAND threshold, SAT, or `P = NP`. |
| Concrete framed replacement/slack | `lake env lean -DwarningAsError=true lean-audit/PNPNANDSlackAxiomAudit.lean` | Serial environment/support/continuation frames preserve equivalent support replacement and expose the corresponding additive slack identity. | Arbitrary support subsets/profiles, the report's global replacement theorem, or the locked-NAND family. |
| Local locked-NAND baseline bridge | `node --test audits/lean-locked-nand-baseline0.test.mjs` plus the four locked-baseline Lean axiom transcripts | Six typed local candidates have honest output widths and constant-free internal programs; semantic outputs inject into gates; counts come from typed sources; the five square local macros have exact empty-context minima. | A global square baseline candidate, cross-instance `BaselineDistinct`, the locked builder or threshold, residual slack at most four, polynomiality, SAT, or `P = NP`. |
| Conditional locked-NAND threshold boundary | `node --test audits/lean-locked-nand-threshold-boundary0.test.mjs` and `lean-audit/PNPLockedNANDThresholdBoundaryAxiomAudit.lean` | From actual typed candidates plus six explicit semantic premises, Lean derives the conditional unsat/sat minimum boundary and conditional residual slack at most four. | Instantiation of those premises, the report threshold theorem, global carrier layout or `BaselineDistinct`, `TraceEquivalence`, derived final laws, an answer-independent polynomial builder, SAT, or `P = NP`. |
| Explicit-list residual routes | `lake env lean -DwarningAsError=true lean-audit/PNPResidualRoutesAxiomAudit.lean` | A supplied finite list is scanned for a strictly smaller equivalent implementation; gains are sound and strictly descend in residual slack; exact and ZeroSlack results require semantic-minimality proofs. | List or global route completeness, absence of unlisted gains, the report ZeroSlack contradiction, PCCMin exactness, or polynomial runtime. |
| Archive integrity | `npm run legacy:v0:check` | Three annotated-tag identities and the pinned release digests match the archive manifest. | Signed provenance, theorem correctness, or checker soundness. |
| Historical checker replay | `npm run legacy:v0:replay -- --output /tmp/pnp-legacy-v0-7072f8d` | The pinned legacy implementation and selected tests reproduce their recorded behavior outside the active checkout. | Current theorem status, independent checker soundness, or validation of every mathematical implication. |
| Release checksums | `SHA256SUMS` and `SHA256SUMS.sha256` | Published artefact bytes match the sealed ledger. | Correctness of the artefact contents. |
| Independent audit | Reviewer derivations, counterexamples, clean-room checkers, and reproduction logs | Evidence about mathematics, checker soundness, complexity, and provenance at the audited boundary. | Broader claims outside the audit's stated scope. |

## Frozen release coordinates

```text
source tag:      final-pnp-proof-report-hardened-7072f8d
source commit:   7072f8d0bda6d44d240f9bb3fad624fd357e1278
artefact tag:    final-pnp-proof-report-artifacts-hardened-7072f8d-sealed
artefact commit: 9d1de19f827e5cb6880741352eb2349cbbb45994
artefact path:   proof-artifacts/final-pnp-proof-report-hardened-7072f8d/
archive manifest: archive/legacy-v0/ARCHIVE.json
```

The current canonical [PDF](./canonical_proof_report.pdf) and
[TeX](./canonical_proof_report.tex) form a generated, concise reconstruction report. It
records the false concrete publication gate and does not state an established `P = NP` theorem.
The historical 56-page claim manuscript is retained only at the pinned legacy source coordinate
recorded by [`archive/legacy-v0/`](./archive/legacy-v0/README.md).

## Reviewer map

- [Compiled Lean theorem inventory](./docs/lean_theorem_inventory.md): current deterministic environment inventory, concrete publication gate, milestone bindings, and generated-report boundary.
- [Formal reconstruction notice](./docs/FORMAL_RECONSTRUCTION.md): current authority, earned scope, blockers, and nonclaims.
- [Reviewer guide](./docs/reviewer_guide.md): historical checker-route overview, audit paths, and fast falsification checklist.
- [Proof pipeline](./docs/proof_pipeline.md): historical proposed mathematical route, executable evidence route, and hidden-search risks.
- [Terminology crosswalk](./docs/terminology_crosswalk.md): historical-report definitions and standard-language mappings for bespoke terms.
- [Trust model](./docs/trust_model.md): historical mathematical, parser, checker, runtime, build, seal, report, and website trust boundaries.
- [Audit questions](./docs/audit_questions.md): historical claim-by-claim worksheet with concrete refutation criteria.
- [Reproducibility protocol](./docs/reproducibility.md): fresh-clone, checksum, pinned-test, regeneration, and comparison instructions.
- [Minimal examples](./examples/minimal/README.md): eight small accepted/rejected demonstrations.
- [External review status](./EXTERNAL_REVIEW_STATUS.md): public record of substantive feedback and what has not been independently verified.
- [Lean direct-wire NAND semantics](./docs/lean_nand_semantics.md): exact scope of the axiom-free Boolean semantics milestone.
- [Lean concrete machine and cost kernel](./docs/lean_concrete_machine.md): executable codecs, finite rule-list semantics, bounded execution, runtime witnesses, and exact nonclaims.
- [Lean blank-delimited tape output](./docs/lean_tape_handoff.md): observable first-blank output semantics, the pure canonical handoff target, and the remaining executable-handoff boundary.
- [Lean boundary-marked pipeline tape geometry](./docs/lean_pipeline_tape_geometry.md): two-track data/marker framing, arbitrary exterior garbage, and proved local boundary expansion.
- [Lean executable all-input framer](./docs/lean_pipeline_input_framer.md): a literal finite machine from every raw bitstring to a represented frame, with exact branch costs and a uniform compiled raw polynomial.
- [Lean executable internal output handoff](./docs/lean_pipeline_output_handoff.md): a literal finite machine from an already represented tape to its represented blank-delimited handoff target, with exact linear work and compiled budgets.
- [Lean local framed machine simulation](./docs/lean_pipeline_machine_simulation.md): ordered first-match exact-run lifting, `k ≤ F` prefix extraction, and conditional designated-halting padding at work fuel `3 * F` and compiled fuel `18 * F` from an already represented start.
- [Lean literal Cook–Levin input-length tally](./docs/lean_cook_levin_builder_input_length.md): fixed-rule input preservation, exact unary tally, exact work/raw polynomials, timeout behavior, and the total-framer endpoint connection.
- [Lean executable Cook–Levin builder input prefix](./docs/lean_cook_levin_builder_input_prefix.md): collision-free framer/tally composition, literal launch execution, exact cumulative trace, external raw polynomial, and fail-closed timeout behavior.
- [Lean standalone Cook–Levin builder token appender](./docs/lean_cook_levin_builder_token_appender.md): four-token finite control, exact append/rewind execution, first canonical formula bits, external raw bound, and fail-closed malformed/short-fuel behavior.
- [Lean composed Cook–Levin first-token prefix](./docs/lean_cook_levin_builder_first_token_prefix.md): literal 184-rule raw-input composition, exact bridge and final tape, first canonical token bits, external quadratic bound, and fail-closed negative cases.
- [Lean composed Cook–Levin complete width header](./docs/lean_cook_levin_builder_complete_header.md): literal unary width-polynomial evaluation, collision-free five-component composition, exact complete header bits, external polynomial fuel, and fail-closed boundaries.
- [Lean composed Cook–Levin body-start prefix](./docs/lean_cook_levin_builder_body_start_prefix.md): complete-header composition with a unary next-slot evaluator and fixed separator appender, exact retained coordinate and token bits, external polynomial fuel, and fail-closed boundaries.
- [Lean composed Cook–Levin first-literal prefix](./docs/lean_cook_levin_builder_first_literal_prefix.md): body-start composition with a unary next-slot evaluator and fixed sign/zero appenders, a constructive positive-variable-zero proof, exact retained coordinate and token bits, external polynomial fuel, and fail-closed boundaries.
- [Lean composed Cook–Levin complete first-clause prefix](./docs/lean_cook_levin_builder_first_clause_prefix.md): first-literal composition with a unary next-slot evaluator and a fixed eight-token tail, constructive positive-variable-zero/one/two semantics, exact retained coordinate and complete clause bits, external polynomial fuel, and fail-closed boundaries.
- [Lean literal Cook–Levin token-cursor padding step](./docs/lean_cook_levin_builder_dynamic_token_cursor_step.md): complete-first-clause composition with one total launch and a fixed 45-rule cursor advance, exact valid-padding semantics, retained coordinate advancement, external polynomial fuel, and fail-closed boundaries.
- [Lean Cook–Levin first-clause remaining-padding run](./docs/lean_cook_levin_builder_first_clause_padding_run.md): two unary evaluators around a literal 25-rule countdown loop, exact traversal of the remaining first-clause padding block, second-clause-start semantics, external polynomial fuel, and fail-closed boundaries.
- [Lean Cook–Levin second-clause separator step](./docs/lean_cook_levin_builder_second_clause_separator_step.md): selected separator appender plus cursor advance, exact canonical prefix through clause two's opening token, retained following-`F` coordinate, external polynomial fuel, and fail-closed boundaries.
- [Lean Cook–Levin second-clause first-literal prefix](./docs/lean_cook_levin_builder_second_clause_first_literal_prefix.md): two selected `F` appenders and two cursor advances, exact canonical prefix through negative variable zero, retained variable-one sign coordinate, external polynomial fuel, and four fail-closed launch boundaries.
- [Lean Cook–Levin second-clause second-literal prefix](./docs/lean_cook_levin_builder_second_clause_second_literal_prefix.md): selected `F`/`T`/`F` appenders and three cursor advances, exact canonical prefix through negative variable one, retained clause-terminator coordinate, external polynomial fuel, and six fail-closed launch boundaries.
- [Lean collision-free pipeline state namespace](./docs/lean_pipeline_state_namespace.md): injective three-stage renaming, lookup-isolated finite rule-table concatenation, and exact stage-local trace transport.
- [Lean sequential pipeline state namespace](./docs/lean_pipeline_sequential_state_namespace.md): disjoint whole-component images, isolated dispatch, local-trace transport, and the exact remaining composition boundary.
- [Lean executable pipeline stage bridges](./docs/lean_pipeline_stage_bridges.md): exact framer/simulator/handoff launches, verdict-indexed handoff copies, and cumulative work/raw costs through the internal endpoint.
- [Lean executable terminal raw-output packer](./docs/lean_terminal_output_packer.md): universal local packing, blank-delimited output equality, exact compiled cost, and one-step-short timeout.
- [Lean executable handoff-to-terminal bridge](./docs/lean_pipeline_terminal_bridge.md): disjoint verdict-indexed packer copies, exact endpoint launches, local terminal output equality, and the remaining earlier-trace transport boundary.
- [Lean all-input four-stage pipeline compiler](./docs/lean_pipeline_compiler.md): complete raw-input verdict/output preservation for an already-raw proof-bearing target, explicit external polynomials, timeout behavior, and the remaining charged-program refinement boundary.
- [Lean finite charged-pipeline complexity interface](./docs/lean_concrete_complexity.md): concrete bitstring P/NP witnesses, bounded certificates, polynomial reductions, the inactive target, and the raw-machine-link boundary.
- [Lean direct-wire NAND enumerator](./docs/lean_nand_enumerator.md): scope and limits of exact-width syntactic completeness.
- [Lean exhaustive reference minimum](./docs/lean_nand_reference_minimum.md): decidable truth tables, exact finite minimum, residual slack, and the concrete framed boundary.
- [Lean locked-NAND local baselines](./docs/lean_locked_nand_baseline.md): typed candidates, semantic output lower bounds, source-derived accounting, five exact local minima, and the quarantined legacy fixture.
- [Lean conditional locked-NAND threshold boundary](./docs/lean_locked_nand_threshold_boundary.md): the six proof-bearing premises, derived semantic boundary, hostile-review mapping, and exact missing instantiations.
- [Lean explicit-list residual routes](./docs/lean_residual_routes.md): sound gain scanning, proof-bearing terminal results, and fail-closed unresolved outcomes.

## Install and current package surface

Use the lockfile-preserving installation command:

```bash
npm ci --ignore-scripts
```

The root package deliberately exports only current formal-status and archive-verification APIs. The
legacy checker modules remain in repository history and at the pinned source tag, but are not active
package exports.

```js
import {
  CheckFormalReconstructionStatus0,
  CheckLegacyV0Archive0,
} from '@aisknab/pnp';

const status = await CheckFormalReconstructionStatus0({ writeOutput: false });
const archive = await CheckLegacyV0Archive0();
```

Useful top-level commands:

```bash
npm run check
npm test
npm run validate
npm run formal:status
node scripts/export-lean-theorem-inventory.mjs --check
node scripts/generate-formal-publication.mjs --check
npm run report:check
npm run legacy:v0:check
npm run pnp:verify -- --no-write
```

## Historical Proof-development scripts

The assertion-checker release used narrowly scoped proof-development entrypoints under the `proof:*`
namespace. They are not scripts on current `main`; they exist only in the pinned legacy-v0 source
tree reached by the designated replay. They do not determine current theorem status. The current authority is
[`status/FORMAL_RECONSTRUCTION_STATUS.json`](./status/FORMAL_RECONSTRUCTION_STATUS.json), checked with:

```bash
node pcc-formal-reconstruction-status0.mjs --json
```

In that legacy interface, a proof script was a direct checker invocation of this form:

```text
node pcc-<checker-name>0.mjs --json
```

The following commands are historical examples from the pinned source tag and are not commands on
the active package or formal proof gates:

```bash
npm run proof:uniform-final-soundness-target -- --historical-replay
npm run proof:uniform-input-family -- --historical-replay
npm run proof:uniform-locked-nand-construction -- --historical-replay
npm run proof:uniform-locked-nand-threshold -- --historical-replay
npm run proof:uniform-residual-band-minimizer -- --historical-replay
npm run proof:uniform-zeroslack-closure -- --historical-replay
npm run proof:no-hidden-oracle-semantic -- --historical-replay
npm run proof:uniform-complexity-conclusion -- --historical-replay
node pcc-formal-reconstruction-status0.mjs --json
```

The uniform scripts above replay legacy assertion-checker records. They do not determine current
theorem status or establish any proposition named by those records.

## Historical Public RunAll0 entry point

`RunAll0` was the public entry point for the frozen assertion-checker release. It is not exported on
current `main`. Reproduce it only through the pinned legacy-v0 runner described in
[`REPRODUCE.md`](./REPRODUCE.md). The current status check is:

```bash
node pcc-formal-reconstruction-status0.mjs --json
```

At the pinned source tag, the legacy commands were:

```bash
npm run smoke -- --historical-replay
npm run smoke:full -- --historical-replay
```

The legacy replay encoded this conditional assertion:

```text
CheckPCCPackexp(GeneratePCCPack())=accept implies P = NP
```

The generator is untrusted. The legacy checker validates the materialized package, compares canonical bytes rather than digest equality, and records the conditional conclusion only after its final replay
accepts. A reject run emits a replayable first failure and no public theorem conclusion. Acceptance of
that replay does not establish the named mathematical conclusion.

The package entry point is:

```text
index.mjs
```

## Historical Release audit replay

The release audit belongs to the frozen assertion-checker release. It is not a current package script
or part of the current formal verification gate. Use the pinned runner in
[`REPRODUCE.md`](./REPRODUCE.md); any historical commands below apply only inside its detached source
worktree and must not be used to infer current theorem status.

```bash
npm run release:audit -- --historical-replay
```

For the full release audit record:

```bash
npm run release:audit:full -- --historical-replay
```

The release audit checks the public package surface, package exports, README claim boundary, orphaned
tests, syntax of checker modules, deterministic repeated `RunAll0` execution, the public surface freeze
phase, and the materialized public-status release gate. Those checks describe legacy checker replay,
not a mathematical proof.

### Release audit hard-gate default

Inside the pinned source worktree, the unflagged legacy form
`npm run release:audit -- --fast-local` rejects at the reconstruction boundary. Historical replay
must be explicit:

```bash
npm run release:audit -- --historical-replay --fast-local
```

Fast local mode keeps the public surface freeze enabled while skipping the costly materialized
public-status gate. This remains checker-replay behavior, not theorem verification.

### Release audit materialized gate flags

The old forms `npm run release:audit -- --materialized-gate` and
`npm run release:audit -- --no-materialized-gate` now reject unless `--historical-replay` is also
present. The historical CLI retains `--materialized-gate-out` and `--no-materialized-gate-cli` for
reproducing the concrete gate as a path separate from synthetic `RunAll0`.

### Release audit materialized gate summary

Historical full-mode records retain these fields:

```text
materializedPublicStatusGateDigest
materializedPublicStatusGateFileCount
materializedPublicStatusGateDirectRecordCount
materializedPublicStatusGateCliRecordCount
materializedPublicStatusGateAcceptedPublicConclusionOnly
syntheticRunAll = false
acceptedPublicConclusionOnly = true
```

These are preserved audit fields only. They do not describe current theorem status.

### Release audit surface freeze

The historical `surfaceFreeze` record includes `materializedPublicStatusGateDigest` and
`materializedPublicStatusGateAcceptedPublicConclusionOnly`. The reconstruction-era replacement is
`CheckFormalPublicSurface0`, which verifies that legacy routes are absent from the closed current
package surface.

## Historical Internal materialized package path

The remaining release-audit sections document the frozen assertion-checker machinery. Their fields,
normal forms, and negative tests are preserved for auditability only. They are subordinate to the
[formal reconstruction status](./status/FORMAL_RECONSTRUCTION_STATUS.json).

Materialized package checks use explicit JSON fixtures rather than implicit source state:

```text
MaterializedPCCPack0.json
  -> CheckMaterializedShell0
  -> CheckMaterializedAggregate0
```

Historical replay commands for this layer are:

```bash
npm run materialized:shell
npm run materialized:aggregate -- --historical-replay
npm run materialized:bridge -- --historical-replay
```

An accepted historical bridge recorded `CheckPCCPackexp status = accepted` and
`ExternalAcceptRunReplay verdict = accept` before emitting its conditional record. These fields are
legacy checker outputs, not current theorem authority.

## Historical Release audit README wording freeze

`CheckReadmeReleaseBoundary0` preserves the legacy conditional theorem boundary and its
stale-layout exclusions for reproducible checker replay. Passing that wording check does not
validate the mathematics or reactivate theorem emission.

## Historical Public entry release surface freeze

The public release surface is checked by `CheckPublicEntryReleaseSurface0`.

The exact portions are:

```text
index.mjs public export names
package.json exports keys and values
package.json bin keys and values
```

The script surface is intentionally extensible under the narrow `proof:*` namespace during proof development. Non-proof script additions and unsafe proof-script commands still reject.

## Historical Release audit public surface freeze phase

The release audit executes the public entry release surface freeze checker as a ledger phase named `publicSurfaceFreeze`.

The phase verifies:

```text
index.mjs public export names
package.json exports map
package.json bin map
package.json script map
```

During active proof development, the script map check is exact for existing release scripts and permits only the constrained `proof:*` checker-script namespace.

## Historical Release audit public surface freeze summary

The release audit exposes the public-surface check as a first-class summary, not only as a side effect.

The summary includes:

```text
publicSurfaceFreezeDigest
publicSurfaceFreezePublicEntryExportCount
publicSurfaceFreezePackageExportCount
publicSurfaceFreezePackageBinCount
publicSurfaceFreezePackageScriptCount
publicSurfaceFreezeSurfaceFrozen
```

When enabled, the release audit requires:

```text
surfaceFrozen = true
```

During active proof development, `surfaceFrozen = true` means exports and bin entries remain exact while package scripts may grow only through the constrained `proof:*` checker-script namespace.

## Historical Release audit public surface freeze negative coverage

The release audit includes negative coverage for the public surface freeze phase.

The negative checks prove that `CheckReleaseAudit0` rejects if the public surface freeze checker returns an accepted record with:

```text
wrong normal-form kind
surfaceFrozen = false
zero public entry export count
zero package export count
zero package bin count
zero package script count
missing normal form
```

All such failures surface at:

```text
CheckReleaseAudit0.publicSurfaceFreeze
```
