# Formal reconstruction notice

**Effective: 16 July 2026**

## Current status

The target theorem is `P = NP`. It is **not currently established by this repository**.

Public theorem emission is disabled while the project is reconstructed around a concrete,
assumption-audited Lean theorem. The active machine-readable status is
[`status/FORMAL_RECONSTRUCTION_STATUS.json`](../status/FORMAL_RECONSTRUCTION_STATUS.json).
It and the current canonical report are derived from the deterministic compiled-environment
inventory mirrored at [`status/LEAN_THEOREM_INVENTORY.json`](../status/LEAN_THEOREM_INVENTORY.json)
and [`public/pnp-theorem-inventory.json`](../public/pnp-theorem-inventory.json).

Use `node pcc-formal-reconstruction-status0.mjs --json` to verify the active status boundary. The
current `npm run pnp:verify` command checks that boundary, the closed active package surface, the
pinned legacy-v0 archive identity, and the small current-authority suite. It cannot be configured to
execute the historical replay; replay acceptance does not change formal-reconstruction status.

Use `node pcc-formal-public-surface0.mjs --json` to verify that superseded activation, release,
materialized, and theorem-checker routes are absent from the active package exports, scripts, and bins.

## Why the earlier activation was withdrawn

The legacy JavaScript stack checks the shape, linkage, digests, and declared fields of finite
records. Several central mathematical obligations are represented by assertion-bearing fields
or trust objects rather than derivations of the named propositions. Acceptance of those records
therefore does not establish the mathematical truth of the locked-NAND reduction, residual-band
minimizer, ZeroSlack theorem, or final complexity conclusion.

The current Lean development makes parts of the intended route explicit and now defines an
axiom-free finite charged-pipeline interface for P, bounded-certificate NP, and polynomial
many-one reductions. It does not yet prove that every such pipeline compiles or refines to the raw
single-tape machine kernel. A blank-materialization layer proves that finite tape lists denote the
same raw execution whenever their infinite blank extensions agree. In particular, every ordinary
empty, odd, or even input agrees with its packed work-tape start. The literal finite input framer
now consumes that equivalence: it handles every raw bitstring, reaches an accepting represented
frame under exact empty/full/partial branch costs, and accepts without timeout from ordinary
`startConfig` within `6 * m * m + 39 * m + 75` raw steps. All 70 public framer declarations have
empty axiom closure. The local framer theorem ends at that frame; the later all-input compiler now
consumes it for every raw bitstring. A separate local layer preserves the raw interpreter's first matching rule
and lifts every supplied exact chain of `n` successful raw transitions from an already represented
boundary frame to exactly `3 * n` successful work transitions. From an ordinary raw `run` with
fuel `F`, it extracts an exact prefix of length `k ≤ F` reaching the same endpoint. If that endpoint
is designated halting, `workRun` with fuel `3 * F` and compiled-machine `run` with fuel `18 * F`
reach its representation and encoding. This is conditional padding, not a termination result: the
full budgets are not successful-transition counts or input-size bounds, and a stuck nonhalting stop
is not classified as a verdict. An additional axiom-free namespace layer
injectively retags the framer, lifted simulator, and handoff into pairwise-disjoint state images,
proves first-match lookup isolation for one concatenated finite rule table, and transports each
existing exact stage-local trace. A bridge-first finite work machine now adds one exact
symbol-preserving framer-to-simulator launch and separate accept/reject launches into two disjoint
verdict-indexed handoff copies. For every supplied exact target run it composes the three stages,
preserves bounded accept/reject classification, leaves a supplied stuck nonhalting endpoint as
timeout at the exact prefix budget, and compiles from ordinary canonical paired raw input at exactly
six times the cumulative work cost. This supplied-trace bridge alone does not prove target
termination or turn the supplied source-transition count and final output length into an
external-input-size polynomial. The
development also includes the executable internal handoff machine: from an already represented logical
tape `raw`, it reaches an accepting representation of `raw.handoffTarget` in exactly
`2 * raw.outputBits.length + 4` work steps and `12 * raw.outputBits.length + 24` compiled steps.
The local handoff theorem begins at an encoded internal work configuration; the cumulative bridge
theorem begins at ordinary paired `startConfig`. Its two-track encoded endpoint is not itself an
ordinary raw-visible `machineOutput` layout. A separate literal `TerminalOutputPacker` now proves
exact blank-delimited raw output equality with a local `18*n^2 + 36*n + 6` bound and one-step-short
timeout. `PipelineTerminalBridge` appends two disjoint verdict-indexed packer copies to an extended
finite rule table and proves exact accepting/rejecting endpoint launches, terminal halts, and raw
output equality under the local `18*n^2 + 36*n + 12` suffix bound. It also preserves every
successful earlier bridge step and exact trace in the extended rule table. For each caller-supplied
exact accepting or rejecting target execution, one theorem now composes the ordinary paired input,
framer, simulator, represented handoff, terminal launch, and packer in that literal machine, with
exact verdict and raw-output equality. `PipelinePairedCompiler` now extracts the exact prefix from
the target's proof-bearing bounded run, proves that an `F`-step target exposes at most `m + F + 1`
output bits, and pads the same literal compiled machine to an explicit polynomial in external pair
length `m`. For every `PolynomialTimeMachine` and every canonical pair it preserves exact verdict,
no-timeout, language acceptance, and ordinary raw output. `PipelineCompiler` now uses the same
literal table for every raw `BitString`: it extracts the target prefix internally, preserves exact
verdict and ordinary output, excludes timeout, and proves language acceptance at
`B(m) = m + p(m) + 1` and an explicit complete runtime polynomial in external length `m`. All 29
public declarations have empty axiom closure. This wraps one already-raw proof-bearing target.
`PipelineSequentialStateNamespace` supplies collision-free outer images for two complete component
tables and literal launches from either first verdict. `PipelineSequentialCompiler` now completes
that execution for every raw input in one finite table: either first verdict launches the second
simulator on the represented first output, the second verdict and ordinary output are exact, and a
stuck nonhalting first endpoint remains timeout. If the component time bounds are `p` and `q`, the
external polynomial is
`PipelineRaw(p)(m) + 6 + PipelineRaw(q)(m + p(m) + 1)`. All 31 public declarations have empty
axiom closure. `PipelineRefinement` now recursively applies this compiler to function composition
and decision precomposition, proving exact output/verdict and a polynomial raw-machine refinement
for every finite charged program tree. All 16 public declarations have empty axiom closure.
The development also provides one direct raw-machine instance: a universally
correct polynomial-time verifier for canonically encoded finite CNF formulae and bounded assignment
certificates, proving `PNP.Concrete.CNFSAT ∈ NP`. It does not provide a deterministic polynomial-time
decider proving `CNFSAT ∈ P`, concrete NP-hardness or NP-completeness, the complete locked-NAND
threshold theorem, the residual-band exact minimizer, ZeroSlack, the recursive complexity-model
machine link, or a root theorem `PNP.Main.p_eq_np` with an acceptable axiom audit.

The repository now pins `leanprover/lean4:v4.31.0` and builds the explicit `PNP` library root. That
root imports every tracked Lean source module. `PNP.Main.rootTheoremStatus` is assumption-free data
recording that the theorem is not released; it is not the target theorem. The current conditional
bridge still depends on four disclosed project-specific axioms: `PNP.LockedNANDThreshold`,
`PNP.ResidualBandExactMinimization`, `PNP.GeneratePCCPack`, and `PNP.CheckPCCPackexp`. The legacy
`PNP.SAT` value is now an ordinary non-authoritative label, not an axiom and not an alias for
`PNP.Concrete.CNFSAT`.

The root now also imports an axiom-free concrete foundation: canonical bitstring framing and pair
decoding, natural-polynomial bound syntax, a finite rule-list single-tape machine, fuel-bounded
execution, and proof-bearing deterministic runtime witnesses. Above it, finite function and
decision pipeline syntax carries polynomial runtime, output-size, certificate-size, and handoff
bounds. Lean constructs P contained in NP, reduction identity/composition/transport, and the
NP-complete-in-P implication. Boundary geometry and the local simulator now discharge exact finite
configuration runs, including marker growth across arbitrary exterior garbage, exact-prefix
extraction, and the conditional designated-halting padding described above.
The separate input framer supplies an executable all-input-to-frame trace with exact branch costs
and the uniform raw polynomial `6 * m * m + 39 * m + 75`; its earlier canonical-pair route retains
the sharper exact paired bound. The state-namespace layer gives it, the simulator, and the internal
handoff pairwise-disjoint images in one lookup-isolated concatenated rule table and proves that the
three established exact traces survive renaming. The stage-bridge layer connects supplied exact
target runs into one verdict-preserving internal execution with explicit cumulative work and raw
costs. The separate terminal packer supplies raw output de-tagging from its encoded internal start,
and the terminal-bridge layer proves the subsequent local suffix from either represented handoff
endpoint and transports the earlier ordinary-input trace into that extended machine. The paired
compiler derives target termination and a complete external-size polynomial for canonical pair
inputs. The all-input compiler generalizes that result to every raw input, including empty, odd,
malformed, and non-pair words, while preserving exact verdict and raw-visible output. The remaining
sequential compiler then composes two such proof-bearing targets in one literal table, transfers the
first output internally, and proves the second verdict, raw-visible output, timeout behavior, and an
external polynomial. The remaining machine-link gap is the recursive compiler from the charged
function/decision program syntax into the existing `RawRefinement` contracts.
See
[`lean_concrete_complexity.md`](./lean_concrete_complexity.md) and
[`lean_pipeline_stage_bridges.md`](./lean_pipeline_stage_bridges.md), and
[`lean_pipeline_terminal_bridge.md`](./lean_pipeline_terminal_bridge.md), and
[`lean_pipeline_paired_compiler.md`](./lean_pipeline_paired_compiler.md), and
[`lean_pipeline_compiler.md`](./lean_pipeline_compiler.md), and
[`lean_pipeline_sequential_compiler.md`](./lean_pipeline_sequential_compiler.md).

The concrete CNF layer separately defines canonical formula and assignment codecs, propositional
CNF semantics, a Boolean certificate checker, a finite work machine, and its compiled raw machine.
Lean proves for every raw formula/certificate pair that the compiled machine accepts exactly when
the checker returns true, rejects exactly when it returns false, and cannot time out at the explicit
polynomial fuel bound. The resulting `.paired` `PolynomialTimeVerifier` proves
`PNP.Concrete.FinalUniversalDesign.cnfSATInNP : InNP CNFSAT`. This is a bounded-certificate NP
membership theorem, not a deterministic decision procedure and not a hardness result.

## Compiled inventory and current publication boundary

`lean-audit/PNPTheoremInventory.lean` traverses `Lean.Environment.constants` after the explicit
`PNP` root has compiled and calls `Lean.collectAxioms` for every included public `PNP.*`
declaration. It does not infer declarations or dependencies by parsing Lean source. The canonical,
lexically ordered JSON output records declaration kinds and compiled axiom closures, and its status
and public copies must be byte-identical. See
[`lean_theorem_inventory.md`](./lean_theorem_inventory.md) for the inventory contract and check
commands.

Every earned intermediate milestone row requires its configured detailed theorem candidates to
match by exact name and theorem kind, have axiom closures within the fixed Lean standard
allowlist and no project axioms, preserve their per-name
domain-separated kernel-type SHA-256 values, and match the pinned closure over every
`lean/**/*.lean` file plus the Lean/Lake pins and inventory probe. Type or source drift revokes
milestone credit until reviewed pins change.

Declaration, theorem, module, excluded-private, and reviewed-candidate counts are emitted by the
compiled inventory and are intentionally not duplicated here. The current Lean source closure has
exactly four project-specific axioms; the generated inventory and publication outputs must be
regenerated and byte-checked after source-closure changes before they may describe the revision.

Inventory generation is deliberately separate from theorem publication. The concrete gate expects
the compatibility theorem `PNP.Main.p_eq_np` to have the exact concrete target
`PNP.Main.ConcretePEqualsNP`. The target now exists as an axiom-free **definition** aliasing mutual
inclusion for the finite charged-pipeline classes; it is not a proof. The compatibility/root theorem
`PNP.Main.p_eq_np` remains absent. The existing witness-handle proposition `PNP.PEqualsNP` is
abstract and explicitly publication-ineligible.

The expected kernel fingerprints for the concrete target type and value, compatibility-root type,
axiom closure, and source closure are intentionally `null` in this migration step. Unset
fingerprints fail closed; `null` never matches `null`. The concrete finite charged-pipeline model is
eligible, but eligibility alone cannot replace the absent root theorem or unset fingerprints.
Therefore the gate does not pass and every theorem-emission field derived from it remains false or
`null`.

The root `canonical_proof_report.tex` and `canonical_proof_report.pdf` now form the generated,
concise formal-reconstruction report. They replace the historical claim manuscript at the
root and make the non-activation boundary explicit. The historical 56-page claim artifact is
available only from the pinned legacy source coordinate recorded under
[`archive/legacy-v0/`](../archive/legacy-v0/README.md).

The direct CNF verifier closes concrete NP membership for `PNP.Concrete.CNFSAT`; the all-input and
sequential compilers plus recursive refinement close the concrete machine-link blocker. The
Cook–Levin development now proves exact raw-verifier semantic equivalence and an explicit
polynomial bound for the actual canonical encoded formula in external source-input length. It also
provides a rectangular answer-independent constraint/clause/token/bit schedule whose populated
slots reproduce that exact encoding and whose total bit-slot count is the same external polynomial.
Direct coordinate decoders now agree pointwise with every schedule layer, and a fuelled cursor has
exact prefix, full, one-step-short, terminal, excess-fuel, and canonical-output theorems. The first
literal builder stage is also present: a fixed 19-rule machine preserves the source input, appends
an exact unary length tally, connects to the total-input-framer endpoint, and proves exact work and
compiled raw polynomials plus malformed and one-step-short timeout. A collision-free finite table
executes the total framer, one literal symbol-preserving launch, and that tally from every raw
bitstring within the external compiled polynomial `18*n*n + 63*n + 93`; a tally scan configuration
headed by the unused `zeroOne` symbol and one-step-short fuel remain timeout. A separate fixed
59-rule machine appends any one of the four canonical two-bit CNF tokens after a supplied tally
endpoint and restores the source focus for every input, canonical prior output, and arbitrary
exterior garbage.

The first composed builder prefix joins those two complete tables. One literal 184-rule work
machine uses disjoint injective state images for all 116 input-prefix rules and all 59 appender rules,
with nine total bridge rules between them. Every raw bitstring reaches the preserved input/tally
workspace containing exactly the first `T` token within the external compiled bound
`18*n*n + 87*n + 147`. Lean proves that the token is direct formula-bit coordinates zero and one and
`encodedFormula.take 2` for every concrete problem in either input mode. The prefix endpoint before
launch, malformed prefix/appender phases, and one-step-short fuel remain timeout.

The complete-header milestone extends that exact trace through a structurally generated literal unary
evaluator for the verifier-fixed, mode-sensitive formula-width polynomial. Five total nine-symbol
bridges place the prefix, evaluator, a 16-rule unary-root controller, and reusable `T` and final `F`
appenders in pairwise-disjoint injective state images. The resulting finite table has exactly
`363 + evaluator.ruleCount` rules and never calls `NatPolynomial.eval` from its executable table.
For every raw input it accepts at the exact preserved workspace containing `T` repeated
`FormulaWidth` times followed by `F`; the corresponding bits equal
`encodedFormula.take (2 * (FormulaWidth + 1))`. The exact compiled trace is bounded by a public
external `NatPolynomial`, while the pre-launch prefix endpoint and one-step-short full trace remain
timeout. All 74 evaluator declarations and all 83 composed-header declarations have complete
kernel-axiom audits whose closures are empty or use only `propext` and `Quot.sound`.

The body-start milestone continues through a structurally generated unary evaluator for token
coordinate `FormulaVariableSlotBound + 2`, two total bridges, and a fixed separator appender. Every
raw input emits exactly `T^FormulaWidth F Sep`, retains that token coordinate and its doubled raw-bit
cursor, and follows an external compiled polynomial. Its 60 public declarations have complete
kernel-axiom audits using only the approved Lean-standard closure.

The first-literal milestone continues again through a unary evaluator for token coordinate
`FormulaVariableSlotBound + 4`, three total bridges, and fixed `T` and `F` appender copies in four
disjoint state images. Every raw input emits exactly `T^FormulaWidth F Sep T F`; a constructive
schedule proof identifies the final pair as the positive sign and unary-zero terminator of the first
shape-clause literal, positive variable zero. The emitted bits equal
`encodedFormula.take (2 * (FormulaWidth + 4))`, and the external compiled bound evaluates to the
body-start bound plus `174 + 6*Unary.workSteps(nextTokenSlotPolynomial) + 48*n + 24*width`. Its 74
public declarations, including the halt-source separation theorem required for safe downstream
composition, have complete kernel-axiom audits using only `propext` and `Quot.sound`.

The current first-clause milestone extends that trace through a unary evaluator for token coordinate
`FormulaVariableSlotBound + 12` and a fixed 535-rule tail containing eight complete token appenders
and seven total bridges. Every raw input emits exactly
`T^FormulaWidth F Sep T F T T F T T T F Finish`. A constructive schedule proof identifies the three
clause literals as positive variables zero, one, and two, and the emitted bits equal
`encodedFormula.take (2 * (FormulaWidth + 12))`. The external compiled bound evaluates to the
first-literal bound plus
`1158 + 6*Unary.workSteps(firstClauseNextTokenSlotPolynomial) + 192*n + 96*width`. All 77 new public
declarations, and the combined 78-declaration audit including the predecessor separation theorem,
use only the approved Lean-standard closure.

This earns exactly the canonical prefix through the complete first clause. The retained coordinate
is data: no machine interprets the dynamic formula cursor as raw transitions, emits the remaining
formula body, composes a complete raw formula builder with a construction-runtime proof, or packages
a concrete `PolynomialReduction`. A deterministic
polynomial-time CNF-SAT decider, concrete NP-hardness/NP-completeness, locked-NAND threshold,
residual-band minimizer, ZeroSlack, the remaining end-to-end polynomial bounds, and the root
theorem/axiom audit remain incomplete.

The first concrete foundation is now checked in `PNP.DirectWire`: intrinsically topological direct-wire
NAND programs, total Boolean evaluation, gate-count size, ordered output wiring, and elementary
projection/constant/repeated-output/NAND/NOT/AND laws. Its dedicated axiom audit is clean. This does
not by itself discharge any of those publication blockers.

The next constructive layer enumerates every well-typed direct-wire implementation at fixed input,
gate, and output widths, including the unique empty output tuple and both orders of every NAND input
pair. Its completeness theorems and certificate are axiom-free. The enumerator is intentionally not
canonical or claimed duplicate-free.

Finite Boolean tuples now give an executable decision procedure exactly equivalent to pointwise
`DirectWire.Equivalent`. A deterministic exhaustive scan from zero gates through a supplied target
selects an equivalent witness, proves its selected size is no greater than the target, and proves a
lower bound against every equivalent direct-wire candidate at every gate count. The resulting
empty-context reference minimum is invariant under semantic equivalence, and its residual slack is
zero exactly for a semantically minimum implementation. This is a finite reference computation: no
polynomial or practical-runtime bound is claimed, and it is not the asserted residual-band
minimizer used by the historical route.

Serial composition also provides one concrete environment/support/continuation frame. Within that
frame, equivalent support implementations can be replaced, and the corresponding additive global
slack identity is proved. This does not cover arbitrary support subsets, support profiles, or the
locked-NAND family. Accordingly the broad replacement/slack status fields remain false, and the
same substantive activation blockers remain.

The locked-NAND local bridge now contains six intrinsically typed direct-wire candidates with
honest gate/output widths: equality `10/10`, constant one `2/2`, constant zero `3/3`, trace
`18/18`, prefix conjunction `2/2`, and final conjunction `4/1`. Their internal programs are proved
constant-free. A general semantic theorem sends nonconstant, nonprojection, pairwise-distinct
outputs injectively to gates. Finite truth-signature proofs discharge those conditions for the five
square local candidates and establish exact empty-context reference minima of 10, 2, 3, 18, and 2.
The one-output final conjunction is excluded from that exactness claim.

Locked-baseline arithmetic is also derived from the actual typed program: an `m`-gate program has
`2m` source occurrences, `3m` trace-plus-source checks, and baseline
`18m + 10w_= + 3w_0 + 2w_1 + 2(3m-1)`, followed by four displayed final gates. The report word is
multi-output: its baseline coordinates plus one final coordinate remain exposed. Global candidate
construction and cross-instance `BaselineDistinct` are still absent, so the locked builder,
threshold, residual-slack-at-most-four bound, and polynomiality fields remain false.

The legacy synthetic `m = 2` fixture is quarantined because its real four program sources conflict
with metadata claiming six occurrences. Honest program-derived baseline/displayed counts are
`86/90`; counts made consistent with that metadata are `95/99`; and the stored hybrid values are
`91/95`. The typed Lean accounting, not this inconsistent seed, is current authority. See
[`lean_locked_nand_baseline.md`](./lean_locked_nand_baseline.md) for the full local proof boundary.

A further axiom-free module now proves the conditional semantic threshold deduction from an
explicit six-field package: `baselineCandidate`, `fullCandidate`, `baselineConditions`,
`initialOutputsPreserved`, `unsatisfiableFinalZero`, and `satisfiableFinalConditions`. From those
proof-bearing premises it derives the baseline lower bound, conditional residual slack at most
four, unsatisfiable minimum exactly at the baseline, satisfiable minimum between baseline plus one
and baseline plus four, and the corresponding conditional iff.

This is not the report locked-NAND threshold theorem. The six fields are not instantiated for a
source circuit. In particular, the arbitrary proposition and natural-number parameters are not
identified with circuit SAT and `lockedBaselineCount`; no global carrier layout, cross-instance
`BaselineDistinct`, `TraceEquivalence`, derived whole-carrier final-output laws, answer-independent
uniform builder, or polynomial bound is supplied. The module is not connected to the abstract
`PNP.LockedNANDThreshold` language.

The historical hostile review named `DirectWireOutputLowerBound`, `MacroDistinct`,
`TraceEquivalence`, `ZeroOutputConvention`, and `FinalLockSeparation`. The general output lower
bound was discharged in the preceding layer, and the model-level free-zero append convention is
now formalized. Global `MacroDistinct`, `TraceEquivalence`, and `FinalLockSeparation` remain
missing, as do all six concrete premise instantiations above. See
[`lean_locked_nand_threshold_boundary.md`](./lean_locked_nand_threshold_boundary.md).

The residual-route layer now performs one honest executable operation: it scans an explicit finite
list of typed implementations for the first strictly smaller semantically equivalent candidate.
Every returned gain is proved equivalent, smaller, and strictly descending in reference residual
slack. Exact-minimum and ZeroSlack result constructors require Lean proofs of semantic minimality;
the executable scanner itself can return only `gain` or `unresolved`.

This scan is deliberately fail-closed. `unresolved` excludes gains only in the caller-supplied
list. Lean contains an empty-list regression whose current implementation has residual slack one,
so unresolved cannot establish global minimality or zero slack. Candidate-list completeness, the
BCEL/HN/BUD/selector contradiction, a complete PCCMin loop, and every polynomial runtime claim
remain absent. The residual-band, ZeroSlack, and polynomial blockers therefore remain unchanged.

## The only acceptable future activation gate

Public theorem emission may be reconsidered only when all of the following are mechanically true:

1. an exactly pinned Lean environment builds the explicit root target;
2. `PNP.Main.p_eq_np` exists and proves the concrete target theorem;
3. the root theorem's dependency closure contains no `sorry` or `admit` placeholders;
4. no PNP-specific axiom or trust parameter assumes any substantive part of the result;
5. SAT, P, NP, reductions, machines, correctness, and cost are concrete, with the charged-pipeline
   semantics proved adequate for the selected raw machine model;
6. a deterministic SAT decider is executable and its polynomial bound is proved in the selected
   machine model (the current `CNFSAT ∈ NP` verifier is insufficient);
7. the locked-NAND, residual-band, and ZeroSlack obligations are proved rather than asserted; and
8. public status and paper claims are generated from the checked Lean theorem inventory.

The separate concrete gate enforces this boundary. Merely adding a declaration with the right name,
relying on abstract `PNP.PEqualsNP`, or leaving an expected fingerprint unset cannot activate it.

Check the current non-activation outputs with:

```bash
lake build PNP
node scripts/export-lean-theorem-inventory.mjs --check
node scripts/generate-formal-publication.mjs --check
node pcc-formal-reconstruction-status0.mjs --json --no-write
npm run report:check
```

External review can provide useful independent audit evidence, but it is not a mathematical premise
and is not part of this gate.

## Historical material

The previous assertion-checker stack, 56-page claim report, and activated coordinates remain
available at the pinned legacy coordinates for auditability. They are historical evidence about
what the implemented checkers accepted. They are not current theorem-status or report authority.

This notice supersedes the following coordinates as proof or publication authority:

```text
PNP-ACTIVATED-STATUS-2026-07-05-01
PNP-PUBLIC-THEOREM-ACTIVATION-2026-07-05-01
PNP-UNRESTRICTED-FINAL-SOUNDNESS-RELEASE-2026-07-05-01
```

Their files and Git history remain inspectable as subordinate legacy assertion-checker evidence.
The byte-exact source, artifact, and document coordinates are recorded under
[`archive/legacy-v0/`](../archive/legacy-v0/README.md). They must not be used to infer current theorem
status.
