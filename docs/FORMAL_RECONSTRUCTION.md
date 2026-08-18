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
threshold theorem, the residual-band exact minimizer, ZeroSlack, or a root theorem
`PNP.Main.p_eq_np` with an acceptable axiom audit.

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
timeout. All 74 evaluator declarations and all 84 composed-header declarations have complete
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
`1158 + 6*Unary.workSteps(firstClauseNextTokenSlotPolynomial) + 192*n + 96*width`. The following
direct token slot is constructively proved to be valid padding. All 79 new public declarations, and
the combined 80-declaration audit including the predecessor separation theorem, use only the
approved Lean-standard closure.

The token-cursor-step milestone composes that exact endpoint with one total nine-symbol launch and a
fixed 45-rule cursor-advance table. Every raw input preserves the complete first-clause output and
moves the retained unary coordinate from `FormulaVariableSlotBound + 12` to
`FormulaVariableSlotBound + 13`. Its consumed coordinate is the first in-range padding opportunity,
so the token-level specification cursor advances without emitting a token. The cursor suffix takes
exactly `2*cursorWord.length + 8` work steps including the launch, and the full compiled run is
bounded by `FirstClausePrefix.rawTimeBound + 48 + 12*cursorWord.length`. Malformed cursor scratch,
the unlaunched predecessor endpoint, and one-step-short total fuel remain timeout. All 47 public
declarations, including two reviewed dead-state dispatch facts for downstream composition, use only
the approved Lean-standard closure.

The first-clause-padding-run milestone continues from that one-step endpoint. It evaluates the exact
remaining count `(FormulaVariableSlotBound - 1) * (FormulaVariableSlotBound + 6)`, consumes it with
a literal 25-rule unary countdown loop, and evaluates the absolute second-clause-start coordinate.
Every looped-over direct slot is proved to be in-range padding, the recursive specification run emits
no token, and its endpoint is proved to contain the `Sep` that begins clause two. The complete table
has `1244` plus six unary-evaluator rule counts and is bounded by an external polynomial covering both
evaluators, three launches, and the quadratic countdown. The 83 new declarations plus one predecessor
controller interface use only the approved Lean-standard closure.

The second-clause-separator milestone then composes that endpoint with a selected 59-rule `Sep`
appender, two total nine-symbol bridges, and the same fixed 45-rule cursor advance. Its literal table
has `1366` plus six unary-evaluator rule counts. Every raw input emits the canonical prefix through
the separator beginning clause two, advances the retained unary coordinate by one, and proves that
the following direct token is `F`; the emitted bits are exactly
`encodedFormula.take (2 * (FormulaWidth + 13))`. Its external compiled bound is the predecessor
bound plus `246 + 24*n + 12*FormulaWidth + 12*cursorWord.length`. The combined 56-declaration audit
has 15 empty closures, 11 using only `propext`, and 30 using only `propext` and `Quot.sound`.
Malformed appender tally/output, malformed cursor scratch, both unlaunched endpoints, and
one-step-short total fuel remain timeout.

The second-clause-first-literal milestone continues with two selected 59-rule `F` appenders, four
total symbol-preserving bridges, and two copies of the fixed 45-rule cursor advance. Its table has
`1610` plus the six inherited/generated unary-evaluator rule counts. Every raw input emits the
complete negative literal on variable zero in clause two; its bits are exactly
`encodedFormula.take (2 * (FormulaWidth + 15))`. Direct schedule proofs identify the sign,
unary-zero terminator, and following variable-one sign as `F`, while the machine emits the first
two. Its external bound adds `564 + 48*n + 24*FormulaWidth + 24*cursorWord.length` to the separator
prefix bound. The combined 87-declaration audit has 25 empty, 18 `propext`, and 44
`propext`/`Quot.sound` closures. All four pre-launch endpoints, both appender copies, both cursor
copies, and one-step-short total fuel are fail-closed.

The second-clause-second-literal milestone then composes selected 59-rule `F`, `T`, and `F`
appenders, six total symbol-preserving bridges, and three copies of the fixed 45-rule cursor advance.
Its table has `1976` plus the six inherited/generated unary-evaluator rule counts. Every raw input
emits the complete negative literal on variable one in clause two; its bits are exactly
`encodedFormula.take (2 * (FormulaWidth + 18))`. Direct schedule proofs identify the sign as `F`,
the unary unit as `T`, the literal terminator as `F`, and the retained next token as `Finish`.
Its external bound adds `1026 + 72*n + 36*FormulaWidth + 36*cursorWord.length` to the first-literal
prefix bound. The combined 115-declaration audit has 34 empty, 25 `propext`, and 56
`propext`/`Quot.sound` closures. All six pre-launch endpoints, all three appenders and cursors, and
one-step-short total fuel are fail-closed.

The complete-second-clause milestone emits that retained `Finish` with one selected 59-rule
appender, then advances the unary cursor once with the fixed 45-rule table. Two total
symbol-preserving bridges yield a 113-rule suffix and a global table with `2098` plus the same six
unary-evaluator rule counts. Every raw input emits
`T^FormulaWidth F Sep T F T T F T T T F Finish Sep F F F T F Finish`; its bits are exactly
`encodedFormula.take (2 * (FormulaWidth + 19))`. Direct schedule proofs identify the executed slot
as `Finish` and the retained next slot as in-range padding. Its external bound adds
`390 + 24*n + 12*FormulaWidth + 12*cursorWord.length` to the second-literal prefix bound. The
combined 57-line audit covers all 55 new declarations plus the two reviewed cursor dead-loop facts:
15 closures are empty, 10 use only `propext`, and 32 use only `propext` and `Quot.sound`.
Malformed appender tally/output, malformed cursor scratch, both unlaunched endpoints, and
one-step-short total fuel remain fail-closed.

The second-clause-padding milestone then evaluates the exact remaining count
`D = (V - 1) * (V + 6) + 5 = formulaTokensPerClause - 7`, reuses the audited 25-rule
`PaddingCountdown` table to consume those opportunities, and evaluates the target coordinate.
Three total `WorkChain` bridges compose those phases with the complete-second-clause prefix. The
literal global table has `2150` plus the six inherited/generated predecessor unary-evaluator rule
counts and the two new evaluator rule counts. Every raw input follows an exact trace through all
`D` padding coordinates and reaches `V + 1 + 2 * formulaTokensPerClause`, whose direct schedule
outcome is the third clause's opening `Sep`. No token is emitted: the final bits remain exactly
`encodedFormula.take (2 * (FormulaWidth + 19))`. The compiled bound adds two evaluator costs,
three six-step launches, and the exact countdown term
`6 * (D * (2 * R + 8) + D^2)` to the predecessor bound. The combined 68-declaration audit has 26
empty closures, 9 using only `propext`, and 33 using only `propext` and `Quot.sound`. Malformed
countdown scratch/root phases, the unlaunched predecessor endpoint, and one-step-short total fuel
remain fail-closed.

The third-clause-separator milestone then reuses the audited selected 59-rule `Sep` appender and
45-rule cursor advance behind one new total bridge. The resulting literal table has `2272` plus
the eight inherited unary-evaluator rule counts. Every raw input emits the separator at
`V + 1 + 2 * formulaTokensPerClause`, advances the retained coordinate to `+ 1`, and proves by
both direct and specification cursors that the following token is `F`. The output bits are exactly
`encodedFormula.take (2 * (FormulaWidth + 20))`; the external compiled bound adds
`330 + 24*n + 12*FormulaWidth + 12*cursorWord.length` to the predecessor bound. The combined
56-declaration audit has 14 empty closures, 11 using only `propext`, and 31 using only `propext`
and `Quot.sound`. Malformed appender tally/output, malformed cursor scratch, both unlaunched
endpoints, and one-step-short fuel remain fail-closed.

The third-clause-first-literal milestone then reuses the audited 235-rule two-`F` appender/cursor
suffix behind one total symbol-preserving bridge. The resulting literal table has `2516` plus the
eight inherited unary-evaluator rule counts. Every raw input emits the negative sign and unary-zero
terminator at coordinates `V + 1 + 2 * formulaTokensPerClause + 1` and `+ 2`, then retains
coordinate `+ 3`. Constructive schedule proofs identify the third excluded pair as variables zero
and two, the emitted sign and terminator as `F`, and the retained variable-two sign as `F`. The
output bits are exactly `encodedFormula.take (2 * (FormulaWidth + 22))`; the external compiled
bound adds `732 + 48*n + 24*FormulaWidth + 24*cursorWord.length` to the separator bound. The
combined 87-declaration audit has 24 empty closures, 18 using only `propext`, and 45 using only
`propext` and `Quot.sound`. Malformed tally/output in both appenders, malformed scratch in both
cursors, all four unlaunched endpoints, and one-step-short fuel remain fail-closed.

The third-clause-second-literal milestone composes that prefix with a fixed 479-rule
`F T T F` appender/cursor suffix behind one total symbol-preserving bridge. Its nested component
tables have 113, 235, 357, and 479 rules, and the resulting global table has `3004` plus the eight
inherited unary-evaluator rule counts. Every raw input emits the negative sign, two unary units,
and terminator for variable two, retaining coordinate
`V + 1 + 2 * formulaTokensPerClause + 7`. Direct and specification schedule proofs establish
`F`, `T`, `T`, `F`, and the following `Finish`; the output bits are exactly
`encodedFormula.take (2 * (FormulaWidth + 26))`. The external compiled bound adds
`1752 + 96*n + 48*FormulaWidth + 48*cursorWord.length` to the first-literal bound. The complete
145-declaration audit has 46 empty closures, 32 using only `propext`, and 67 using only `propext`
and `Quot.sound`. Malformed tally/output in all four appenders, malformed scratch in all four
cursors, all eight unlaunched endpoints, and one-step-short fuel remain fail-closed.

The complete-third-clause milestone then reuses the selected 59-rule `Finish` appender and 45-rule
cursor advance behind one total symbol-preserving bridge. The resulting literal table has `3126`
plus the eight inherited unary-evaluator rule counts. Every raw input emits the clause terminator,
advances from `V + 1 + 2 * formulaTokensPerClause + 7` to `+ 8`, and proves by both direct and
specification cursors that the retained opportunity is the first in-range padding slot. The output
bits are exactly `encodedFormula.take (2 * (FormulaWidth + 27))`; the external compiled bound adds
`498 + 24*n + 12*FormulaWidth + 12*cursorWord.length` to the second-literal bound. The combined
57-declaration audit has 14 empty closures, 10 using only `propext`, and 33 using only `propext`
and `Quot.sound`. Malformed appender tally/output, malformed cursor scratch, both unlaunched
endpoints, and one-step-short fuel remain fail-closed.

The third-clause-padding milestone then evaluates the exact remaining count
`D = (V - 1) * (V + 6) + 4 = formulaTokensPerClause - 8`, reuses the audited 25-rule
`PaddingCountdown` table to consume those opportunities, and evaluates the target coordinate.
Three total `WorkChain` bridges compose those phases with the complete-third-clause prefix. The
literal global table has `3178` plus the eight inherited/generated predecessor unary-evaluator rule
counts and the two new evaluator rule counts. Every raw input follows an exact trace through all
`D` padding coordinates and reaches `V + 1 + 3 * formulaTokensPerClause`, whose direct schedule
outcome is the fourth clause's opening `Sep`. No token is emitted: the final bits remain exactly
`encodedFormula.take (2 * (FormulaWidth + 27))`. The compiled bound adds two evaluator costs,
three six-step launches, and the exact countdown term
`6 * (D * (2 * R + 8) + D^2)` to the predecessor bound. The combined 68-declaration audit has 26
empty closures, 9 using only `propext`, and 33 using only `propext` and `Quot.sound`. Malformed
countdown scratch/root phases, the unlaunched predecessor endpoint, and one-step-short total fuel
remain fail-closed.

The fourth-clause-separator milestone then places the reused selected 59-rule `Sep` appender and
45-rule cursor advance after that complete padding run through one outer total nine-symbol bridge.
The resulting global table has `3300` plus the ten inherited/generated unary-evaluator rule counts.
Every raw input follows exact predecessor, appender, cursor, bridge, suffix, and combined traces;
emits exactly the separator at `V + 1 + 3 * formulaTokensPerClause`; and advances the retained
coordinate to `+ 1`, whose direct and specification outcomes are the following negative sign `F`.
The output bits are exactly `encodedFormula.take (2 * (FormulaWidth + 28))`; the external compiled
bound is `BuilderThirdClausePaddingRun.rawTimeBound + 426 + 24*n + 12*FormulaWidth +
12*cursorWord.length`. The combined 56-declaration audit covers all 48 new public declarations and
eight reused separator/cursor interfaces: 14 closures are empty, 11 use only `propext`, and 31 use
only `propext` and `Quot.sound`. Malformed appender tally/output, malformed cursor scratch, both
unlaunched endpoints, and one-step-short total fuel remain fail-closed.

The fourth-clause-first-literal milestone then places the reused 357-rule selected `F T F`
appender/cursor suffix after the separator prefix through one outer total nine-symbol bridge. The
resulting table has `3666` plus the ten inherited/generated unary-evaluator rule counts. Every raw
input emits the complete first negative literal on variable one, advances the retained coordinate
to `V + 1 + 3 * formulaTokensPerClause + 4`, and proves the following token is the second
literal's negative sign `F`. The output bits are exactly
`encodedFormula.take (2 * (FormulaWidth + 31))`; the external bound is
`BuilderFourthClauseSeparatorStep.rawTimeBound + 1422 + 72*n + 36*FormulaWidth +
36*cursorWord.length`. The 115-declaration audit has 33 empty closures, 25 using only `propext`,
and 57 using only `propext` and `Quot.sound`. Malformed tally/output/scratch states, all six
unlaunched endpoints, and one-step-short fuel remain fail-closed.

The fourth-clause-second-literal milestone then places the reused 479-rule selected `F T T F`
appender/cursor suffix after the first-literal prefix through one outer total nine-symbol bridge.
The resulting table has `4154` plus the ten inherited/generated unary-evaluator rule counts. Every
raw input emits the complete second negative literal on variable two, advances the retained
coordinate to `V + 1 + 3 * formulaTokensPerClause + 8`, and proves the following token is
`Finish`. The output bits are exactly `encodedFormula.take (2 * (FormulaWidth + 35))`; the
external bound is `BuilderFourthClauseFirstLiteralPrefix.rawTimeBound + 2232 + 96*n +
48*FormulaWidth + 48*cursorWord.length`. The 147-declaration audit has 46 empty closures, 32
using only `propext`, and 69 using only `propext` and `Quot.sound`. Malformed tally/output/scratch
states, all eight unlaunched endpoints, and one-step-short fuel remain fail-closed.

The complete-fourth-clause milestone then places a selected 59-rule `Finish` appender and the
existing 45-rule cursor after the second-literal prefix through two total nine-symbol bridges. The
selected suffix has 113 rules and the resulting table has `4276` plus the ten inherited/generated
unary-evaluator rule counts. Every raw input emits the clause-four terminator, advances the retained
coordinate to `V + 1 + 3 * formulaTokensPerClause + 9`, and proves the following token is padding.
The output bits are exactly `encodedFormula.take (2 * (FormulaWidth + 36))`; the external bound is
`BuilderFourthClauseSecondLiteralPrefix.rawTimeBound + 618 + 24*n + 12*FormulaWidth +
12*cursorWord.length`. The 57-declaration audit has 14 empty closures, 10 using only `propext`,
and 33 using only `propext` and `Quot.sound`. Malformed tally/output/scratch states, both
unlaunched endpoints, and one-step-short fuel remain fail-closed.

The fourth-clause-padding milestone then evaluates the exact remaining count
`(V - 1) * (V + 6) + 3 = formulaTokensPerClause - 9`, runs the reused 25-rule padding countdown,
and materializes `V + 1 + 4 * formulaTokensPerClause` through two new unary evaluators and three
total nine-symbol bridges. The resulting table has `4328` plus twelve inherited/generated
unary-evaluator rule counts. Every raw input traverses the entire remaining clause-four padding
block without emitting a token, preserves `encodedFormula.take (2 * (FormulaWidth + 36))`, and
stops at the first opportunity in the intentionally empty fifth fixed-width clause slot. Direct
lookup and the specification cursor both prove that endpoint is padding. The external compiled
bound is `BuilderFourthClausePrefix.rawTimeBound + 18` plus six times the count-evaluator work,
countdown bound, and target-evaluator work. The 68-declaration audit covers all 65 new public
declarations and three reused countdown interfaces: 26 closures are empty, 9 use only `propext`,
and 33 use only `propext` and `Quot.sound`. Both malformed countdown phases, the unlaunched
predecessor endpoint, and one-step-short fuel remain fail-closed.

The fifth-clause-padding milestone then evaluates one complete fixed-width clause count
`formulaTokensPerClause`, runs the reused 25-rule padding countdown, and materializes
`V + 1 + 5 * formulaTokensPerClause` through two new unary evaluators and three total nine-symbol
bridges. The resulting table has `4380` plus fourteen inherited/generated unary-evaluator rule
counts. Every raw input traverses the entire intentionally empty fifth clause rectangle without
emitting a token, preserves `encodedFormula.take (2 * (FormulaWidth + 36))`, and stops at the first
opportunity in the intentionally empty sixth fixed-width clause slot. Direct lookup and the
specification cursor prove every traversed coordinate and the endpoint are padding. The external
compiled bound is `BuilderFourthClausePaddingRun.rawTimeBound + 18` plus six times the
count-evaluator work, countdown bound, and target-evaluator work. The 68-declaration audit covers
all 65 new public declarations and three reused countdown interfaces: 28 closures are empty, 9 use
only `propext`, and 31 use only `propext` and `Quot.sound`. Both malformed countdown phases, the
unlaunched predecessor endpoint, and one-step-short fuel remain fail-closed.

The first-constraint-padding milestone then evaluates the exact remaining empty suffix
`(V - 2) * (V + 2) * formulaTokensPerClause =
(formulaClauseSlotsPerConstraint - 5) * formulaTokensPerClause`, runs the reused 25-rule padding
countdown, and materializes
`V + 1 + formulaClauseSlotsPerConstraint * formulaTokensPerClause` through two new unary
evaluators and three total nine-symbol bridges. The resulting table has `4432` plus sixteen
inherited/generated unary-evaluator rule counts. Every raw input traverses the sixth and all later
empty clause rectangles belonging to the first scheduled constraint without emitting a token,
preserves `encodedFormula.take (2 * (FormulaWidth + 36))`, and stops at the `Sep` beginning the
second scheduled constraint. Direct lookup and the specification cursor prove every traversed
coordinate is padding and the endpoint is that separator. The external compiled bound is
`BuilderFifthClausePaddingRun.rawTimeBound + 18` plus six times the count-evaluator work,
countdown bound, and target-evaluator work. The 68-declaration audit covers all 65 new public
declarations and three reused countdown interfaces: 26 closures are empty, 9 use only `propext`,
and 33 use only `propext` and `Quot.sound`. Both malformed countdown phases, the unlaunched
predecessor endpoint, and one-step-short fuel remain fail-closed.

The second-constraint-separator milestone then composes that endpoint with the reused selected
59-rule `Sep` appender and fixed 45-rule cursor advance through one outer and one inner total
nine-symbol bridge. The resulting table has `4554` plus sixteen inherited/generated unary-evaluator
rule counts. Every raw input emits exactly the separator beginning the second scheduled constraint,
preserves `encodedFormula.take (2 * (FormulaWidth + 37))`, and advances the retained unary coordinate
to `V + 1 + formulaClauseSlotsPerConstraint * formulaTokensPerClause + 1`. Direct lookup and the
specification cursor prove that the following token is `T`, the positive sign beginning the next
constraint's at-least-one clause. The external compiled bound evaluates to
`BuilderFirstConstraintPaddingRun.rawTimeBound + 534 + 24*n + 12*FormulaWidth +
12*cursorWord.length`. The 56-declaration combined audit covers all 48 new public declarations plus
eight reused separator/cursor and dead-state interfaces: 14 closures are empty, 11 use only
`propext`, and 31 use only `propext` and `Quot.sound`. Malformed appender tally/output states,
malformed cursor scratch, both unlaunched endpoints, and one-step-short fuel remain fail-closed.

The second-constraint-first-literal-sign milestone then composes that separator endpoint with the
reused selected 59-rule `T` appender and fixed 45-rule cursor advance through one outer and one
inner total nine-symbol bridge. The resulting table has `4676` plus sixteen inherited/generated
unary-evaluator rule counts. Every raw input emits exactly the positive sign beginning the second
constraint's first literal, preserves `encodedFormula.take (2 * (FormulaWidth + 38))`, and advances
the retained unary coordinate to
`V + 1 + formulaClauseSlotsPerConstraint * formulaTokensPerClause + 2`. A constructive schedule
case split handles both the width-one head constraint and the wider-tape position-one symbol
constraint; direct lookup and the specification cursor prove that the following token is the first
unary `T` of a nonzero variable index. The external compiled bound evaluates to
`BuilderSecondConstraintSeparatorStep.rawTimeBound + 546 + 24*n + 12*FormulaWidth +
12*cursorWord.length`. The 56-declaration combined audit covers all 48 new public declarations plus
eight reused true-token/cursor and dead-state interfaces: 14 closures are empty, 11 use only
`propext`, and 31 use only `propext` and `Quot.sound`. Malformed appender tally/output states,
malformed cursor scratch, both unlaunched endpoints, and one-step-short fuel remain fail-closed.

The second-constraint-first-literal-first-unary-unit milestone composes that sign endpoint with the
same selected 59-rule `T` appender and fixed 45-rule cursor advance through one outer and one inner
total nine-symbol bridge. The resulting table has `4798` plus sixteen inherited/generated
unary-evaluator rule counts. Every raw input emits exactly the first unary `T` of the second
constraint's first variable index, preserves `encodedFormula.take (2 * (FormulaWidth + 39))`, and
advances the retained coordinate to
`V + 1 + formulaClauseSlotsPerConstraint * formulaTokensPerClause + 3`. The constructive schedule
case split strengthens the prior nonzero-index fact to show the selected index is at least three;
direct lookup and the specification cursor therefore prove the following token is the second unary
`T`. The external compiled bound evaluates to
`BuilderSecondConstraintFirstLiteralSignStep.rawTimeBound + 558 + 24*n + 12*FormulaWidth +
12*cursorWord.length`. The measured 56-declaration audit covers all 48 new public declarations plus
eight reused true-token/cursor and dead-state interfaces: 14 closures are empty, 11 use only
`propext`, and 31 use only `propext` and `Quot.sound`. Malformed appender tally/output states,
malformed cursor scratch, both unlaunched endpoints, and one-step-short fuel remain fail-closed.

The second-constraint-first-literal-second-unary-unit milestone composes that first-unary-unit
endpoint with the same selected 59-rule `T` appender and fixed 45-rule cursor advance through one
outer and one inner total nine-symbol bridge. The resulting table has `4920` plus sixteen
inherited/generated unary-evaluator rule counts. Every raw input emits exactly the second unary `T`
of the second constraint's first variable index, preserves
`encodedFormula.take (2 * (FormulaWidth + 40))`, and advances the retained coordinate to
`V + 1 + formulaClauseSlotsPerConstraint * formulaTokensPerClause + 4`. The constructive schedule
proof again establishes that the selected index is at least three; direct lookup and the
specification cursor therefore prove the following token is the third unary `T`. The external
compiled bound evaluates to
`BuilderSecondConstraintFirstLiteralFirstUnaryUnitStep.rawTimeBound + 570 + 24*n +
12*FormulaWidth + 12*cursorWord.length`. The measured 56-declaration audit covers all 48 new public
declarations plus eight reused true-token/cursor and dead-state interfaces: 14 closures are empty,
11 use only `propext`, and 31 use only `propext` and `Quot.sound`. Malformed appender tally/output
states, malformed cursor scratch, both unlaunched endpoints, and one-step-short fuel remain
fail-closed.

The second-constraint-first-literal-third-unary-unit milestone composes that second-unary-unit
endpoint with the same selected 59-rule `T` appender and fixed 45-rule cursor advance through one
outer and one inner total nine-symbol bridge. The resulting table has `5042` plus sixteen
inherited/generated unary-evaluator rule counts. Every raw input emits exactly the third and final
unary `T` of the second constraint's first variable index, preserves
`encodedFormula.take (2 * (FormulaWidth + 41))`, and advances the retained coordinate to
`V + 1 + formulaClauseSlotsPerConstraint * formulaTokensPerClause + 5`. The constructive schedule
case split proves the index is exactly three: the width-one branch has time bound zero and head
index three, while the wider branch selects the position-one blank-symbol index three. Direct
lookup and the specification cursor therefore prove the following token is the terminating `F`.
The external compiled bound evaluates to
`BuilderSecondConstraintFirstLiteralSecondUnaryUnitStep.rawTimeBound + 582 + 24*n +
12*FormulaWidth + 12*cursorWord.length`. The 56-declaration audit covers all 48 new public
declarations plus eight reused true-token/cursor and dead-state interfaces. Exactly 14 closures are
empty, 11 use only `propext`, and 31 use only `propext` and `Quot.sound`.
Malformed appender tally/output states, malformed cursor scratch, both unlaunched endpoints, and
one-step-short fuel remain fail-closed.

The second-constraint-first-literal-terminator milestone composes that third-unary-unit endpoint
with the selected 59-rule `F` appender and fixed 45-rule cursor advance through one outer and one
inner total nine-symbol bridge. The resulting table has `5164` plus sixteen inherited/generated
unary-evaluator rule counts. Every raw input emits exactly the terminating `F`, preserves
`encodedFormula.take (2 * (FormulaWidth + 42))`, and advances the retained coordinate to
`V + 1 + formulaClauseSlotsPerConstraint * formulaTokensPerClause + 6`. A constructive schedule
case split proves that the retained next token is `Finish` when the tableau tape width is one and
the positive `T` beginning the next literal at wider widths. The external compiled bound evaluates
to `BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.rawTimeBound + 594 + 24*n +
12*FormulaWidth + 12*cursorWord.length`. The 56-declaration audit covers all 48 new public
declarations plus eight reused false-token/cursor and dead-state interfaces: 14 closures are empty,
11 use only `propext`, and 31 use only `propext` and `Quot.sound`. Malformed appender tally/output
states, malformed cursor scratch, both unlaunched endpoints, and one-step-short fuel remain
fail-closed.

The second-constraint-first-literal-successor-token milestone then evaluates the represented
tableau width and enters one reused 59-rule token appender through a fixed 93-rule branch table.
At width one the branch appends `Finish`; at every wider width it appends `T`. A final unary
evaluator materializes the following coordinate. The global table has `5284` plus eighteen
inherited/generated unary-evaluator rule counts. Every raw input preserves
`encodedFormula.take (2 * (FormulaWidth + 43))` and advances the retained coordinate to
`V + 1 + formulaClauseSlotsPerConstraint * formulaTokensPerClause + 7`. Direct lookup and the
specification cursor prove that the next opportunity is padding at width one and unary `T` at
wider widths, but the machine does not emit it. The external compiled bound evaluates to
`BuilderSecondConstraintFirstLiteralTerminatorStep.rawTimeBound + 600 + 24*n +
12*FormulaWidth + 12*width + 12*widthRootPrefixLength + 6*widthWorkSteps +
6*targetWorkSteps`. The 82-declaration audit covers all 80 new public declarations plus two
strengthened predecessor boundaries: 37 closures are empty, 12 use only `propext`, and 33 use
only `propext` and `Quot.sound`. No closure reaches `Classical.choice` or a project axiom.
The predecessor endpoint before launch and one-step-short fuel remain fail-closed, and the
component machines retain their malformed-workspace guarantees.

The second-constraint-padding-or-unary-opportunity milestone consumes that
retained schedule position with a 93-rule optional appender. At width one the
controller's done exit bridges directly to the appender accept state and
emits no token; at every wider width the more exit launches the appender at
`T`, emitting the first unary unit of the second literal. A final unary
evaluator materializes the next coordinate. The global table has `5404` plus
twenty inherited/generated unary-evaluator rule counts. Its exact bits are
`encodedFormula.take (2 * (FormulaWidth + 43 + if tapeWidth = 1 then 0 else
1))`, and its retained coordinate is
`V + 1 + formulaClauseSlotsPerConstraint * formulaTokensPerClause + 8`.
Direct lookup proves the following slot is again padding at width one and the
second unary `T` at every wider width. The external compiled bound evaluates
to `BuilderSecondConstraintFirstLiteralSuccessorTokenStep.rawTimeBound + 612
+ 24*n + 12*FormulaWidth + 12*width + 12*widthRootPrefixLength +
6*widthWorkSteps + 6*targetWorkSteps`. The 82-declaration audit covers all 80
new public declarations plus two strengthened schedule boundaries: 37
closures are empty, 12 use only `propext`, and 33 use only `propext` and
`Quot.sound`. No closure reaches `Classical.choice` or a project axiom.

The second-constraint-second-padding-or-unary-opportunity milestone reuses
the same reviewed 93-rule optional appender at the next schedule position.
At width one the controller again takes its direct skip bridge and emits no
token; at every wider width it appends exactly the second unary `T` of the
second literal. The global table has `5524` plus twenty-two
inherited/generated unary-evaluator rule counts. Its exact bits are
`encodedFormula.take (2 * (FormulaWidth + 43 + if tapeWidth = 1 then 0 else
2))`, and its retained coordinate is
`V + 1 + formulaClauseSlotsPerConstraint * formulaTokensPerClause + 9`.
Direct lookup and the specification cursor prove that the following slot is
again padding at width one and the third unary `T` at every wider width. The
external compiled bound evaluates to
`BuilderSecondConstraintPaddingOrUnaryOpportunityStep.rawTimeBound + 624 +
24*n + 12*FormulaWidth + 12*width + 12*widthRootPrefixLength +
6*widthWorkSteps + 6*targetWorkSteps`. The 82-declaration audit covers all 66
new public declarations, fourteen reused optional-appender interfaces, and
two strengthened schedule boundaries: 37 closures are empty, 12 use only
`propext`, and 33 use only `propext` and `Quot.sound`. No closure reaches
`Classical.choice` or a project axiom.

The second-constraint-third-padding-or-unary-opportunity milestone reuses
the same reviewed 93-rule optional appender at the following schedule
position. At width one the controller again takes its direct skip bridge and
emits no token; at every wider width it appends exactly the third unary `T`
of the second literal. The global table has `5644` plus twenty-four
inherited/generated unary-evaluator rule counts. Its exact bits are
`encodedFormula.take (2 * (FormulaWidth + 43 + if tapeWidth = 1 then 0 else
3))`, and its retained coordinate is
`V + 1 + formulaClauseSlotsPerConstraint * formulaTokensPerClause + 10`.
Direct lookup and the specification cursor prove that the following slot is
again padding at width one and the fourth unary `T` at every wider width. The
external compiled bound evaluates to
`BuilderSecondConstraintSecondPaddingOrUnaryOpportunityStep.rawTimeBound +
636 + 24*n + 12*FormulaWidth + 12*width + 12*widthRootPrefixLength +
6*widthWorkSteps + 6*targetWorkSteps`. The 82-declaration audit covers all 66
new public declarations, fourteen reused optional-appender interfaces, and
two strengthened schedule boundaries: 37 closures are empty, 12 use only
`propext`, and 33 use only `propext` and `Quot.sound`. No closure reaches
`Classical.choice` or a project axiom.

The second-constraint-fourth-padding-or-unary-opportunity milestone reuses
the same reviewed 93-rule optional appender at the following schedule
position. At width one the controller again takes its direct skip bridge and
emits no token; at every wider width it appends exactly the fourth unary `T`
of the second literal. The global table has `5764` plus twenty-six
inherited/generated unary-evaluator rule counts. Its exact bits are
`encodedFormula.take (2 * (FormulaWidth + 43 + if tapeWidth = 1 then 0 else
4))`, and its retained coordinate is
`V + 1 + formulaClauseSlotsPerConstraint * formulaTokensPerClause + 11`.
Direct lookup and the specification cursor prove that the following slot is
padding at width one and the terminating `F` at every wider width. The
external compiled bound evaluates to
`BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.rawTimeBound +
648 + 24*n + 12*FormulaWidth + 12*width + 12*widthRootPrefixLength +
6*widthWorkSteps + 6*targetWorkSteps`. The 82-declaration audit covers all 66
new public declarations, fourteen reused optional-appender interfaces, and
two strengthened schedule boundaries: 37 closures are empty, 12 use only
`propext`, and 33 use only `propext` and `Quot.sound`. No closure reaches
`Classical.choice` or a project axiom.

The second-constraint-fifth-padding-or-terminator-opportunity milestone
uses a new 93-rule optional-terminator controller over the audited token
appender rule table. At width one the controller takes its direct skip
bridge and emits no token; at every wider width it appends exactly the
terminating `F` of the second literal. The global table has `5884` plus
twenty-eight inherited/generated unary-evaluator rule counts. Its exact bits
are `encodedFormula.take (2 * (FormulaWidth + 43 + if tapeWidth = 1 then 0
else 5))`, and its retained coordinate is
`V + 1 + formulaClauseSlotsPerConstraint * formulaTokensPerClause + 12`.
Direct lookup and the specification cursor prove that the following slot is
padding at width one and the opening unary `T` of the following literal at
every wider width. The external compiled bound evaluates to
`BuilderSecondConstraintFourthPaddingOrUnaryOpportunityStep.rawTimeBound +
660 + 24*n + 12*FormulaWidth + 12*width + 12*widthRootPrefixLength +
6*widthWorkSteps + 6*targetWorkSteps`. The 82-declaration audit covers all 66
new outer public declarations, fourteen new optional-terminator interfaces,
and two strengthened schedule boundaries: 37 closures are empty, 12 use
only `propext`, and 33 use only `propext` and `Quot.sound`. No closure may reach
`Classical.choice` or a project axiom.

The second-constraint-sixth-padding-or-opening-unary-opportunity milestone
reuses the reviewed 93-rule optional appender at the following schedule
position. At width one the controller again takes its direct skip bridge and
emits no token; at every wider width it appends exactly the opening positive
`T` of the following literal. The global table has `6004` plus thirty
inherited/generated unary-evaluator rule counts. Its exact bits are
`encodedFormula.take (2 * (FormulaWidth + 43 + if tapeWidth = 1 then 0 else
6))`, and its retained coordinate is
`V + 1 + formulaClauseSlotsPerConstraint * formulaTokensPerClause + 13`.
Direct lookup and the specification cursor prove that the following slot is
padding at width one and the first unary-index `T` of the following literal
at every wider width. The external compiled bound evaluates to
`BuilderSecondConstraintFifthPaddingOrTerminatorOpportunityStep.rawTimeBound +
672 + 24*n + 12*FormulaWidth + 12*width + 12*widthRootPrefixLength +
6*widthWorkSteps + 6*targetWorkSteps`. The 82-declaration audit covers all 66
new public declarations, fourteen reused optional-appender interfaces, and
two strengthened schedule boundaries: 37 closures are empty, 12 use only
`propext`, and 33 use only `propext` and `Quot.sound`. No closure may reach
`Classical.choice` or a project axiom.

The second-constraint-seventh-padding-or-unary-opportunity milestone reuses
the reviewed 93-rule optional appender at the next schedule position. At
width one the controller again takes its direct skip bridge and emits no
token; at every wider width it appends exactly the first unary-index `T` of
the following literal. The global table has `6124` plus thirty-two
inherited/generated unary-evaluator rule counts. Its exact bits are
`encodedFormula.take (2 * (FormulaWidth + 43 + if tapeWidth = 1 then 0 else
7))`, and its retained coordinate is
`V + 1 + formulaClauseSlotsPerConstraint * formulaTokensPerClause + 14`.
Direct lookup and the specification cursor prove that the following slot is
padding at width one and the second unary-index `T` of the following literal
at every wider width. The external compiled bound evaluates to
`BuilderSecondConstraintSixthPaddingOrOpeningUnaryOpportunityStep.rawTimeBound +
684 + 24*n + 12*FormulaWidth + 12*width + 12*widthRootPrefixLength +
6*widthWorkSteps + 6*targetWorkSteps`. The 82-declaration audit covers all 66
new public declarations, fourteen reused optional-appender interfaces, and
two strengthened schedule boundaries: 37 closures are empty, 12 use only
`propext`, and 33 use only `propext` and `Quot.sound`. No closure may reach
`Classical.choice` or a project axiom.

This earns the complete first four populated clauses, traverses all four clauses' remaining padding,
crosses every remaining empty clause rectangle of the first scheduled constraint, and emits the
separator, positive first-literal sign, all three unary index units, the terminating `F`, and its
width-selected `Finish` or `T` successor in the second constraint's first literal. It also consumes
the next seven schedule opportunities, emitting nothing for width-one padding or the first four unary
`T` tokens, terminating `F` of the second literal, and opening positive and first unary-index `T`
tokens of the following literal at wider widths.
It is not a general dynamic cursor or an arbitrary raw slot decoder: no machine emits the following
padding or second-unary-index-`T` opportunity, traverses the rest of the second constraint, or emits the
remaining formula body,
composes a complete raw formula builder with a construction-runtime proof, or packages
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
construction and cross-instance `BaselineDistinct` are supplied by later milestones; this local
accounting layer alone does not establish them.

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

This is not the report locked-NAND threshold theorem. The later global-candidate module now
instantiates the typed `baselineCandidate`, `fullCandidate`, and
`initialOutputsPreserved` fields with circuit SAT and `lockedBaselineCount` as their intended
indices. The missing fields at the candidate-assembly boundary were `baselineConditions`,
`unsatisfiableFinalZero`, and `satisfiableFinalConditions`. The following two milestones now
instantiate `baselineConditions` and the whole-carrier `unsatisfiableFinalZero` law, leaving
exactly `satisfiableFinalConditions`. The answer-independent uniform builder and its polynomial
bound are not supplied. The conditional module is not yet connected to the abstract
`PNP.LockedNANDThreshold` language.

`LockedNANDCarrierTrace` now closes the next unbounded Section 17 dependency for arbitrary finite
NAND circuits. It defines the exact disjoint `X ⊔ T ⊔ O ⊔ R ⊔ L ⊔ {z}` carrier with width
`inputs + 6*gates + 1`, proves total encode/decode inverse laws, carrier-family separation, and
freshness of `z`, and generates exactly three distinguished source/trace checks per actual gate.
It then proves both directions of `TraceEquivalence` by topological induction: every source input
has a canonical coherent extension, and every accepted trace equals genuine program evaluation at
every gate. The existential trace predicate is therefore satisfiable exactly when the declared
source-circuit output is satisfiable.

This is the legacy trace lemma rather than the complete locked-NAND threshold construction. Its
carrier is consumed by the following global-candidate milestone. Cross-instance
`BaselineDistinct`, both whole-carrier final-output branch laws, uniform polynomial construction,
and the threshold do not follow from the carrier/trace milestone alone. See
[`lean_locked_nand_carrier_trace.md`](./lean_locked_nand_carrier_trace.md).

`LockedNANDGlobalCandidates` now reconstructs the next Section 17 layer uniformly over every
finite typed circuit. It assembles source and trace macros in topological order, folds all
distinguished checks with the exact nonempty prefix tree, and proves the resulting raw count is
`lockedBaselineCount`. Writing that count as `B`, Lean constructs the exact `B`-gate/`B`-output
square baseline and exact `B + 4`-gate/`B + 1`-output extension.

Every initial full-candidate output is proved equal to its corresponding baseline output. The new
final coordinate is exactly `z ∧ TraceChecks ∧ T_out`; both candidates have constant-free
internal syntax, and every baseline output is structurally independent of the fresh `z` input.
This constructs three of the six conditional-boundary fields. Candidate assembly alone does not
prove global `BaselineDistinct`, `unsatisfiableFinalZero`, `satisfiableFinalConditions`, the
threshold, or the uniform polynomial bitstring builder. Later milestones now discharge all three
of those semantic fields. See
[`lean_locked_nand_global_candidates.md`](./lean_locked_nand_global_candidates.md).

The global `BaselineDistinct` milestone now closes the fourth field. Lean proves that every
exposed baseline gate is semantically nonconstant, differs from every positive projection of the
carrier, and computes a function distinct from every other exposed baseline gate. The proof is
uniform over every finite topological NAND circuit and combines per-macro fresh-lock separation
with two retained check-lock anchors shared by the complete prefix fold. The square baseline
therefore has exhaustive `referenceMinimum` exactly `B`.

The five public milestone theorems use only `propext` and `Quot.sound`; they do not reach
`Classical.choice` or a project axiom. Baseline distinctness alone does not prove either
whole-carrier branch law, the global residual-slack result, the uniform polynomial bitstring
builder, or the locked-NAND threshold. See
[`lean_locked_nand_global_baseline_distinct.md`](./lean_locked_nand_global_baseline_distinct.md).

`LockedNANDGlobalUnsatisfiableFinalZero` now closes the fifth conditional-boundary field. If the
source circuit is unsatisfiable, Lean proves that the full final coordinate is false on every
carrier valuation, not merely on coherent traces. Projecting the first `B` outputs recovers the
baseline, while appending the forced-zero output preserves equivalence without adding a gate;
together these bounds prove the full exhaustive `referenceMinimum` is exactly `B`.

Both public theorems use only `propext` and `Quot.sound`; neither reaches `Classical.choice` or a
project axiom. This milestone by itself does not discharge the satisfiable branch. See
[`lean_locked_nand_global_unsatisfiable_final_zero.md`](./lean_locked_nand_global_unsatisfiable_final_zero.md).

`LockedNANDGlobalSemanticThreshold` now closes the sixth and final typed premise. Around a
satisfying coherent trace, toggling only the fresh final-lock bit toggles the full final output
while leaving every baseline output unchanged. Lean uses that pair of valuations to prove
nonconstancy, separation from every positive carrier projection, and separation from every
baseline coordinate. The special final-lock projection is handled by a separate valuation whose
output-trace bit is false.

All six fields are packaged from the same answer-independent candidates. Consequently, for every
finite topological NAND circuit with baseline `B`, satisfiability implies an exhaustive minimum in
`[B + 1, B + 4]`, unsatisfiability gives minimum exactly `B`, the displayed candidate has residual
slack at most four, and satisfiability is equivalent to the minimum crossing `B + 1`. The private
decidability instance is exhaustive finite input search and has no polynomial-runtime claim.

The eight-declaration audit uses exactly `propext` and `Quot.sound`, never `Classical.choice` or a
project axiom. This closes the typed semantic threshold, not the report's encoded polynomial-time
builder or the abstract `PNP.LockedNANDThreshold` language. See
[`lean_locked_nand_global_semantic_threshold.md`](./lean_locked_nand_global_semantic_threshold.md).

`PNP.Concrete.LockedNANDEncoding` and `PNP.Concrete.LockedNANDReduction` now
place that typed theorem behind one strict version-zero bit grammar. The
boundary includes raw topological NAND syntax, direct legacy output
normalization semantics, constructive intrinsic validation, exact round trips,
the complete full-candidate output word, and the source-derived baseline.
Malformed source bytes map to the empty word, which is proved outside the
target language. For every bitstring, source satisfiability is equivalent to
the encoded full candidate crossing its encoded threshold.

The 48-declaration audit has four empty closures, 37 using only `propext`, and
seven using only `propext` with `Quot.sound`. This module is a pure semantic
transformation and does not by itself supply a parser/validator machine,
emitter machine, `RawRefinement`, `PolynomialReduction`, or
runtime/output-size proof. The following source-parser milestone implements
and bounds the validator against these exact bytes, and the target-emitter
milestone implements the downstream exact byte construction. See
[`lean_concrete_locked_nand_semantic_reduction.md`](./lean_concrete_locked_nand_semantic_reduction.md).

`PNP.Concrete.LockedNANDSourceParser` now aggregates the completed bounded
source parser. Its executable layer is a direct nine-symbol `WorkMachine` with
228 control states and 2,052 pairwise query-distinct literal rules; its rule
construction does not call the semantic decoder. Constructive normal forms
classify reserved or partial four-bit tokens and every strict circuit-grammar
failure. Separate exact-trace modules prove canonical packed layouts, an accepting boundary that
exposes the original source bytes, and a generic rejecting cleanup boundary
that exposes the empty output. The compiled layer records
`4096 * (n + 1)^3` work transitions and six raw transitions per work
transition as a literal polynomial expression and proves ordinary-start
blank equivalence.

The total exact theorem now dispatches every bitstring—valid circuits,
grammar failures, and well-encoded circuits with invalid references—to a
halted endpoint within `4096 * (n + 1)^3` work transitions. The endpoint is
accepting exactly for `ValidEncodedCircuit`; valid source bytes are preserved
verbatim, while every invalid source exposes the empty output. The compiled
machine accepts with the same iff, returns exactly `validatedSourceBytes`,
and cannot time out within `6 * 4096 * (n + 1)^3` raw transitions.

The compiled boundary is packaged as a `PolynomialTimeMachine`, a
nonexpanding `PolynomialTimeFunction`, and the validator program's exact leaf
`RawRefinement`. The declaration audit covers the complete public parser
surface and permits only the approved Lean-standard closure, with no project
axiom, host-side decoder, schedule lookup, or caller execution certificate.
This completes the parser/validator milestone, but not the target emitter or
the composed source-to-target reduction. See
[`lean_concrete_locked_nand_source_parser.md`](./lean_concrete_locked_nand_source_parser.md).

`PNP.Concrete.LockedNANDTargetEmitter` now aggregates the complete
grammar-only target builder. The fixed controller contains 1,387,921 literal
rules, keeps all control and primitive-block states disjoint, and constructs
its rule table without the semantic decoder, target function, schedule
lookup, or caller certificate. On every bitstring it either rejects malformed
grammar with empty output or accepts a decoded raw circuit and emits exactly
`RawBuilder.targetBytes`.

The all-input work trace is bounded by a literal degree-five polynomial; raw
compilation multiplies that bound by six. A separate quadratic polynomial
bounds emitted bytes. The compiled interface proves exact output,
grammar-decoder acceptance, and non-timeout, then packages a
`PolynomialTimeMachine`, standalone `PolynomialTimeFunction`, and leaf
`RawRefinement`.

Composition with the strict source parser computes
`buildLockedNANDInstance` on every input and has a recursively compiled
`RawRefinement`. In particular, a grammar-decoded circuit with an invalid
reference is accepted at the standalone grammar boundary but cleared by the
strict composition. The 3,295-declaration transcript permits only empty
closure, `propext`, and `propext` with `Quot.sound`. This closes target
emission and strict parser/emitter composition. The following reduction
milestone packages that composition; this emitter module alone does not
discharge the abstract `PNP.LockedNANDThreshold` assumption. See
[`lean_concrete_locked_nand_target_emitter.md`](./lean_concrete_locked_nand_target_emitter.md).

`PNP.Concrete.LockedNANDPolynomialReduction` now packages the existing strict
parser/emitter function as
`PolynomialReduction EncodedNANDSAT EncodedLockedNANDThreshold`. Its function
field is exactly `strictLockedNANDPolynomialTimeFunction`; its output theorem
is exactly `buildLockedNANDInstance`; and its correctness theorem is an iff on
every bitstring. The package also exposes the corresponding `ReducesTo`
witness and preserves the recursive `FunctionProgram.RawRefinement`.

The audit covers all seven new public declarations and nine reused boundary
interfaces. It permits only the existing Lean-standard `propext` and
`Quot.sound` closure, with no project axiom, `Classical.choice`, host lookup,
or caller certificate. This closes the concrete polynomial-reduction
packaging edge in the legacy locked-NAND route. It does not connect the
concrete target language to the abstract `PNP.LockedNANDThreshold`, prove the
report-level threshold theorem, put CNFSAT in P, establish NP-hardness, or
prove P = NP. See
[`lean_concrete_locked_nand_polynomial_reduction.md`](./lean_concrete_locked_nand_polynomial_reduction.md).

`PNP.Concrete.CNFToNAND` now supplies the next legacy-route semantic edge.
It traverses every decoded CNF formula structurally and constructs an
intrinsically topological NAND program without querying satisfiability. Lean
proves exact valuation semantics, strict canonical decoder inversion,
well-formed encoded output, the exact gate count, a quadratic serialized
output bound in external input length, and fail-closed correctness on every
bitstring. Empty formulas are true, empty clauses are false, and either sign
of an out-of-range literal is false.

The resulting all-bitstring theorem is
`CNFSAT bits ↔ EncodedNANDSAT (compileEncodedCNFToNAND bits)`, and pure
composition with the locked-NAND builder reaches
`EncodedLockedNANDThreshold`. See
[`lean_concrete_cnf_to_nand_semantic_compiler.md`](./lean_concrete_cnf_to_nand_semantic_compiler.md).

The all-input CNF-to-NAND milestone now implements that exact pure function
with one fixed parser/carrier/controller graph. Every bitstring halts within a
polynomial in its encoded length. Valid CNF words emit the exact strict NAND
bytes; malformed words reject with empty output. The compiled machine supplies
the corresponding `PolynomialTimeFunction` and literal `RawRefinement`.
Lean packages the direct `PolynomialReduction CNFSAT EncodedNANDSAT` and its
explicit composition with the strict locked-NAND polynomial reduction. This
closes the general compiler/reduction edge rather than extending another
finite formula prefix. It does not decide CNF-SAT, connect the concrete target
to the abstract report-level threshold assumption, complete ZeroSlack/PCCMin,
or prove P = NP. See
[`lean_concrete_cnf_to_nand_polynomial_reduction.md`](./lean_concrete_cnf_to_nand_polynomial_reduction.md).

`PNP.Main.locked_nand_threshold` now closes the report-facing concrete
locked-NAND construction boundary. Its exact kernel type is
`PNP.Concrete.ReducesTo PNP.Concrete.CNFSAT
PNP.Concrete.LockedNAND.EncodedLockedNANDThreshold`. The witness is the
composed finite parser/compiler/emitter pipeline, so correctness, runtime,
output-size bounds, malformed-input behavior, and recursive raw refinement
all apply uniformly to every bitstring. The theorem's compiled closure uses
only `propext` and `Quot.sound`; it does not depend on the legacy abstract
string-handle axiom. This is still a many-one reduction, not a polynomial
decider for the target, a concrete CNFSAT NP-hardness result, a residual-band
or ZeroSlack/PCCMin theorem, or the root theorem. See
[`lean_concrete_locked_nand_threshold_publication.md`](./lean_concrete_locked_nand_threshold_publication.md).

The historical hostile review named `DirectWireOutputLowerBound`, `MacroDistinct`,
`TraceEquivalence`, `ZeroOutputConvention`, and `FinalLockSeparation`. The general output lower
bound and model-level free-zero append convention were discharged in preceding layers.
`TraceEquivalence` and complete candidate assembly are now formalized for the typed semantic
carrier, global `MacroDistinct` is discharged by the exact baseline output conditions, and the
whole-carrier `ZeroOutputConvention` consequence is discharged in the unsatisfiable branch.
`FinalLockSeparation` and its satisfiable semantic consequences are now
discharged. The strict encoding and pure semantic transformation are also
formalized. The literal source parser now has all-input exact correctness,
byte-preserving-or-empty output, compiled cubic non-timeout, polynomial
machine/function witnesses, and its leaf raw refinement. The literal target
emitter now has exact all-input target bytes, polynomial runtime and output
bounds, compiled non-timeout, polynomial machine/function witnesses, strict
parser composition, and recursive raw refinement. That composition is now
packaged as the concrete
`EncodedNANDSAT`-to-`EncodedLockedNANDThreshold` `PolynomialReduction`.
The report-facing concrete all-bitstring reduction is now published as
`PNP.Main.locked_nand_threshold`; the legacy abstract string-handle bridge
remains quarantined and is not a premise of that theorem. See
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

The next reconstructed edge is universal rather than another fixed route.
`ResidualGainChain` checks every adjacent strict equivalent gain in any finite
disclosed chain and proves
`residualSlack(endpoint) + chain.length ≤ residualSlack(start)`. The endpoint
remains semantically equivalent and has the same exhaustive reference
minimum. Specializing the existing locked-candidate slack-at-most-four theorem
therefore bounds every accepted locked-family chain by four steps. This is the
iteration-count sentence in legacy report §16 combined with the family bound
in §17. It does not supply the missing gain generator, route completeness,
ZeroSlack contradiction, exact minimizer, or polynomial checker/PCCMin
runtime. See
[`lean_residual_gain_chain.md`](./lean_residual_gain_chain.md).

`ResidualGainStopping` now reconstructs the corresponding semantic stopping
criterion from report §16 over the whole finite implementation space. Positive
residual slack is equivalent to existence of some strict equivalent gain, and
zero slack and semantic minimality are each equivalent to global absence of
one. A verified chain endpoint with a separately proved global no-gain premise
therefore has zero slack and yields an exact minimum result equivalent to the
start. The witness for positive slack is the exhaustive reference-minimum
implementation. Consequently, this theorem does not make the stopping test
polynomial, generate a route, or turn a failed finite scan into global absence.
The report's ZeroSlack certificate, route completeness, exact PCCMin loop, and
runtime obligations remain open. See
[`lean_residual_gain_stopping.md`](./lean_residual_gain_stopping.md).

`ResidualTerminalFullBridge` now reconstructs the direct-wire full-mode part
of the terminal whole-carrier bridge in legacy report §8. Terminalization
preserves the exact implementation, gate count, and semantics at every input
and output coordinate. An independent attained-and-universal minimum
specification is proved equal to the exhaustive reference minimum, which is
the direct-wire terminal `RW-MuBridge`. A cheaper complete whole-span
realization exists exactly when residual slack is positive and every such
realization gives strict residual descent; zero slack is equivalent to its
absence. The quotient carrier and mode firewall, proper supports,
SaturatePositive, BCEL/BN2–BN6, selector completeness, ZeroSlack/PCCMin, and
polynomial runtime remain open. See
[`lean_residual_terminal_full_bridge.md`](./lean_residual_terminal_full_bridge.md).

`ResidualTerminalProjectionMinimum` now reconstructs the finite reference
minimum behind legacy report §5.1, Projection Monotonicity. For every finite
direct-wire implementation, computed terminal-profile observer, and explicit
forgetful projection, Lean exhaustively searches every implementation size
through the current gate count. The resulting full-profile and
quotient-profile minima are attained and satisfy universal lower bounds. The
quotient minimum cannot exceed the full minimum, and their exact difference is
the projection defect. That defect is zero exactly when an attained quotient
minimum carries the mode firewall's checked full lift; a positive defect rules
out such a lift. This is an exhaustive finite reference construction, not a
polynomial minimizer. Proper or governed supports, `SaturatePositive`, Package
E, BCEL/BN2–BN6, route completeness, ZeroSlack/PCCMin, polynomial runtime, and
the root theorem remain open. See
[`lean_residual_terminal_projection_minimum.md`](./lean_residual_terminal_projection_minimum.md).

`ResidualTerminalProjectionTransfer` now reconstructs the signed arithmetic
identity from legacy report §5.2. For every finite family of meet, left, right,
and join implementations sharing one computed terminal-profile observer and
one projection, Lean relates the four full-profile minima, quotient-profile
minima, and projection defects exactly. In the constant-cut case, zero defect
at meet and both sides plus join defect `D` gives projection excess exactly
`D`, hence positive excess for positive `D`. This does not construct or certify
the proper-support/saturated square needed by the manuscript's later
contradiction. `SaturatePositive`, Package E, BCEL/BN2–BN6, route completeness,
ZeroSlack/PCCMin, polynomial runtime, and the root theorem remain open. See
[`lean_residual_terminal_projection_transfer.md`](./lean_residual_terminal_projection_transfer.md).

`ResidualTerminalSaturation` now reconstructs the general “Saturation closure”
operator from legacy report §3, “Saturated support calculus and square
closure.”  For every finite universe of gate, boundary, interface, and computed
profile records, an explicit Boolean relation tags required dependencies with
the manuscript's ten closure mechanisms.  The generated reflexive transitive
closure contains its seed, is dependency-closed, is least among closed
supersets, is monotone and idempotent, and has exactly the closed supports as
fixed points.  The relation is still explicit data rather than an extraction
from an arbitrary circuit.  Proper-support construction, support completion,
square legitimacy, projection-compatible squares, `SaturatePositive`, Package
E, BCEL/BN2–BN6, route completeness, ZeroSlack/PCCMin, polynomial runtime, and
the root theorem remain open.  See
[`lean_residual_terminal_saturation.md`](./lean_residual_terminal_saturation.md).

`ResidualTerminalExecutableSaturation` and
`ResidualTerminalPhysicalSupportCompletion` now reconstruct the next bounded
parts of the physical support construction from legacy report §§2–3. For every
finite primitive-record universe, explicit terminal dependency system, and
finite seed, a deterministic finite work list computes exactly the prior
inductive saturation. For every selected set of gates, the actual direct-wire
program then computes the canonical physical support triple `(U, ∂U, ιU)`:
every input or external gate wire crossing into `U` is in `∂U`, and every gate
wire crossing out or named as a program output is in `ιU`. Lean proves both
directions of these membership specifications, so no crossing wire is omitted
and no unrelated wire is added; constants and wires internal to `U` remain
internal. The dependency system is still explicit data rather than the
manuscript's extracted profile frontier. Proper positive support, full support
completion, square legitimacy, the required projection square,
`SaturatePositive`, Package E, BCEL/BN2–BN6, route completeness,
ZeroSlack/PCCMin, polynomial runtime, and the root theorem remain open. See
[`lean_residual_terminal_physical_support_completion.md`](./lean_residual_terminal_physical_support_completion.md).

`ResidualTerminalSupportExtraction` now reconstructs the adjacent extraction
edge from legacy report §2.2. For every finite direct-wire candidate and every
finite, possibly noncontiguous terminal record list, it builds an actual
direct-wire candidate over the computed incoming boundary and ordered outgoing
interface. Selected predecessors are reindexed internally, unselected
predecessors and primary inputs become exact boundary inputs, and constants
remain local. Lean proves equality with an independent open-support evaluator
for every boundary valuation, and proves recovery of original interface gate
values when the boundary is induced by a whole-circuit execution. The result
also composes with executable terminal saturation. It does not yet derive the
profile frontier, construct a proper positive support, prove square legitimacy
or the required projection square, establish `SaturatePositive`, or close any
later global blocker. See
[`lean_residual_terminal_support_extraction.md`](./lean_residual_terminal_support_extraction.md).

`ResidualTerminalProperSupport` now reconstructs the next finite
proper-positive search edge from legacy report §§2.2, 3, and 10. For every
finite direct-wire candidate and explicit terminal dependency system, it
enumerates every canonical primitive-record seed, performs executable
saturation and extraction, and compares the extracted gate count with the
exhaustive exact minimum for the same open function. Every returned support is
nonempty, strictly smaller than the ambient gate carrier, closed, physically
compatible, semantically exact, and equipped with an equivalent strictly
smaller minimum replacement. The exact negative theorem proves that `none`
means no governed canonical seed is both proper and positive. This is a finite
reference computation rather than a polynomial algorithm. It does not derive
the full manuscript profile frontier, prove governed completion or square
legitimacy, construct the required projection square, or establish
`SaturatePositive`, `BCELReady`, ZeroSlack, PCCMin, or the root theorem. See
[`lean_residual_terminal_proper_support.md`](./lean_residual_terminal_proper_support.md).

`ResidualTerminalSupportSquareClosure` now reconstructs the algebraic and
physical part of the named “Saturated support square closure” theorem in
legacy report §3. For every finite direct-wire candidate, explicit terminal
dependency system, and pair of finite terminal seeds, it computes saturated
left and right corners, their canonical intersection meet, and their
saturated-union join. Lean proves closure of every corner, the exact
greatest-lower-bound and least-upper-bound laws, invariance under seed
reordering and duplication, computed physical compatibility, and exact open
semantics with induced whole-circuit recovery. The dependency system remains
explicit caller data. This does not establish the frontier pushout, projection
compatibility, side-tight minima, BN2 square legitimacy, `SaturatePositive`,
`BCELReady`, ZeroSlack, PCCMin, polynomial runtime, or the root theorem. See
[`lean_residual_terminal_support_square_closure.md`](./lean_residual_terminal_support_square_closure.md).

`ResidualTerminalGovernedSupportCompletion` now reconstructs the next bounded
completed-support edge from legacy report §§2 and 3. For every finite
direct-wire candidate, explicit terminal dependency system, finite seed list,
and saturated support-square corner, it retains the exact closed records and
computes the physical boundary, ordered interface, and selected profile
coordinates in all ten terminal profile roles. Lean proves exact membership,
duplicate freedom, pairwise role disjointness, complete selected-record
coverage, dependency closure, and physical compatibility. The dependency
system remains explicit caller data. This does not establish the frontier
pushout, projection-compatible square, side-tight minima, BN2 square
legitimacy, `SaturatePositive`, `BCELReady`, ZeroSlack, PCCMin, polynomial
runtime, or the root theorem. See
[`lean_residual_terminal_governed_support_completion.md`](./lean_residual_terminal_governed_support_completion.md).

`ResidualTerminalFrontierPushout` now reconstructs the legacy report §3
equation `Front_{A∨B} = Front_A star_{Front_{A∧B}} Front_B` for every
finite direct-wire candidate, explicit terminal dependency system, and
computed saturated support square. The construction reads only the two side
completions. Lean proves exact join-boundary, join-interface, and
role-preserving join-profile gluing, exact meet-profile overlap, and witnessed
retention or internalization of side physical coordinates. This closes the
frontier-pushout dependency edge, but it does not establish projection
compatibility, side-tight minima, BN2 square legitimacy, `SaturatePositive`,
`BCELReady`, complete obstruction routing, ZeroSlack, PCCMin, polynomial
runtime, or the root theorem. See
[`lean_residual_terminal_frontier_pushout.md`](./lean_residual_terminal_frontier_pushout.md).

`ResidualTerminalProjectionSquare` now reconstructs the next legacy report §3
projection-commutation edge. For every finite direct-wire candidate, explicit
terminal dependency system, computed saturated support square, and forgetful
terminal projection, it preserves every physical boundary and interface,
filters each of the ten profile roles exactly, and proves that projected meet
is side overlap while projected join is the side-only projected pushout. The
pushout construction does not read the join corner. This closes the structural
projection-square dependency edge, but it does not establish side-tight
four-corner minima, BN2 square legitimacy, `SaturatePositive`, `BCELReady`,
complete obstruction routing, ZeroSlack, PCCMin, polynomial runtime, or the
root theorem. See
[`lean_residual_terminal_projection_square.md`](./lean_residual_terminal_projection_square.md).

`ResidualTerminalSideTightMinimum` now reconstructs the arithmetic and
no-overclaim part of legacy report §11.1 `BN2-CoherentOptimum`. Every typed
full or quotient four-corner basis lies componentwise above the exact
exhaustive minima, and its signed incidence value equals the corresponding
delta plus left and right slack minus meet and join slack. A Boolean gate and
`Option` extractor reject any basis with even one loose corner, including
canceling slacks that leave the raw total unchanged. Canonical independently
attained full and quotient minima pass and return the existing deltas. This
does not construct one coherent four-corner basis, prove BN2 square
legitimacy, maximize a finite tight family, or establish `SaturatePositive`,
`BCELReady`, ZeroSlack, PCCMin, polynomial runtime, or the root theorem. See
[`lean_residual_terminal_side_tight_minimum.md`](./lean_residual_terminal_side_tight_minimum.md).

`ResidualTerminalFourCornerCarrier` now reconstructs the common-carrier edge
between legacy report §3 and the §11.1 `BN2-CoherentOptimum` obligation
`fourCornerOptimaCarrierCompatible`. For every finite computed saturated
support square, one carrier derives all four governed completions, exact
extracted endpoints, and projected frontiers from the same square, candidate,
and projection. Lean proves duplicate-free canonical coordinate lists, exact
meet and join profile transport, identity-preserving retained physical
coordinates, witnessed internalization, fail-closed absence, and projection
compatibility. This closes the carrier prerequisite, but it does not transport
four optimum realizers, prove the full optimum-compatibility obligation,
construct a coherent four-corner optimum, prove BN2 square legitimacy, or
establish `SaturatePositive`, `BCELReady`, ZeroSlack, PCCMin, polynomial
runtime, or the root theorem. See
[`lean_residual_terminal_four_corner_carrier.md`](./lean_residual_terminal_four_corner_carrier.md).

`ResidualTerminalFourCornerOptimumCompatibility` now reconstructs the full
§11.1 dependency named `fourCornerOptimaCarrierCompatible`. It embeds every
corner boundary and interface into one reversible common ambient carrier,
fixes outputs absent from a corner to false, and proves that ambientization
and localization preserve semantics, gate counts, equivalence, and the exact
semantic reference minimum. All four canonical full and quotient optima then
use one derived role map, one observer, and one projection, and their eight
localized realizers retain the exact shared-family minimum counts. This closes
optimum carrier compatibility, but it does not prove coherent transport along
the square, `sideTightCompletionExists`, BN2 square legitimacy,
`SaturatePositive`, `BCELReady`, ZeroSlack, PCCMin, polynomial runtime, or the
root theorem. See
[`lean_residual_terminal_four_corner_optimum_compatibility.md`](./lean_residual_terminal_four_corner_optimum_compatibility.md).

`ResidualTerminalFourCornerOptimumCoherence` now reconstructs the next
§11.1 `BN2-CoherentOptimum` dependency over that shared carrier. For every
finite computed terminal support square, observer, projection, and full or
quotient mode, an executable classifier traverses the four directed square
legs in a fixed order. It compares semantics only at outputs retained by both
endpoints, compares mode-appropriate profiles in canonical role and coordinate
order, and checks full-mode obligations first. The result is either a checked
side-tight canonical tuple with exact minimum sizes, incidence values, and
physical square commutation, or the exact sound first semantic, profile,
charge-profile, obligation, or mode-firewall mismatch. Quotient success remains
comparison-only. This closes the finite coherence-or-first-failure interface,
but it does not prove that every square is coherent, connect a mismatch to a
later no-outcome route, prove `sideTightCompletionExists`, establish BN2 square
legitimacy, or establish `SaturatePositive`, `BCELReady`, ZeroSlack, PCCMin,
polynomial runtime, or the root theorem. See
[`lean_residual_terminal_four_corner_optimum_coherence.md`](./lean_residual_terminal_four_corner_optimum_coherence.md).

`ResidualTerminalFourCornerSideTightCompletion` now reconstructs the local
Section 11.1 dependency named `sideTightCompletionExists`. For every finite
computed terminal support square, observer, and selected full or quotient
comparison mode, one exact route query returns either its proof-bearing first
local coherence obstruction or a checked coherent optimum tuple. The tuple
retains the common carrier, exact minimum sizes, numerical side-tightness,
exact incidence values, and physical square commutation. Computed route
silence therefore implies the side-tight completion in that mode, and silence
in both modes supplies both completions without using the separate
quotient-to-full promotion query. This closes the local completion edge, but
it does not establish universal route silence, connect a local obstruction to
the complete global no-outcome system, prove BN2 square legitimacy, derive the
terminal dependency system, maximize the complete tight-basis family, or
establish `SaturatePositive`, `BCELReady`, ZeroSlack, PCCMin, polynomial
runtime, or the root theorem. See
[`lean_residual_terminal_four_corner_side_tight_completion.md`](./lean_residual_terminal_four_corner_side_tight_completion.md).

`ResidualTerminalCandidateSaturation` and
`ResidualTerminalSaturationCostBalance` now reconstruct two further finite
edges of legacy `RW-SaturatePositive`. The production terminal dependency
system is derived from the direct-wire candidate: physical edges come from
actual source/output incidence, while profile edges come from exhaustive
context-sensitive observer influence. No dependency relation or extraction
certificate is accepted from the caller. The deterministic saturation trace
records the first rule, dependent, required record, and exact before/after
support for every event. Its total balance classifier recomputes support,
full-minimum, and quotient-minimum costs and returns either linked aggregate
proofs preserving full slack and positivity or the exact first nontransparent
event with a typed reason. Together with the preceding positivity firewall,
this closes the finite terminal forms of
`transparentSaturationCostBalanced` and
`firstNontransparentStepRecorded`. It does not route a nontransparent event:
`interfaceExposureRoutesToE` and
`originKernelObligationClosureRouted` remain open. Accordingly full
`SaturatePositive`, `BCELReady`, ZeroSlack, PCCMin, polynomial runtime, and the
root theorem remain unproved. See
[`lean_residual_terminal_saturation_cost_balance.md`](./lean_residual_terminal_saturation_cost_balance.md).

`ResidualTerminalInterfaceExposureRouting` now closes the finite local form of
`interfaceExposureRoutesToE`. It recognizes only events whose exact
`interfaceConsumer` edge is recomputed from the candidate-derived dependency
system, then reuses the cost classifier to return either transparency evidence
or a proof-bearing local E-route with the selected coordinate, typed reason,
and nontransparency proof. The trace classifier is tied to the production
classifier's exact first nontransparent event and complete transparent prefix;
an earlier non-interface failure remains in a distinct fail-closed branch.
Outgoing-coordinate completion additionally gives the exact zero-cost retract
and preserves full slack. The local E-route is not a Package E `VerifyDW`
acceptance or a proof of global gain. `originKernelObligationClosureRouted`,
full `SaturatePositive`, `BCELReady`, ZeroSlack, PCCMin, polynomial runtime,
and the root theorem therefore remain open. See
[`lean_residual_terminal_interface_exposure_routing.md`](./lean_residual_terminal_interface_exposure_routing.md).

`ResidualTerminalOriginKernelObligationRouting` and
`ResidualTerminalFiniteSaturatePositive` close the remaining finite local
closure-routing edge and compose all five reconstructed terminal
`RW-SaturatePositive` sub-obligations. Exact origin, kernel, and obligation
events are recognized only when their role, rule kind, orientation, and
candidate-derived dependency edge agree. A recognized event is safe only when
it is cost-transparent, an obligation is discharged after the event, and any
profile coordinate hidden by the projection is unchanged. The deterministic
failure order records a balance failure, open obligation, or forgotten-profile
mismatch. The production classifier preserves the complete safe prefix and
returns the exact first interface route, origin/kernel/obligation route, or
other fail-closed nontransparent event. A proof-bearing composite problem then
adds positive initial full slack to the existing candidate BCEL anchor problem.
Its total classifier preserves full positivity through safe saturation and
enters the existing checked-lift or BCEL firewall, or returns that exact first
route. This is a finite composition, not the manuscript-wide theorem: local
routes are not mapped to the complete global outcome system or Package E, and
RankWF, route completeness, full `SaturatePositive`, `BCELReady`, ZeroSlack,
PCCMin, polynomial runtime, and the root theorem remain open. See
[`lean_residual_terminal_finite_saturate_positive.md`](./lean_residual_terminal_finite_saturate_positive.md).

`ResidualTerminalRankWF` now reconstructs the named residual `RankWF` boundary.
The rank is exactly the manuscript's ten natural coordinates in priority order:
witness type, span type, mode, frontier defect, projection defect, saturation
defect, anchor count, charge size, profile size, and canonical code. Nine
nested `Prod.lex` relations over `Nat.lt_wfRel` provide the strict order and its
kernel-checked well-foundedness. The same relation drives an executable Boolean
comparison with both equivalence directions; every coordinate has an explicit
priority theorem, and proof-bearing descent, accessibility, and induction
surfaces are public. This does not map current finite routes into the complete
global outcome system or prove that any route decreases the rank. Route
completeness, Package E, full `SaturatePositive`, `BCELReady`, ZeroSlack,
PCCMin, polynomial runtime, and the root theorem remain open. See
[`lean_residual_terminal_rank_wf.md`](./lean_residual_terminal_rank_wf.md).

`ResidualTerminalBN3RequestEnvelope` now repairs that inference at the finite
candidate-derived boundary. After the existing computed BCEL anchor-nucleus
classifier succeeds, the nucleus's canonically ordered primitive records form
one duplicate-free request identity list for every proper cut. Exact membership
is executable, monotone, stable under extensional transport, and represented by
a singleton minimal consumer. Filtering that one list gives exact,
duplicate-free active incidence. One canonical selection function then chooses
the existing full or quotient BN2 basis for every proper cut and proves every
choice side-tight and coherent. A total wrapper retains each upstream
proof-bearing failure branch unchanged. See
[`lean_residual_terminal_bn3_request_envelope.md`](./lean_residual_terminal_bn3_request_envelope.md).

The separate `PNPBN3JointRealizabilityGap` witness remains important: arbitrary
per-cut basis existence still cannot imply a stable family. The new theorem
avoids that invalid inference by deriving the identities and bases from one
successful computed nucleus. Its proper-cut scan enumerates all subsets, so it
is exponential reference computation rather than a concrete polynomial
machine. The finite BN4 cancellation kernel below closes only the adjacent
activation and same-key arithmetic edge; the full historical BN4–BN6 chain,
complete decreasing route coverage, selector/realizer closure, global
ZeroSlack, and polynomial PCCMin are still absent. Both global publication
milestones therefore remain unearned. See
[`bn3_joint_realizability_gap.md`](../review/bn3_joint_realizability_gap.md).

`ResidualTerminalBN4ActivationCancellation` consumes a successful finite BN3
envelope and an explicit typed signed-cell ledger. The exact singleton request
code is active precisely on the BN3 request predicate, and code equality is
equivalent to activation-function equality without enumerating cuts. Each
complete key retains its request atom, semantic signature, and transport type.
The executable per-key classifier proves exact integer mass conservation and
returns a canonical balanced, positive, or negative residual whose cells keep
that key, have positive mass, and cannot contain an opposite-sign pair. The
total wrapper preserves all upstream proof-bearing failures and rejects cells
whose atoms are outside the successful envelope. The ledger, signatures, and
transport labels remain explicit inputs, so this is not the full historical
BN4 theorem and provides no PkgC/BN6, global-route, selector, ZeroSlack,
PCCMin, or polynomial-runtime conclusion. See
[`lean_residual_terminal_bn4_activation_cancellation.md`](./lean_residual_terminal_bn4_activation_cancellation.md).

`ResidualTerminalBN5FullShadowLocalization` consumes a successful BN4
cancellation outcome at one complete key together with arbitrary finite
explicit payload and quotient-shadow lists. Every refined full unit carries
the BN4 key plus frontier, charge-owner, obligation, origin-kernel, and
mode-projection coordinates. The total executable classifier validates that
the refinement length is the exact negative residual mass, computes whether
the cut is inactive, and otherwise returns either complete exact-coordinate
multiplicity coverage or a strict Hall deficit. The deficit exposes literal
neighbor and full-subset cardinalities, preserves the complete coordinate,
and is routed to the named local X1 outcome, so no active unmatched unit is
silently discarded. Payloads and the quotient-shadow universe remain explicit
finite inputs, and matching is not connected back to a BN4 contradiction.
This is not the full historical BN5 theorem and does not establish
CritC/Q/E/L/X2-X4, PkgC/BN6, global routes or selectors, polynomial
generation/runtime, ZeroSlack, PCCMin, SAT in P, or P = NP. See
[`lean_residual_terminal_bn5_full_shadow_localization.md`](./lean_residual_terminal_bn5_full_shadow_localization.md).

`ResidualTerminalPkgCSeparatingConsumers` reconstructs the next finite PkgC
edge over an arbitrary explicit minimal-consumer antichain. A canonical nested
scan selects the first disjoint pair that is not singleton-singleton. If no
such pair exists, Lean proves exactly the `DisjointPairsSingletonized` premise
consumed by V54. For a found pair, quotient units are generated from all atoms
of both consumers and mapped into exact BN5 coordinates. The existing
equality-fibre matcher classifies an explicit finite full-restoration universe
into complete coordinate multiplicity coverage or a strict Hall deficit with
a deterministic local Q route. Every edge preserves the entire coordinate,
and the quotient-unit list is proved nonempty. The restoration universe
remains explicit, complete coverage is not connected back to a BN4/BN5
contradiction, and the Hall route is not embedded into the complete global
outcome system. Full PkgC route silence, terminal-candidate derivation, full
BN6/Packet selector-realizer completeness, polynomial runtime, ZeroSlack,
PCCMin, SAT in P, and P = NP remain open. See
[`lean_residual_terminal_pkgc_separating_consumers.md`](./lean_residual_terminal_pkgc_separating_consumers.md).

`ResidualTerminalPkgCTypedRestoration` strengthens that coordinate-only edge
without changing its claim boundary. Given an explicit typed
coordinate-preserving restoration operation, Lean maps every atom of the
canonical first separating pair to an actual full candidate, proves the exact
candidate count and coordinate list at every position, and derives complete
equality-fibre multiplicity coverage. Complete coverage contradicts a strict
Hall deficit for the same graph, so the total classifier returns either V54
singletonization or a proof-bearing typed realization. The operation and its
coordinate-preservation proof remain explicit inputs. The theorem does not
construct the operation from a terminal candidate, prove its full semantic
adequacy, connect complete restoration to BN4 or BN5 contradiction, embed
routes globally, or complete historical PkgC, BN6, Packet, ZeroSlack, PCCMin,
SAT in P, or P = NP. See
[`lean_residual_terminal_pkgc_typed_restoration.md`](./lean_residual_terminal_pkgc_typed_restoration.md).

`ResidualTerminalPkgCSameKeyCancellation` closes the next bounded Section 11.5
edge. For every atom of the canonical first separating pair it mechanically
emits one positive quotient unit cell and one negative restored-full-candidate
unit cell. Equality of the complete BN5 coordinate proves equality of the
nested BN4 key, so Lean proves exact cell count, equal positive and negative
multiplicity at every BN4 key, an empty executable BN4 residual, and zero
signed mass. The total theorem returns either V54 singletonization or this
proof-bearing typed cancellation realization; exact absence of every such
cancellation implies singletonization. The typed restorer remains explicit,
and the generated cells are not yet connected to the terminal candidate's
ambient BN4 ledger. Semantic restorer construction, global route integration
and silence, full PkgC, complete BN6/Packet selectors and realizers,
polynomial runtime, ZeroSlack, PCCMin, SAT in P, and P = NP remain open. See
[`lean_residual_terminal_pkgc_same_key_cancellation.md`](./lean_residual_terminal_pkgc_same_key_cancellation.md).

`ResidualTerminalPkgCAmbientBN4Ledger` closes the next finite linkage without
claiming candidate derivation. An exact `List.Perm` certificate proves the
ambient ledger is precisely the generated balanced cancellation cells plus an
explicit remainder, up to order, so membership, duplicate multiplicity,
length, positive and negative mass, signed mass, and executable residual
contribution all decompose exactly. A successful candidate-derived BN4 kernel
additionally proves each embedded generated cell uses its canonical request
atom. The canonical executable classifier accepts only literal
generated-then-remainder serialization; other orders need a proof certificate.
The ambient ledger, restorer, certificate, and BN4 kernel remain explicit, so
candidate derivation, semantic restoration adequacy, complete global route
integration and silence, full PkgC/BN6/Packet completeness, polynomial runtime,
ZeroSlack, PCCMin, SAT in P, and P = NP remain open. See
[`lean_residual_terminal_pkgc_ambient_bn4_ledger.md`](./lean_residual_terminal_pkgc_ambient_bn4_ledger.md).

`ResidualTerminalPkgCAmbientBN4ResidualReduction` strengthens that exact
embedding at the executable BN4 boundary. Adding the same generated mass to
both signs preserves the residual cell at each key, so Lean lifts the equality
to the complete residual ledger over the ambient canonical key universe and
proves every remainder key occurs there. The canonical classifier constructs
both the embedding and reduction without caller proof bits, and an empty
explicit remainder forces the ambient residual ledger to be empty. The ledger,
restorer, embedding, and remainder remain explicit: candidate derivation,
proof that the remainder is empty or route-producing, restoration semantics,
global route integration and silence, full PkgC/BN6/Packet, polynomial runtime,
ZeroSlack, PCCMin, SAT in P, and P = NP remain open. See
[`lean_residual_terminal_pkgc_ambient_bn4_residual_reduction.md`](./lean_residual_terminal_pkgc_ambient_bn4_residual_reduction.md).

`ResidualTerminalConsumerAntichainNormalForm` reconstructs the manuscript's
unbounded theorem V54 over an arbitrary finite carrier and explicit
minimal-consumer antichain. The generated request is proved monotone and false
on the empty cut, and every listed consumer is proved inclusion-minimal among
active sets. Lean proves that two-sided activation is nonzero on some cut if
and only if the antichain contains a disjoint pair. Under the exact PkgC premise
that every disjoint pair is singleton-singleton, it proves on every cut that
two-sided activation is literally the Boolean cut indicator of the singleton
footprint. This closes the V54 edge from PkgC singletonization to BN6's
hyperedge representation without fixing an anchor cardinality. The antichain
is still explicit: full PkgC construction and route silence, candidate derivation,
the bridge from the V54 footprint into V53 and BN6 payloads, global routes,
selectors, polynomial runtime, ZeroSlack, PCCMin, SAT in P, and P = NP remain
open. See
[`lean_residual_terminal_consumer_antichain_normal_form.md`](./lean_residual_terminal_consumer_antichain_normal_form.md).

`ResidualTerminalConstantCutHypergraphRigidity` reconstructs theorem V53 over
an arbitrary finite duplicate-free carrier and sparse positive hyperedges. An
exact mass partition converts equality of all nonempty proper cut weights into
a singleton-to-pair region identity. Shared pairs have equal weight. With four
or more anchors, two distinct outside pairs force every pair and then every
proper footprint to have weight zero. The named theorem proves all cardinality
branches: full-span weight `D` for q=2; one pair weight `p` with
`w_A + 2p = D` for q=3; and zero proper-footprint weight with full-span weight
`D` for q>=4. This closes V53's abstract classification, but the hypergraph is
still explicit. PkgC construction, candidate derivation, the V54-to-V53 and
V53-to-BN6 bridges, BN6 cells and payloads, global routes, selectors,
polynomial runtime, ZeroSlack, PCCMin, SAT in P, and P = NP remain open. See
[`lean_residual_terminal_constant_cut_hypergraph_rigidity.md`](./lean_residual_terminal_constant_cut_hypergraph_rigidity.md).

`ResidualTerminalBN6HypergraphPacket` now reconstructs the adjacent finite
BN6 bridge over an arbitrary finite already-grouped survivor family. Every
group retains a V54 consumer system, the exact PkgC singletonization premise,
a nonempty positive atom ledger, and payload data. V54 identifies the group's
two-sided activation with crossing of its singleton footprint; the new theorem
sums those pointwise equalities into the exact V53 hypergraph cut weight and
transports a BCEL constant-activation equation into V53's constant-cut
premise. The resulting classification produces a positive pair packet at two
anchors, preserves both conditional packet witnesses in the mixed
three-anchor case, and produces only a positive full-span packet at four or
more anchors. Every positive packet footprint retains an original payload
witness. The grouping certificate, PkgC singletonization, atom ledger, and
constant-cut equation remain explicit inputs. PkgC construction, candidate
derivation and grouping, full historical BN6, Packet selectors and realizers,
global route completeness, polynomial runtime, ZeroSlack, PCCMin, SAT in P,
and P = NP remain open. See
[`lean_residual_terminal_bn6_hypergraph_packet.md`](./lean_residual_terminal_bn6_hypergraph_packet.md).

`ResidualTerminalPacketSelectorSeeds` reconstructs the next bounded Packet
edge over an arbitrary finite exact BN6 conclusion. A raw seed records carrier
containment, a footprint of size at least two, and the original grouped
cell-and-atom payload witness. The exhaustive theorem yields the pair seed,
seeds for every pair footprint when the balanced-triple mass is positive, or
the positive full-span seed in the three-anchor or larger branch. It does not
claim selector-universe membership, faithfulness, compatibility, realizer or
route construction, enumeration, or polynomial bounds. Those obligations,
together with PkgC completion, ZeroSlack, PCCMin, SAT in P, and P = NP, remain
open. See
[`lean_residual_terminal_packet_selector_seeds.md`](./lean_residual_terminal_packet_selector_seeds.md).

`ResidualTerminalPacketSelectorUniverse` reconstructs the next finite Packet
edge over the same arbitrary explicit grouped BN6 family. It defines the exact
duplicate-free grouped-footprint list, proves that list membership is
equivalent to naming an original grouped cell at the same footprint, and
upgrades every raw seed to membership without discarding carrier, size, cell,
or atom evidence. This input-relative payload-selector universe is not the
manuscript's encoded or polynomial selector universe, and payload retention is
not manuscript-level faithfulness or compatibility. Realizer and route
construction, grouped-family derivation, polynomial enumeration and size
bounds, PkgC completion, ZeroSlack, PCCMin, SAT in P, and P = NP remain open.
See
[`lean_residual_terminal_packet_selector_universe.md`](./lean_residual_terminal_packet_selector_universe.md).

`ResidualTerminalPacketSelectorHandles` adds canonical input-relative handles
for that exact universe. A handle is a position in the explicit grouped list;
duplicate-free footprints make decoding injective, and each decoded footprint
retains carrier containment, length at least two, and its original grouped
cell-and-atom payload witness. Every payload selector has exactly one such
handle, and the pair, balanced-triple, and full-span alternatives are preserved.
These list positions are not the manuscript's bit encoding or polynomial
selector universe and do not establish manuscript-level selector faithfulness
or compatibility. Realizer and route construction, grouped-family derivation,
polynomial encoding and enumeration bounds, PkgC completion, ZeroSlack,
PCCMin, SAT in P, and P = NP remain open. See
[`lean_residual_terminal_packet_selector_handles.md`](./lean_residual_terminal_packet_selector_handles.md).

`ResidualTerminalPacketSelectorCodec` turns each of those handles into a
canonical unary bitstring and defines one total decoder. The decoder accepts
only a one-run followed by one final zero, rejects missing delimiters, trailing
bits, and out-of-range indices, and Lean proves exact round trip, injectivity,
canonical successful decoding, exact code length, unique accepted codes, and
retention of the existing payload, carrier, size, cell, and atom evidence in
every Packet branch. The code-length theorem is bounded by the supplied
explicit grouped-family list, not by encoded circuit size. It does not prove
polynomial enumeration or runtime, encode atom or payload data, establish
manuscript-level selector faithfulness or compatibility, construct a realizer
or route, derive the grouped family, complete PkgC, ZeroSlack, or PCCMin, put
SAT in P, or prove P = NP. See
[`lean_residual_terminal_packet_selector_codec.md`](./lean_residual_terminal_packet_selector_codec.md).

`ResidualTerminalPacketSelectorPayloadRealization` adds the next bounded
finite interface. Its total function maps every accepted canonical code to the
exact original grouped cell at that decoded handle, that cell's footprint, and
the canonical first original positive payload atom. It rejects exactly when
the existing decoder rejects, proves exact input re-encoding and source-family
membership for every result, and preserves the pair, balanced-triple, and
full-span Packet alternatives. This is deterministic source-payload
materialization relative to a supplied explicit family, not the manuscript's
gain-or-blocker selector realizer. It does not serialize payload data, construct
a replacement circuit, establish selector faithfulness or compatibility,
return a gain or typed blocker route, derive the family, or prove an encoded-
circuit-size bound or polynomial generation/runtime. PkgC completion,
ZeroSlack, PCCMin, SAT in P, and P = NP remain open. See
[`lean_residual_terminal_packet_selector_payload_realization.md`](./lean_residual_terminal_packet_selector_payload_realization.md).

`ResidualTerminalPacketSelectorGainScan` specializes those source payloads to
direct-wire implementations and checks every original atom in the exact
selected cell with the executable strict-equivalent-gain verifier. The total
decoded scan returns only an original atom carrying a proved
`StrictEquivalentGain` or proof that the selected cell contains no such
candidate; every successful gain strictly decreases residual slack. Decoder
rejection remains exact, and the pair, balanced-triple, and full-span Packet
alternatives are preserved. Candidate implementations and the grouped family
remain explicit inputs. Cell-local no-gain is not `BotHN`, `BotBUD`, a
lower-rank `BotSeed`, global minimality, or ZeroSlack, so this is not the
manuscript's complete gain-or-blocker selector realizer. Candidate
construction, selector faithfulness and compatibility, encoded-size and
polynomial-runtime bounds, complete PkgC and routes, ZeroSlack, PCCMin, SAT in
P, and P = NP remain open. See
[`lean_residual_terminal_packet_selector_gain_scan.md`](./lean_residual_terminal_packet_selector_gain_scan.md).

`ResidualTerminalPacketSelectorUniverseGainScan` closes the next finite
selector-oracle edge by enumerating every canonical input-relative handle in
one supplied explicit grouped family and running the complete source-cell scan
at every handle. Its proof-bearing outcome is either a canonical handle and an
original source atom carrying a genuine `StrictEquivalentGain`, or exact
absence of such a gain behind every selector in that supplied universe. Every
gain retains an accepted canonical code, exact source-cell and footprint
evidence, and strict residual descent; the complete pair, balanced-triple, and
full-span Packet conclusion is retained literally. The family and candidate
implementations remain explicit inputs. Family-wide no-gain is not manuscript
selector silence, `BotHN`, `BotBUD`, a lower-rank `BotSeed`, global minimality,
or ZeroSlack. This does not prove selector faithfulness or compatibility,
construct replacements or typed blockers, connect charge surplus, derive the
family, establish encoded-size or polynomial-runtime bounds, complete PkgC or
global routes, put SAT in P, or prove P = NP. See
[`lean_residual_terminal_packet_selector_universe_gain_scan.md`](./lean_residual_terminal_packet_selector_universe_gain_scan.md).

`ResidualTerminalPacketSelectorGainCoverage` formalizes the exact conditional
bridge beyond that finite scan. An explicit gain-coverage certificate must map
every strict equivalent gain from the current implementation to an original
payload atom in one canonical source cell. Under that premise, exhaustive
family-wide no-gain proves global absence of strict equivalent gains and
constructs a proof-bearing `ZeroSlackResult`; the alternative branch retains
its exact source-atom gain and strict residual descent. Every encoded Packet
alternative is preserved literally. An empty-family positive-slack regression
proves that scan silence alone cannot supply the certificate. This is not
unconditional ZeroSlack: the repository does not construct the explicit
gain-coverage certificate from terminal data, prove selector faithfulness or
compatibility, build replacements or typed blockers, close HB/rank routing, or
establish encoded-size and polynomial-runtime bounds. Global PkgC, ZeroSlack,
PCCMin, SAT in P, and P = NP remain open. See
[`lean_residual_terminal_packet_selector_gain_coverage.md`](./lean_residual_terminal_packet_selector_gain_coverage.md).

`ResidualTerminalPacketChargeSurplus` now reconstructs the generic finite
arithmetic kernel of manuscript Section 14 `R-ChargeSurplus`. For arbitrary
finite support and replacement charge ledgers, exact occurrence permutations
preserve multiplicity while pairing every replacement occurrence with one
support occurrence of equal weight. An unmatched positive support charge then
forces both strict occurrence count and strict total weight. When the totals
are proved to be the two NAND gate counts and semantic equivalence is supplied
independently, Lean derives a genuine `StrictEquivalentGain` and strict
residual descent; neither strictness fact is an input field. A regression
rejects reuse of a duplicate support occurrence and a ledger without an
unmatched occurrence. The ledgers, pairing, exact gate accounting, and
semantics remain explicit inputs: the repository does not construct the
replacement or ledger from Packet/terminal data, produce typed blockers, close
HB/rank routing, or prove polynomial bounds. This is not unconditional
ZeroSlack; global PkgC, ZeroSlack, PCCMin, SAT in P, and P = NP remain open. See
[`lean_residual_terminal_packet_charge_surplus.md`](./lean_residual_terminal_packet_charge_surplus.md).

`ResidualTerminalPacketUnitChargeBlueprintRealizer` now specializes that
kernel to a data-only direct-wire unit-charge blueprint format. The two gate counts
mechanically determine canonical `List.range` occurrence ledgers with unit
weights. A constructive remove-first checker, proved exactly equivalent to
`List.Perm` without `Classical.choice`, validates both occurrence partitions,
a nonempty unmatched remainder, and semantic equivalence. Acceptance then
constructs the charge-surplus realization, a genuine strict equivalent gain,
and strict residual descent. The same validator scans every original blueprint
atom behind every canonical handle in one supplied explicit grouped BN6 family
while retaining the complete Packet alternatives. The blueprints, pairing,
family, and candidates remain inputs; family-local validator silence is not
`BotHN`, `BotBUD`, a lower-rank `BotSeed`, global no-gain, or ZeroSlack. The
repository still does not derive these blueprints from terminal data, prove
selector faithfulness or compatibility, close HB/rank routes, or establish
polynomial generation/runtime. Global PkgC, ZeroSlack, PCCMin, SAT in P, and
P = NP remain open. See
[`lean_residual_terminal_packet_unit_charge_blueprint_realizer.md`](./lean_residual_terminal_packet_unit_charge_blueprint_realizer.md).

The checked Packet typed-realizer contract in
`ResidualTerminalPacketTypedRealizerContract` now reconstructs the data-only
typed-output interface immediately following that blueprint realizer. Over an
arbitrary finite selector list and supplied finite-rank executable tables, the
checker accepts each faithful row only as a valid unit-charge blueprint gain,
an active HN blocker at no greater rank, an active budget blocker at no greater
rank, or a faithful selector at strictly lower rank. Checked evidence is tied
by equality to the exact input row, and the grouped-BN6 specialization covers
every canonical handle through the existing exhaustive handle list. The
selector family, rank assignment, faithfulness predicate, claims, and blocker
tables remain inputs. The finite indices are not the manuscript rank tuple,
and invalid rows are rejected rather than converted into blockers. The
repository still does not construct those inputs from terminal data, prove
selector compatibility, blocker semantics, HB acyclicity, global selector
silence, or polynomial generation/runtime. Global PkgC, ZeroSlack, PCCMin, SAT
in P, and P = NP remain open. See
[`lean_residual_terminal_packet_typed_realizer_contract.md`](./lean_residual_terminal_packet_typed_realizer_contract.md).

`ResidualTerminalHBBlockerGraphAcyclicity` now reconstructs the next checked
blocker-graph acyclicity boundary. Its data-only node sum contains only HN and
budget ranks, and its data-only edges name a blocked node and one dependency.
The graph checker exhaustively verifies that every strict comparison in the
supplied finite rank carrier is preserved by a mapping into the already
formalized ten-coordinate `TerminalResidualRank.LexLT` order, then checks
strict exact-rank descent for every supplied edge. Lean derives accessibility,
well-foundedness by inverse image and subrelation, and absence of every
nonempty directed cycle in the accepted graph. It also upgrades valid
lower-seed bots to exact-rank descent and composes these facts with the
canonical Packet typed-realizer contract. The graph, edge list, rank mapping,
blocker semantics, and dependency completeness remain supplied or open. The
result does not construct the graph from terminal data, prove rank-complete
selector silence or the full `HB.NegativeClosure`, establish polynomial
generation/runtime, or complete ZeroSlack, PCCMin, SAT in P, or P = NP. See
[`lean_residual_terminal_hb_blocker_graph_acyclicity.md`](./lean_residual_terminal_hb_blocker_graph_acyclicity.md).

`ResidualTerminalHBDependencyTableClosure` reconstructs the checked
total-table HB dependency boundary and removes the independent edge-list input
from the prior finite graph. It enumerates every HN and budget node at
every supplied finite rank and assigns each node one total data-only
dependency row. The graph is materialized mechanically from every row, so an
edge occurs exactly when its dependency occurs in the corresponding row. The
checker exhaustively validates the finite-to-exact rank embedding and strict
exact-rank descent for every listed dependency. Lean derives exact row
coverage, accessibility, well-foundedness, generic rank induction, and absence
of every nonempty cycle. Composition with the Packet typed-realizer contract
adds covered rows to HN and budget bots and exact-rank descent to lower seeds.
The dependency table, rank mapping, and local induction premise remain
explicit. Exact representation coverage does not prove blocker semantics or
semantic dependency completeness relative to terminal data, and generic
induction does not silence an active blocker without the missing local
invariant. The result therefore does not establish rank-complete selector
silence, the full `HB.NegativeClosure`, polynomial generation/runtime,
unconditional ZeroSlack, PCCMin, SAT in P, or P = NP. See
[`lean_residual_terminal_hb_dependency_table_closure.md`](./lean_residual_terminal_hb_dependency_table_closure.md).

`ResidualTerminalHBActiveDependencyClosure` now reconstructs the manuscript's
next checked HB active-dependency closure over that total table. Activity for an HN or
budget node is projected directly from the existing typed-realizer
environment. An exhaustive Boolean scan requires every active node to name an
active dependency in its own row, while the preceding table checker requires
every such dependency to descend the exact ten-coordinate rank. Well-founded
induction then proves every supplied HN/BUD activity bit false. Composition
with the checked typed-realizer evidence eliminates HN and budget bot branches,
leaving only a genuine checked gain or a faithful strictly lower-rank seed.
The activity bits, dependency rows, rank map, selector family, faithfulness
predicate, and claims remain explicit inputs. The checker does not derive
blocker semantics or semantic dependency completeness from terminal data, and
gain/lower-seed closure remains open. The result therefore is not
rank-complete selector silence, the full `HB.NegativeClosure`, polynomial
generation/runtime, unconditional ZeroSlack, PCCMin, SAT in P, or P = NP. See
[`lean_residual_terminal_hb_active_dependency_closure.md`](./lean_residual_terminal_hb_active_dependency_closure.md).

`ResidualTerminalHBSelectorSilenceClosure` now reconstructs the conditional
selector-silence rank closure over those accepted supplied tables. Checked HB
closure removes HN/BUD bots. An explicit global semantic gain exclusion
premise removes the genuine-gain branch, so any faithful canonical selector
would require a faithful selector at strictly lower finite rank. Strong
induction proves every canonical handle in the table nonfaithful. A second
contract derives global gain exclusion from the existing explicit
gain-coverage certificate and exact source-cell no-gain evidence. The grouped
family, ranks, faithfulness predicate, realizer claims, blocker sidecars, and
global premise or certificate remain inputs. The result does not establish
selector faithfulness or compatibility, construct those inputs from terminal
data, prove blocker semantics or semantic dependency completeness, or close
unconditional `HB.NegativeClosure`, ZeroSlack, PCCMin, polynomial runtime, SAT
in P, or P = NP. See
[`lean_residual_terminal_hb_selector_silence_closure.md`](./lean_residual_terminal_hb_selector_silence_closure.md).

`ResidualTerminalHBExecutableSelectorSilenceInduction` now reconstructs the
executable selector-silence induction itself. Instead of accepting the prior
global semantic no-gain premise, its checker scans every canonical handle and
requires every recorded realizer claim to be a typed bottom. Checked HB closure
eliminates HN/BUD bottoms, and strong finite-rank induction eliminates faithful
lower seeds. The grouped family, rank and faithfulness functions, claims,
activity functions, dependency rows, and rank map remain explicit data inputs.
The result does not construct them from terminal data, establish selector
faithfulness or compatibility, prove blocker semantics or semantic dependency
completeness, close the full unconditional `HB.NegativeClosure` or ZeroSlack,
or provide polynomial bounds. See
[`lean_residual_terminal_hb_executable_selector_silence_induction.md`](./lean_residual_terminal_hb_executable_selector_silence_induction.md).

`ResidualTerminalPacketSelectorFaithfulnessRouting` now reconstructs the
Packet selector-faithfulness routing edge into that executable HB result. Ten
data-only fields on each canonical positive source payload are checked in a
fixed first-failure order, the complete canonical handle list is scanned, and
the computed result is bound exactly to the supplied HB faithfulness table.
Every positive BN6 Packet conclusion supplies a canonical handle, so route-clear
acceptance makes one handle faithful while accepted executable selector silence
makes every handle nonfaithful. The resulting contradiction is fully
kernel-checked. The grouped family, payload fields, rank tags, route-clear data,
HB table, claims, blocker activity, and dependency rows remain explicit inputs.
Positive slack, `SaturatePositive`, `BCELReady`, terminal-data construction,
complete route silence, unconditional ZeroSlack, and polynomial PCCMin remain
open. See
[`lean_residual_terminal_packet_selector_faithfulness_routing.md`](./lean_residual_terminal_packet_selector_faithfulness_routing.md).

The canonical Packet faithfulness-table construction in
`ResidualTerminalPacketSelectorFaithfulnessTable` now removes the independent
faithfulness-function choice at that boundary. It canonicalizes any supplied
typed-realizer table by replacing its faithfulness function with the canonical
positive source-payload computation while preserving the finite rank map,
realizer claims, and HN/BUD activity functions exactly. Exhaustive
faithfulness binding therefore accepts by construction. A route-clear positive
Packet contradicts accepted executable selector silence without a separate
binding premise. This is uniform over arbitrary finite grouped BN6 families
and rank counts. The payload-field checks, rank assignment, grouped-family
derivation, claims, blocker semantics, activity and dependency rows remain
explicit inputs and are not derived from a terminal candidate. External
selector compatibility, complete route silence, unconditional HB negative
closure, ZeroSlack, and polynomial PCCMin remain open. See
[`lean_residual_terminal_packet_selector_faithfulness_table.md`](./lean_residual_terminal_packet_selector_faithfulness_table.md).

The total Packet selector first-route outcome in
`ResidualTerminalPacketSelectorFirstRouteOutcome` now closes the executable
classification gap at that same supplied-data boundary. For every payload at
an arbitrary finite rank, the first-route classifier returns `none` exactly
when the complete checker accepts, and checker rejection returns one concrete
earliest typed route. The result lifts to every canonical grouped-family
handle. Every positive Packet therefore yields either a computed faithful
handle or a first route; accepted executable selector silence and HB
active-dependency closure for the canonicalized table remove the faithful
case. The resulting named theorem takes neither a route-clear premise nor an
independent binding premise. The payload fields, family, rank assignment,
claims, activity and dependency tables remain explicit inputs, and no theorem
yet proves the external semantics or decreasing global coverage of a reported
route. Terminal-data construction, unconditional HB negative closure,
ZeroSlack, and polynomial PCCMin remain open. See
[`lean_residual_terminal_packet_selector_first_route_outcome.md`](./lean_residual_terminal_packet_selector_first_route_outcome.md).

The exact Packet first-route semantics milestone in
`ResidualTerminalPacketSelectorFirstRouteSemantics` now interprets that route
at the supplied-payload boundary. For all ten constructors and every arbitrary
finite rank, `firstRoute = some route` is equivalent to the exact proposition
that all earlier fields accepted and the named field failed. The exact failure
is unique, and rejection is equivalent to the existence of one such proof.
The result lifts through canonical grouped-family payload selection; the
positive-Packet/HB endpoint now returns both the route equality and its exact
field-failure proposition without route-clear or binding premises. This does
not derive the Boolean fields from terminal data, prove their external
manuscript semantics, or map a failure into a decreasing complete global
outcome. Unconditional HB negative closure, ZeroSlack, and polynomial PCCMin
remain open. See
[`lean_residual_terminal_packet_selector_first_route_semantics.md`](./lean_residual_terminal_packet_selector_first_route_semantics.md).

The rank-reflected Packet descent-route milestone in
`ResidualTerminalPacketDescentRouteReflection` now removes the free Boolean at
the final route. The canonical payload preserves the first nine fields and
computes `strictDescentClear` from the exact ten-coordinate `RankWF`
comparison. Acceptance yields an actual decreasing relation; a final descent
failure yields its negation. The positive-Packet/HB endpoint therefore returns
an earlier exact field route or a proof that the supplied transition is
nondecreasing, without route-clear or descent-binding premises. The first nine
fields, before/after ranks, grouped family, and HB data remain explicit, and
the other nine routes are not yet mapped into the complete global outcome
system. Complete route silence, unconditional HB negative closure, ZeroSlack,
and polynomial PCCMin remain open. See
[`lean_residual_terminal_packet_descent_route_reflection.md`](./lean_residual_terminal_packet_descent_route_reflection.md).

The canonical Packet rank-tag route-reflection milestone in
`ResidualTerminalPacketRankRouteReflection` now removes the second duplicate
field at that boundary. The typed-realizer table already assigns every handle
one authoritative finite rank, so
`withComputedRankDescent expectedRank before after` copies that rank into the
payload and retains the exact residual-rank descent computation. The
classifier cannot return `.rank`; a final `.descent` route still proves actual
nondecrease. The positive-Packet/HB endpoint carries the exact failure proof,
rank-route exclusion, and final nondecrease alternative without route-clear,
rank-binding, or descent-binding premises. The rank map, residual ranks, seven
earlier Boolean fields, `exactRouteClear`, grouped family, and HB data remain
explicit. The eight remaining routes are not yet mapped into the complete
global outcome system. Complete route silence, unconditional HB negative
closure, ZeroSlack, and polynomial PCCMin remain open. See
[`lean_residual_terminal_packet_rank_route_reflection.md`](./lean_residual_terminal_packet_rank_route_reflection.md).

The canonical Packet exact-route reflection milestone in
`ResidualTerminalPacketExactRouteReflection` removes the third duplicate field
at the active source boundary. Each canonical handle already comes with proofs
that its selected cell is in the supplied grouped family, has exactly the
decoded footprint, contains the selected original payload atom, and gives that
atom positive mass. The canonical payload therefore sets the internal
`exactRouteClear` bit by construction, while copying the table-owned handle
rank and computing exact residual descent. The classifier can return neither
`.exactRoute` nor `.rank`; a final `.descent` route still proves actual
nondecrease. The positive-Packet/HB endpoint carries the exact failure proof,
both route exclusions, and the final nondecrease alternative without
route-clear or binding premises. This internal route is not an external exact
minimum. The seven semantic Boolean fields, grouped family, finite rank map,
residual ranks, and HB data remain explicit, and the seven remaining routes are
not yet integrated into the complete global outcome system. Complete route
silence, unconditional HB negative closure, ZeroSlack, and polynomial PCCMin
remain open. See
[`lean_residual_terminal_packet_exact_route_reflection.md`](./lean_residual_terminal_packet_exact_route_reflection.md).

The canonical Packet charge-route reflection milestone in
`ResidualTerminalPacketChargeRouteReflection` removes the fourth
caller-controlled field at the active source boundary. Every canonical handle
selects an original payload atom whose strictly positive mass is part of the
grouped-family structure. The canonical payload therefore sets
`chargeChecked` by construction while retaining the reflected internal source
route, table-owned rank, and exact residual-descent comparison. The classifier
can return none of `.charge`, `.exactRoute`, or `.rank`; a final `.descent`
route still proves actual nondecrease. The positive-Packet/HB endpoint carries
the exact failure proof, all three route exclusions, and the final
nondecrease alternative without route-clear or binding premises. Positive
source mass is not full external charge-surplus, replacement, or budget
semantics. Six Boolean fields, the grouped family, finite rank map, residual
ranks, and HB data remain explicit, and the six remaining routes are not yet
integrated into the complete global outcome system. Complete route silence,
unconditional HB negative closure, ZeroSlack, and polynomial PCCMin remain
open. See
[`lean_residual_terminal_packet_charge_route_reflection.md`](./lean_residual_terminal_packet_charge_route_reflection.md).

The canonical Packet colour-route reflection milestone in
`ResidualTerminalPacketColourRouteReflection` removes the fifth
caller-controlled field at the active source boundary. Every canonical handle
has a grouped footprint proved to lie in the family carrier and to contain at
least two atoms. The canonical payload therefore computes its internal
`colourChecked` bit from selector-relevant footprint size while retaining the
separate carrier-sublist proof, positive charge, reflected internal source
route, table-owned rank, and exact residual-descent comparison. The classifier
can return none of `.colour`, `.charge`, `.exactRoute`, or `.rank`; a final
`.descent` route still proves actual nondecrease. The positive-Packet/HB
endpoint carries the exact failure proof, all four route exclusions, and the
final nondecrease alternative without route-clear or binding premises. This
internal eligibility check is not full external manuscript colour
equivalence. Five Boolean fields, the grouped family, finite rank map, residual
ranks, and HB data remain explicit, and the five remaining routes are not yet
integrated into the complete global outcome system. Complete route silence,
unconditional HB negative closure, ZeroSlack, and polynomial PCCMin remain
open. See
[`lean_residual_terminal_packet_colour_route_reflection.md`](./lean_residual_terminal_packet_colour_route_reflection.md).

The canonical Packet typed-frontier route reflection milestone in
`ResidualTerminalPacketFrontierRouteReflection` removes the sixth
caller-controlled field at the active source boundary. Each selected payload
now carries explicit typed source and selector frontier signatures, and the
canonical projection computes `frontierChecked` by executable equality. An
exact `.frontier` route is therefore equivalent to signature inequality;
equal signatures exclude that route. The classifier continues to exclude
`.colour`, `.charge`, `.exactRoute`, and `.rank`, while a final `.descent`
route still proves actual nondecrease. The positive-Packet/HB endpoint carries
the exact failure proof, all four exclusions, frontier inequality when
applicable, and the descent alternative without route-clear or binding
premises. The signatures themselves are supplied rather than derived from
terminal data or bound to the manuscript BN5 frontier. Obligation, activation,
direction, and budget remain explicit, and the four remaining routes are not
yet integrated into the complete global outcome system. Complete route
silence, unconditional HB negative closure, ZeroSlack, and polynomial PCCMin
remain open. See
[`lean_residual_terminal_packet_frontier_route_reflection.md`](./lean_residual_terminal_packet_frontier_route_reflection.md).

The BN5-bound Packet frontier-and-obligation route reflection milestone in
`ResidualTerminalPacketBN5ObligationRouteReflection` replaces the separate
typed-frontier wrapper with the terminal BN5 coordinate already retained by
the formal reconstruction. The canonical projection compares the exact source
and selector BN5 `frontier` and `obligation` fields. A `.frontier` route is
equivalent to frontier inequality; an `.obligation` route carries prior
frontier equality and exact obligation inequality. Canonical colour, positive
charge, the internal source route, table-owned rank, and exact residual descent
remain computed, so `.colour`, `.charge`, `.exactRoute`, and `.rank` stay
excluded and `.descent` still proves nondecrease. The BN5 coordinates remain
explicit inputs rather than being constructed from terminal data. Activation,
direction, and budget are the three remaining fields and routes. Complete
route silence, unconditional HB negative closure, ZeroSlack, and polynomial
PCCMin remain open. See
[`lean_residual_terminal_packet_bn5_obligation_route_reflection.md`](./lean_residual_terminal_packet_bn5_obligation_route_reflection.md).

The BN4 activation-exact Packet route reflection milestone in
`ResidualTerminalPacketBN4ActivationRouteReflection` computes the next Packet
field from equality of the activation atoms nested inside those same source
and selector BN5 coordinates. The existing BN4 theorem proves that atom
equality is equivalent to equality of the canonical activation predicates on
every cut. An `.activation` route therefore carries prior frontier and
obligation equality plus exact activation-atom inequality. Canonical colour,
positive charge, the internal source route, table-owned rank, and exact
residual descent remain computed, so `.colour`, `.charge`, `.exactRoute`, and
`.rank` stay excluded and `.descent` still proves nondecrease. The coordinates
remain explicit rather than terminal-derived. Direction and budget are the two
remaining fields and routes. Complete route silence, unconditional HB negative
closure, ZeroSlack, and polynomial PCCMin remain open. See
[`lean_residual_terminal_packet_bn4_activation_route_reflection.md`](./lean_residual_terminal_packet_bn4_activation_route_reflection.md).

The typed Packet direction-route reflection milestone in
`ResidualTerminalPacketDirectionRouteReflection` computes the next Packet
field from equality of explicit source and selector values in an arbitrary
direction type. A `.direction` route therefore carries prior frontier,
obligation, and activation equality plus exact typed-direction inequality.
Canonical colour, positive charge, the internal source route, table-owned
rank, and exact residual descent remain computed, so `.colour`, `.charge`,
`.exactRoute`, and `.rank` stay excluded and `.descent` still proves
nondecrease. The direction values remain explicit rather than terminal-derived
and are not a construction of the manuscript's complete `Dir(u)` semantics.
Budget is the sole remaining supplied Boolean field and route. Complete route
silence, unconditional HB negative closure, ZeroSlack, and polynomial PCCMin
remain open. See
[`lean_residual_terminal_packet_direction_route_reflection.md`](./lean_residual_terminal_packet_direction_route_reflection.md).

The typed Packet budget-route reflection milestone in
`ResidualTerminalPacketBudgetRouteReflection` computes the final supplied
Packet Boolean from equality of explicit source and selector values in an
arbitrary budget type. A `.budget` route therefore carries prior frontier,
obligation, activation, and direction equality plus exact typed-budget
inequality. Canonical colour, positive charge, the internal source route,
table-owned rank, and exact residual descent remain computed, so `.colour`,
`.charge`, `.exactRoute`, and `.rank` stay excluded and `.descent` still proves
nondecrease. The budget values remain explicit rather than terminal-derived
and are not a construction of the manuscript's complete `Bud(u)` envelope,
BudgetResolve, or HB budget-activity semantics. Computing every local Packet
field does not prove external route adequacy or global route silence.
Unconditional HB negative closure, ZeroSlack, and polynomial PCCMin remain
open. See
[`lean_residual_terminal_packet_budget_route_reflection.md`](./lean_residual_terminal_packet_budget_route_reflection.md).

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
