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
Report-level abstract threshold-language linkage remains missing. See
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
