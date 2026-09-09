# M230 plan: complete all-input Cook-Levin formula builder

Status: in progress and not earned. The current published mathematical coordinate
remains M229. This work may span several implementation and verification phases;
none of the component phases alone earns the complete-builder checkpoint.

Publication decision: **defer** PNPLabs work during the intermediate components.
They do not yet establish the complete all-input construction or close its fixed
weighted checkpoint. Continue verified submilestone notifications independently.
Reassess publication when the complete construction and packaged polynomial
reduction are earned, or sooner if an existing public claim needs correction.
A warranted publication will batch pending earned results from the latest exact
verified core merge into one source-pinned site audit and release. Until then,
retain the coherent M229 published snapshot and its existing progress values.

## Starting evidence and selection

The verified starting point is core merge
`3676a3f291193221e4ee3537aaf6023fba95ace0`, tree
`c3dec3c8d169780bc507ed247bd9e3aebdedd430`.

M229 derives a physical zero/positive body-remainder split for every post-header
coordinate, with a fixed machine, compiled execution and a source-size polynomial
bound. Its body endpoints remain incomplete. M216 already proves semantic
iteration over the complete schedule and an aggregate staged-work bound, but
does not connect those stages as one actual machine run. Reproving those semantic
facts or adding a fixed coordinate does not discharge the remaining obligation.

The selected load-bearing target is the existing fixed checkpoint
`reductions-complete-cook-levin-builder`: complete all-input polynomial formula
construction and its packaged reduction. The immediate implementation boundary
is deriving clause occupancy and every token request from the actual input and
retained workspace, then preserving that workspace across the full loop.

The current tracker remains 35/100 with uncertainty 20% to 40%, formal artefact
coverage 205/207, and 0/5 global gates closed. Do not edit those values to mark a
plan or component implementation as earned.

## Exact legacy anchor

Use the manuscript pinned by
[`archive/legacy-v0/ARCHIVE.json`](../../archive/legacy-v0/ARCHIVE.json), document
tag `final-pnp-proof-report-docs-hardened-7072f8d-sealed`.

The relevant dependency is the introduction's use of SAT NP-completeness and the
section headed **Final SAT decision**, including **Accepted package implies
P=NP**. Reconstructing that transport in the selected finite-machine complexity
model requires a concrete polynomial reduction from each bounded-certificate
verifier language to CNFSAT. The existing formula semantics establish the answer
equivalence, but not an executable polynomial construction.

Anchor precision: the manuscript's **TraceEquivalence** lemma concerns the NAND
circuit trace and lock slots. It is not itself a Cook-Levin formula-builder
theorem. This plan does not use that lemma as authority for the missing builder.
The historical accepted package and checker remain specification/provenance
evidence, not a premise replacing any Lean theorem.

Preserve the existing canonical formula, token encoding, variable layout and
answer-independent schedule. A different presentation of the same machine
construction must preserve the exact output interface below. Do not change the
mathematical route merely because its implementation is difficult.

## Unbounded abstraction and intended theorem types

For a fixed `PolynomialTimeVerifier language`, construct one finite program
independently of the source input and any accepting certificate. On every input
bitstring it must output exactly the canonical encoded verifier-tableau formula.

Planned interfaces in `PNP.Concrete.CookLevin`:

```lean
def formulaBuilder {language : Language}
    (verifier : PolynomialTimeVerifier language) : PolynomialTimeFunction

theorem formulaBuilder_output {language : Language}
    (verifier : PolynomialTimeVerifier language) (input : BitString) :
    (formulaBuilder verifier).output input =
      (VerifierTableauProblem.mk verifier input).encodedFormula

def polynomialReduction {language : Language}
    (verifier : PolynomialTimeVerifier language) :
    PolynomialReduction language CNFSAT

theorem cook_levin_formula_builder_checked_complete {language : Language}
    (verifier : PolynomialTimeVerifier language) :
    ∀ input, (polynomialReduction verifier).function.output input =
      (VerifierTableauProblem.mk verifier input).encodedFormula
```

These are target interfaces, not declarations that already exist. The
`PolynomialTimeFunction` must contain a closed finite `FunctionProgram` and
proofs of total halting, charged polynomial runtime and polynomial output size.
The existing recursive `FunctionProgram.RawRefinement` compiler must apply to
that complete program. A semantic function, staged correct output, supplied
selector or caller-supplied construction theorem is not an implementation.

The reduction's correctness should reuse
`VerifierTableauProblem.encodedFormula_mem_CNFSAT_iff_language` after proving
the output equality. This preserves the existing CNFSAT language and concrete
complexity model.

## Active preservation-family integration

The next dependency edge is the exact canonical preservation payload at every
source-selected regional coordinate, not a fixed schedule slot. Decode the
existing written radix packet into typed time, head position, other position
and symbol coordinates; prove the unchanged direct slot is padding exactly on
the diagonal and the canonical two-premise implication off it. Derive all three
literal indices, including next time, from those physical fields. The final
constructor must pack the existing lossless payload and select padding by an
actual comparison, not by a supplied constraint or verdict.

Prepare universal regressions for coordinate reconstruction and bounds, exact
literal order/signs, diagonal padding, payload decoding, source-field linkage,
physical execution, and encoded-source polynomial bounds before the corresponding
proof build. Audit every new public theorem's dependency closure. Reuse unchanged
source/radix/expression/argument evidence; run the changed dependency target,
its axiom probe and its focused regressions before broader integration.

Verified components now establish the all-coordinate reconstruction and exact
canonical slot equality, including the diagonal padding case, with typed bounds
and the lossless payload specification in
[`CookLevinBuilderPreservationCoordinates.lean`](../../lean/PNP/Concrete/CookLevinBuilderPreservationCoordinates.lean).
[`CookLevinBuilderPreservationLiteralSources.lean`](../../lean/PNP/Concrete/CookLevinBuilderPreservationLiteralSources.lean)
binds all three canonical literal plans to the written source/radix fields and
physically computes next time before executing the conclusion-literal kernel.
That chained machine has exact work/raw execution, preserved workspace, the
canonical final index, control-safety proofs and source-size polynomial
register-span/runtime bounds. The payload specification itself is not claimed
as a physical payload constructor.

The prepared component regressions passed: 27 canonical-coordinate checks and
39 source/literal checks, with all 40 public theorem closures restricted to
`propext` and `Quot.sound` (or no axioms). No project axiom or
`Classical.choice` occurs. Failed proof-script attempts did not change theorem
statements, the machine, or the prepared regression expectations. The successful
unchanged component evidence is reused by source hash; full root, inventory and
release evidence remains due at complete M230 integration.

The physical implication branch is now verified in
[`CookLevinBuilderPreservationImplicationPayload.lean`](../../lean/PNP/Concrete/CookLevinBuilderPreservationImplicationPayload.lean).
It runs the conclusion machine first, then the current-head and current-symbol
kernels, with retained-register counts derived from expression node counts.
A fixed eight-field packer copies the computed roots in canonical payload order
without recomputing them. The end-to-end work/raw theorem preserves arbitrary
workspace and accounts for the exact exterior cells consumed. Its payload
decodes to the canonical implication, and to the direct slot off the diagonal;
the prepared regression expressly rejects treating that candidate as padding.
Full retained-frame span and raw execution time have encoded-source polynomial
bounds, and all control-safety contracts are checked.

All 39 prepared implication-payload regressions passed. All 24 public theorem
closures use only `propext` and `Quot.sound`, with no project axiom or
`Classical.choice`. A record-layout syntax correction changed no statement,
machine or test expectation. The component build, axiom audit and regression
run reached terminal success; unchanged predecessor evidence was reused by
source digest. This is component evidence, not the complete-builder checkpoint.

The runtime comparison and scratch-recovery components are now verified.
[`CookLevinBuilderRegisterErase.lean`](../../lean/PNP/Concrete/CookLevinBuilderRegisterErase.lean)
uses three literal transitions per single-register eraser and composes a
structurally fixed count of them. It physically blanks all removed cells,
preserves arbitrary interior and exterior data, and charges every bridge.
[`CookLevinBuilderRegisterEquality.lean`](../../lean/PNP/Concrete/CookLevinBuilderRegisterEquality.lean)
composes the existing residual comparator, a zero test only on the not-less
branch, and four-register erasure. Its exact work/raw execution accepts exactly
equal operands and rejects exactly unequal operands while restoring the original
retained frame. The zero-but-less case is explicitly a rejecting regression;
a zero residual is not treated as an equality verdict on the less-than branch.

All 23 erasure and 27 equality regressions passed. Their 30 public theorem
closures contain no project axiom or `Classical.choice`; they use only
`propext`, `Quot.sound`, or no axioms. The erasure bound is linear in actual
removed register span, and the whole comparison/cleanup runtime has an explicit
polynomial bound in operand magnitude. Reuse this exact component evidence by
digest. These bounds still need composition with the encoded-source field bounds
at the preservation entry; this paragraph does not award full-builder credit.

The complete source-bound preservation payload kernel is now verified in
[`CookLevinBuilderPreservationPayload.lean`](../../lean/PNP/Concrete/CookLevinBuilderPreservationPayload.lean).
Its fixed four-node graph physically copies the two written position fields,
runs the equality/erasure kernel, and executes literal padding on the diagonal
or the canonical implication constructor off it. Neither the program nor its
initial tape accepts a supplied constraint, equality verdict or literal index.
The all-coordinate work/raw theorem charges the pair copy, comparison, selected
branch and every graph bridge. The final payload equals the unchanged direct
preservation slot and decodes exactly, while preserving the source frame and
arbitrary interior data. Its encoded-source polynomial bounds include both the
final register word and the explicitly cleared exterior cells.

All 41 prepared regressions passed, including both unequal cases, zero-but-less,
padding versus absence, canonical decoding and exact tape accounting. All 19
public theorem closures use only `propext` and `Quot.sound`. A dependency
probe isolated an implicit `Classical.propDecidable` helper in a conjunction
bound; splitting that goal into two arithmetic proofs removed it without
changing any theorem statement, machine or regression assertion. Two padding
assertions needed explicit formula-width annotations, not weaker expectations.
The successful source build and axiom phases were reused by immutable source
identity for the final regression-only check.

This completes the preservation payload boundary, not M230. Other canonical
families, family dispatch, clause occupancy/emission, recovery, Finish, the full
loop and the packaged polynomial reduction remain required. No publication row
or fixed weighted checkpoint changes. PNPLabs publication remains deferred.

## Next general shape-family integration

The next load-bearing edge is the complete one-hot row-shape payload family,
using `shapeConstraintSlotDirect` in
[`CookLevinFormulaCursor.lean`](../../lean/PNP/Concrete/CookLevinFormulaCursor.lean)
and the unchanged `rowShapeProgram` in
[`CookLevinTableauCNF.lean`](../../lean/PNP/Concrete/CookLevinTableauCNF.lean).
It inherits the same pinned manuscript and final complexity-transport anchor.
This family exposes the remaining variable-length payload construction, rather
than another fixed schedule position.

For every source-selected shape coordinate, decode the written row quotient and
the radix-`(tapeWidth + 2)` digit. Preserve canonical row order: all
`tapeWidth` symbol-shape constraints first, then the one head-shape constraint
and one state-shape constraint. Materialize the complete `exactlyOne` variable
list from the written source fields. The head list has source-dependent width;
the state list covers every finite state; each symbol list has the canonical
three symbols. The payload must use the existing reversed
`[4, variableCount] ++ variableIndices` format.

The intended source-bound payload contract is:

```lean
theorem BuilderShapePayload.payload_canonical
    {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .shape) :
    BuilderShapePayload.payloadValues problem index remaining =
      BuilderLocalConstraintPayload.values
        (problem.shapeConstraintSlotDirect
          (BuilderConstraintRegionSource.localCoordinate problem index .shape))
```

This target must accompany exact work/raw execution of one finite
`BuilderShapePayload.machine verifier`, no source-input-dependent control
table, exact retained-frame handoffs, and polynomial bounds in encoded source
size for the complete variable list, scratch and execution. A semantic list,
host-generated index array, supplied length/verdict, or a sequence of fixed
widths does not close it. Reuse existing canonical semantics and arithmetic
proofs; implement the genuinely missing general physical list construction.
Prepare variable-order, zero/boundary, decode, source-linkage, tape-preservation,
runtime and axiom regressions before the corresponding builds.

### Physical variable-length range construction

Implement one fixed `BuilderRegisterDescendingRange.machine` taking an actual
written count and exclusive upper index. Its complete output must be the
descending consecutive list of exactly that many indices, followed by no
unaccounted duplicate. Its input invariant is `count ≤ upper`, not a supplied
list, runtime verdict, or control table. The public exact-run theorem must
quantify over every count, upper value, retained frame and interior tape.

Mark the written counter boundary once. Each loop consumes one physical counter
unit, decrements the newest working register, copies that fixed-offset register,
and returns through the same finite control graph. On exhaustion restore the
entire counter and its delimiter, then erase the redundant newest working copy.
Prove exact work/raw execution, canonical descending order, all graph bridges,
preserved retained input, explicit cleared cells, and a polynomial bound for
the entire growing list and runtime. Bind count and upper to the source-derived
shape fields afterwards. Counter-control kernels are dependency components,
not publication rows or completion of this range/list contract.

The fixed control kernels are now verified in
[`CookLevinBuilderRegisterCountdownControl.lean`](../../lean/PNP/Concrete/CookLevinBuilderRegisterCountdownControl.lean).
Eight literal initialization transitions mark the written counter immediately
before the newest working register. The seventeen-transition consumer scans an
arbitrarily long newer register word, marks exactly one remaining counter unit
on its accepting branch, and on exhaustion restores every spent unit and the
original delimiter before rejecting. Both branches return to the same active
end marker and preserve arbitrary interior/exterior tape. A two-transition
decrement physically removes one positive unary unit and leaves its erased cell
explicitly blank; the zero case cannot pass as a successful decrement.

All 35 prepared regressions and all 17 public-theorem axiom audits passed.
The audited closures use only `propext`, `Quot.sound`, or no axioms.
The exact counter traces include zero-length newer words, the last positive
unit and complete restoration. The scan times are linear in the marked counter
and actual growing register-word span. Reserved-identifier, record-layout,
case-pattern and tape-normalization corrections changed no transition table,
execution statement or regression expectation.

The complete descending-range loop is now verified in
[`CookLevinBuilderRegisterDescendingRange.lean`](../../lean/PNP/Concrete/CookLevinBuilderRegisterDescendingRange.lean).
One fixed five-node graph handles every physically written count and exclusive
upper bound with `count ≤ upper`. It emits exactly `count` registers, whose
index-`i` value is `upper - (i + 1)`, restores the original counter, preserves
the retained frame and arbitrary interior data, and erases the redundant working
register even when the count is zero. The exact work/raw theorem charges every
loop back-edge and the final exit.

For a common bound `B` on count, upper value and retained-register span, the
complete raw runtime is at most `180 * (B + 1)^3`; the final register word plus
explicitly cleared exterior cells has span at most `4 * (B + 1)^2`.
The polynomial-syntax theorem composes these bounds with any proved encoded-input
field bound. Actual shape-source linkage remains required; the bound premises
are not asserted to be derived from the source by this generic range kernel.

At that integration, all 35 prepared regressions and 17 public-theorem axiom audits passed.
The closures use only `propext`, `Quot.sound`, or no axioms. A compiled
dependency probe located `Classical.byContradiction` in the impossible
positive-count/zero-value case; explicitly deriving `False` from the numeric
entry invariant removed it without changing the theorem or machine. An overly
broad regression-proof unfold was narrowed while retaining the exact bridge-count
assertion. The final regression-only run reused the unchanged green source build
and axiom evidence by immutable tree and source identity.

### Complete range-payload metadata; next source binding

The full two-pass constructor is now verified in
[`CookLevinBuilderRegisterExactlyOnePayload.lean`](../../lean/PNP/Concrete/CookLevinBuilderRegisterExactlyOnePayload.lean).
One fixed graph reads the original `[count, upper]` registers, constructs the
entire descending range, copies the original count by a second physical counter
pass, and appends the constant tag. It leaves the retained frame followed by
`[count] ++ descending ++ [count, 4]`; the first count is restored scratch,
and the last count/tag belong to the reversed `exactlyOne` payload.

The counter and range kernels now admit a static output delimiter. Their original
ordinary-delimiter machines and complete run contracts remain specializations,
and the retained-marker variant permits another pass without an input-dependent
register offset. The second pass allocates a zero accumulator, consumes one
original counter unit per iteration, increments the accumulator with a fixed
ten-rule machine, then restores the counter and ordinary delimiter. The initial
range still erases its redundant working register. No list, count verdict,
dynamic program size or caller-supplied execution certificate is substituted.

`BuilderRegisterExactlyOnePayload.workRunExact` and `run_compile_exact`
cover every count and upper bound satisfying `count ≤ upper`, arbitrary retained
register frames and interior data, both complete loops and every graph bridge.
They prove the exact remaining exterior:
`(replicate (upper - count + 1) blank).drop (count + 6)`.
The zero-count case writes the complete `[0, 4]` metadata and removes the original
working upper register.

For a common bound `B` on count, upper and retained-register span, complete raw
runtime is at most `360 * (B + 1)^3`; final register-word and explicit exterior
span together are at most `10 * (B + 1)^2`. The polynomial-syntax theorem composes
these bounds with a proved encoded-input field bound. Deriving those fields from
the actual shape source is still required.

All 135 prepared regressions and 67 public-theorem axiom audits passed across the
changed counter/range contracts and the new complete payload constructor.
Closures use only `propext`, `Quot.sound`, or no axioms. Finite-symbol elimination,
empty-list normalization and exact tape-handoff normalization corrections changed
no machine behavior or assertion. A redundant regression tactic was removed after
Lean had already solved the original assertion; the final regression-only run
reused the exact unchanged green source build and axiom audit.

### All-input shape coordinates and physical branch construction

The canonical coordinate linkage is verified in
[`CookLevinBuilderShapeCoordinates.lean`](../../lean/PNP/Concrete/CookLevinBuilderShapeCoordinates.lean).
For every selected shape slot, the source quotient is the time and the remainder
selects a symbol row, the head row or the state row. The uniform finite-index
identity proves that the descending range is exactly the reversed canonical
variable list, including empty lists. Actual dimensions derive the range bound;
no variable list, count correctness certificate or supplied upper bound is
an execution premise.

All 33 prepared regression contracts and 25 public-theorem axiom audits passed.
Their closures use only `propext`, `Quot.sound`, or no axioms. Input-size
notation, layout-projection and list-association corrections changed no theorem
statement or test expectation. The dependency's already verified complete
counter/range payload evidence was reused without rerunning its regressions.

The physical branch construction is now verified in
[`CookLevinBuilderShapeBranchPayload.lean`](../../lean/PNP/Concrete/CookLevinBuilderShapeBranchPayload.lean).
It uses each fixed arithmetic expression's postorder output: the final addition of a base and a one-register count leaf
already writes `[count, upper]` consecutively. The expression is compiled directly
against the actual source/radix register frame, then composed with the complete
range payload machine. This avoids an extra environment pack or copying routine.
The source dimensions and row coordinates are read at fixed source addresses;
the verifier and retained-frame register count determine the program, not the
input length or values.

The branch contracts were prepared before the first check. They require exact
source-field execution, the complete payload run and raw-machine refinement,
source-coordinate/base/count/upper identities, canonical decoding, retained
frame and exterior accounting, total encoded-source polynomial bounds and
deterministic control. The branch regression keeps the classification premise
explicit and rejects using the symbol-branch premise for a head coordinate.
All 28 branch regression contracts and 22 public-theorem axiom audits passed;
every branch theorem closure uses only `propext` and `Quot.sound`.
Chain-state normalization, explicit constructor elimination and a corrected
existing control-lemma name changed no program or theorem statement. The
unchanged coordinate build, 33 regressions and 25 axiom audits were reused.

The exact branch run includes source-field preparation, the graph bridge and
the entire payload constructor. It preserves the original source/radix frame,
retained registers and arbitrary interior data. Its polynomial bound includes
all source arithmetic, scratch, payload registers, raw steps and the explicitly
cleared exterior; no prepared count or supplied field-size bound substitutes
for the source calculation.

Those branch-specific contracts require the correct classification premise.
They were not themselves a complete source-to-payload dispatcher. The physical
selector below now derives that classification by actual machine outcomes while
preserving the same source frame.

### Exact exterior handoff through the complete shape branches

The handoff obligation is now verified without changing finite-machine control
or exact step counts. The range, complete metadata constructor and three
source-bound shape branches all accept arbitrary exterior data. Their original
empty-exterior contracts remain specializations with unchanged theorem types.

For an initial exterior `outside`, the range's final exterior is exactly
`replicate (upper - count + 1) blank ++ outside.drop (values upper count).sum`.
The second metadata pass then drops `count + 6` cells. This records both
newly cleared cells and allocation from the pre-existing exterior; it does not
identify a finite blank list with an empty list. The shape branch additionally
charges the exact register-word span written by its source-field expression
before applying the complete payload handoff.

The generic output-span bounds become `4 * (B + 1)^2 + outside.length`
for the range and `10 * (B + 1)^2 + outside.length` for the complete payload.
The source-bound branch composes its existing encoded-input polynomial with
a bound on the incoming exterior. The runtime polynomials are unchanged.
These bounds account for the cleanup left by a preceding comparison without
adding a supplied execution or branch-selection certificate.

The affected chain passed 183 regression contracts: 62 range, 50 complete
payload, 33 source-coordinate and 38 source-bound branch contracts. All 110
public-theorem axiom audits passed, with closures limited to `propext`,
`Quot.sound`, or no axioms. Two first-pass regression failures were confined
to record layout and an ambiguous blank-symbol type. Their successful source
build and axiom phases were preserved separately; the whole failed runs were
not recorded as green. After notation-only corrections, exact-source guards
allowed the remaining regression checks to reuse those successful phases.
The old regression expectations, finite programs and exact step functions
were checked unchanged.

### Complete physical shape-family payload

The full family is now verified in
[`CookLevinBuilderShapePayload.lean`](../../lean/PNP/Concrete/CookLevinBuilderShapePayload.lean).
One fixed nine-node graph, determined only by the verifier, copies the actual
row and tape-width registers. The residual comparison selects symbol on its
less-than endpoint; its non-less endpoint performs a zero test to distinguish
head from state. Each path erases all four comparison scratch registers and
passes the exact cleared exterior into its complete source-bound branch.

`selectedKind_canonical` binds those outcomes to the canonical source row.
`workRunExact` and `run_compile_exact` cover the entire physical selection and
payload run. `canonical_workRunExact` requires only the actual selected-region
premise, not a caller-supplied branch, count, payload or classification verdict.
The result contains the canonical complete reversed exactly-one payload, and
its decoder theorem preserves the original slot interface. The original
source/radix frame and arbitrary interior data remain intact.

The exact step count reuses the comparison/zero/erase cost already proved for
the equality dispatcher, then adds actual pair preparation, selected payload
work and their two graph bridges. No second comparison or width-plus-one
expression is needed. The total encoded-input polynomial bounds include all
of this work, the retained/scratch registers, complete payload and explicit
exterior. Taking the sum of the three fixed branch bounds gives one bound
independent of the runtime branch.

All 47 prepared regression contracts and 21 public-theorem axiom audits passed.
Every public closure uses only `propext` and `Quot.sound`. Explicit endpoint,
residual-coordinate, machine-alias and tape-projection normalization resolved
the initial build errors without changing the finite program, theorem types
or prepared test assertions. Only the failed new target was rebuilt; the
unchanged dependency evidence was reused.

### Next dependency: complete control-family payload

The next high-value reuse target is the complete control-transition family,
not one fixed rule, state or schedule position. Its canonical source is
`VerifierTableauProblem.controlConstraintSlotDirect` and the three
`controlConstraints` conclusions: next state, moved head and written symbol.
The existing radix packet has radices `[3, 3, stateBound, tapeWidth]`;
its digits select conclusion kind, read symbol, current state and position,
and its final quotient is the transition step.

Bind every valid coordinate to that exact canonical slot, then derive all
premise and conclusion literal indices from the actual source fields and the
fixed verifier's transition function. Compile any required finite rule lookup
from the verifier; do not supply the action, moved position, literal, payload
or correctness certificate at runtime. Reuse the existing source-field,
literal-expression, complete implication-payload and finite-graph machinery
where their interfaces match. Prove exact tape execution, cleanup, canonical
decode and complete encoded-input polynomial bounds together.

The intended family endpoint has the same shape as the verified preservation
and shape endpoints: `canonical_workRunExact problem index remaining inside
hRegion`, with `hRegion` selecting `.control` and no supplied transition
verdict. Prepare all-coordinate, all-three-conclusion, symbol/state lookup,
head-movement boundary, exact payload order, execution and polynomial-bound
regressions before compilation. This remains part of the existing M230
manuscript-to-concrete-CNFSAT dependency, not a new scored milestone.

The initial, control and accepting payload families, canonical clause emission,
full physical successor, main loop and packaged reduction remain open. M230 is not earned; the fixed complete-builder checkpoint
remains open. No publication row or weighted score changes, and PNPLabs
publication remains deferred until the selected major integration is earned.

## Implementation phases

1. **Reuse audit and physical selection.** Locate and reuse existing general
   clause-count, direct-slot, token-decoding, arithmetic, machine-graph and
   schedule lemmas. Derive clause occupancy and all separator, sign, unary
   variable, terminator and padding requests from source-derived data. Cover
   every constraint family and every coordinate. Do not supply a constraint,
   selected clause, route, request, verdict or correctness certificate as an
   additional endpoint input. Any auxiliary object must itself be constructed
   from the fixed verifier and source input with the required size/work bounds.
2. **One physical successor.** Prove actual tape equality from the end of a
   selected iteration to the next iteration's entry. Preserve the input and
   builder prefix; reset scratch state; advance the coordinate; and append
   exactly the selected token or leave output unchanged for padding. Do not
   replace a physical handoff by rebuilding a semantic configuration externally.
3. **Literal complete loop.** Connect the complete header, repeated body step
   and Finish endpoint in one finite program. Prove a loop invariant for an
   arbitrary processed prefix and instantiate the verifier-derived full
   schedule length. Reuse M216's semantic prefix theorem where its premises
   are actually realized by the physical execution.
4. **Polynomial closure and reduction.** Bound the entire construction,
   workspace, encoded output and execution by polynomials in source input size.
   Include selection, scratch recovery and iteration overhead. Establish the
   exact raw output, package the polynomial-time function, and reuse the existing
   semantic answer equivalence to construct the reduction.
5. **Checkpoint review and publication.** Audit the exact endpoint type and all
   public dependency closures. Review the builder checkpoint and any separately
   proved concrete NP-completeness transport checkpoint by ID and evidence.
   Award only discharged checkpoints, with the required score-change rationale.
   Register and publish the milestone only after the complete target passes.

If a general phase fails, keep the milestone in progress and record the exact
remaining obligation. Do not replace it with another fixed-slot result, a
supplied-data theorem, an axiom, `sorry`, `admit`, or a weakened endpoint.

### Component evidence, 2026-09-06

`PNP.Concrete.CookLevinClauseOccupancy` now projects the occupancy of every
canonical clause-schedule coordinate from the source-derived constraint decoder
and the existing exact local clause-count theorem. It does not materialize a
clause merely to determine whether its slot is populated. The general equality
with the canonical schedule includes padded slots and the out-of-range boundary.
An empty clause remains a populated slot, distinct from padding.

The module build, paired regression file
`lean-regression/PNPConcreteCookLevinClauseOccupancy.lean`, and six-public-theorem
axiom probe passed. The probe reported only `propext` and, for the complete
schedule projection, `Quot.sound`; no classical choice or project axioms.
Regressions were prepared with the source before its first build and include
empty clauses, both single-clause constructors, pair-count boundaries, repeated
variables, padding and the general complete-schedule equality.

This is a selector specification component, not its physical implementation or
a polynomial execution theorem. The complete builder remains unearned, and the
publication coordinate, evidence coverage and risk-weighted score are unchanged.

`PNP.Concrete.CookLevinClauseOccupancyDivision` now connects the selector to
quotient/remainder coordinates for every rectangle size and to the existing
fixed divider's actual execution for every canonical clause coordinate. Its
shielded execution preserves arbitrary surrounding tape data, retains the
six-raw-transition simulation, and satisfies a polynomial bound in source input
length for this division stage. It reuses the existing decoder, divider and
shielded-tape proofs rather than constructing another machine.

The changed module, paired division regression and all ten public-declaration
axiom probes passed. Two polynomial evaluation equalities use no axioms; the
other declarations use only `propext` and `Quot.sound`. The regression includes
zero-width/count rectangles, exact row boundaries, the final out-of-range
coordinate, and an exterior containing divider symbols that would contaminate
an unshielded reader. No existing green proof layer was rebuilt unnecessarily.

The next required physical edge is constructing this second divider's input tape
from the retained builder endpoint, including the source-derived clause width.
The remaining constraint/occupancy test must also become physical execution.
The complete selector, successor handoff and complete builder are still open.
No additional publication row or weighted checkpoint is awarded for this phase.

### Physical handoff constraint

The reuse audit identified an important preservation boundary:
`BuilderUnaryPolynomial.finalOutsideLeft` uses `overlayScratch`, which replaces
an initial scratch span. Its preservation theorem covers the input and existing
builder output, not every old scratch cell. Passing the retained coordinate
records as arbitrary scratch would therefore lose required state.

Before composing that evaluator with the classifier, either reserve and retain
the source-derived clause width through the classifier, or physically relocate
the required coordinate records beyond the overwrite span. Prove the actual
tape equations and charge the allocation, relocation and recovery work. Use the
existing mirrored-machine machinery where the builder workspace has reversed
orientation. A host-created padding span, supplied width, externally rebuilt
configuration or semantic record copy does not close this physical handoff.

### Source-derived dimension registers

`PNP.Concrete.CookLevinBuilderDimensionRegisters` now constructs the clause width
before the coordinate records are created. It reuses the existing finite unary
polynomial evaluator with a compound polynomial whose final value is the body
counter and whose final three postorder registers are width, zero, and counter.
The zero product does not erase the width computation: the literal register
layout and the actual machine execution both retain it, with all construction
work charged in the exact source-size polynomial.

The paired regression was prepared before compilation. It distinguishes the
compound register layout from the counter-only polynomial, preserves separators
for empty registers, and pins the general execution, input/output preservation,
and exact time contract. The module build, regression and ten-public-theorem
axiom probe passed; the probe found only `propext` and `Quot.sound`, with one
evaluation equality requiring no axioms.

This closes dimension construction only. The next physical edge must retain and
read these registers through the classifier and second-divider handoff, using
actual tape equalities. No externally supplied dimensions, selector, repeated
loop or packaged reduction is established by this component. The complete
builder, publication coordinate and progress score remain unchanged.

### Raw-input initialization handoff

The next composition joins the complete header directly to dimension
construction. This is necessary before using either as input-derived workspace:
the classifier accepts a prepared entry tape, so its arbitrary-workspace theorem
alone does not construct or connect that entry. Computing dimensions before the
header would also require proving that the header preserves them.

Construct one `WorkMachine` from the fixed verifier, prove its header submachine
is independent of the input bitstring, and compose the existing actual header
and dimension executions with the generic nine-symbol transition bridge. The
intended `initialize_from_raw` endpoint starts at `rawInputWorkTape`, preserves
the complete canonical header, contains the derived width/counter registers,
and includes both phases and the connecting transition in its polynomial bound.
Prepare raw-start, exact-handoff, fixed-machine, register-layout and full-bound
regressions before compilation, together with every public axiom probe. This
does not construct the classifier entry, select a clause or execute the body
loop; those remain subsequent physical obligations of the same full-builder
milestone. Do not award a publication row or checkpoint for initialization.

The implementation at `PNP.Concrete.CookLevinBuilderInitialization` passed its
changed-module build, all eight paired regression cases and all twelve public
axiom probes. The input-independence equality requires no axioms; the other
probes use only `propext` and `Quot.sound`. The final endpoint retains exactly
the canonical unary header and the source-derived dimension layout, with no
caller-supplied intermediate data. The bound includes the six raw transitions
for the phase bridge. Neither existing dependency compilation nor a full suite
was repeated for this component. The next required edge is a physical operation
on these retained registers that produces the classifier entry and preserves
the loop state; arbitrary-workspace preservation alone is not that operation.

### Balanced physical cursor

Use the retained suffix `[width, 0, N]` as `[width, index, remaining]`, initially
with index zero and remaining `N`. For arbitrary index and positive remaining,
one physical separator/unit swap changes `[width, index, remaining + 1]` to
`[width, index + 1, remaining]`. The sum and tape span stay fixed. This avoids
moving the whole workspace or externally reconstructing the next configuration.

The intended fixed machine must scan from the input head to the active scratch
end, locate the index/remaining separator, perform the swap, and return to the
input head. An exhausted counter must return unchanged through a distinct
endpoint. Prove exact execution for arbitrary valid register prefixes, indices,
remaining counts and exterior data, then discharge the prefix conditions from
the initializer's constructed scratch word and charge the complete scan cost.
Prepare regression cases for zero, one and multiple remaining units, nonzero
indices, preserved exterior/input data, malformed scratch and the full generic
endpoint before compilation. This is the loop's coordinate update, not clause
selection or emission; do not skip processing index zero by treating an initial
advance as a completed body iteration. No checkpoint or publication row is earned.

The general cursor table is now checked in
`PNP.Concrete.CookLevin.BuilderBalancedCursor`. Its 18 rules give exact positive
and exhausted runs for arbitrary valid register prefixes, indices, counters and
exterior data. The positive compiled run is charged at six raw steps per work
step; the bound is linear in the complete register span. The accepting and
exhausted endpoints have no outgoing rules, and no duplicate rule queries exist.
This is still a workspace-relative controller: the source-derived initializer
handoff and its encoded-input-size bound remain to be connected. It neither
selects nor emits a clause and is not the complete construction.

Verification: the permanent leaf build, all 14 paired regression examples, and
all 11 public-declaration axiom probes pass. Four declarations are axiom-free,
one uses only `propext`, and six use only `propext` and `Quot.sound`; none uses a
project axiom or `Classical.choice`. The paired fixtures were prepared before the
first compile. The axiom audit caught a tactic-introduced choice dependency in
the conjunction expressing balanced span; constructing its two conjuncts before
arithmetic removed that dependency without changing the statement or weakening
the audit. No broad proof suite or website cycle was run for this component.

### Source-derived cursor handoff and bound

Next derive a canonical register prefix as a slice of the scratch word already
constructed from the input. Prove its exact zero-index/full-counter layout and
valid symbols without a chosen or supplied prefix. Identify the initializer's
actual final tape with that cursor entry and canonical header. Preserve arbitrary
existing output in the generic positive/exhausted cursor runs, so the operation
remains usable after a body-emission step.

For every index and remaining counter whose sum is the source-derived body count,
prove that register span stays equal to the complete constructed scratch span.
Bound the full compiled scan by the fixed polynomial twelve times that span plus
36. Prepare the source module, all 15 paired regression examples, and all 13
public-declaration axiom expectations before the first compilation. Retain the
no-project-axiom/no-classical-choice boundary. This names existing physical cells;
it adds no host oracle, selector or supplied tape. It does not process slot zero,
emit a clause or close the complete loop. Publication and weighted credit remain
deferred under the plan's major-milestone rule.

Implemented in PNP.Concrete.CookLevin.BuilderCursorSource. The prefix is a
computable take of already constructed scratch cells; its exact layout and valid
symbols are derived, not premises supplied to the endpoint. The initializer's
actual final tape equals the zero-index/full-counter cursor tape with the
canonical header. Positive and exhausted runs preserve arbitrary current output
and the logical input. The balance invariant relates every later register span
to the original source-derived scratch span, yielding the stated encoded-input
polynomial bound for the complete compiled scan.

The permanent leaf built on the first attempt with all 15 paired regressions and
all 13 public-declaration axiom probes green. Four closures use only propext and
nine use only propext plus Quot.sound; none uses a project axiom or Classical.choice.
The strict axiom and regression expectations were prepared with the source.
No broad proof or publication suite was repeated. This closes the initializer
register-layout-to-cursor edge, not the classifier operand construction or full
body iteration. Next physically derive the selector/divider operands from these
retained registers, execute every constraint-family/token branch, and compose
selection, output update and cursor advance without skipping coordinate zero.
No milestone row or weighted checkpoint is earned by this component.

### Divider operand preparation review

The first physical classifier divides the post-header token index by
problem.formulaTokensPerClause. The later occupancy division uses
problem.formulaClauseSlotsPerConstraint; these are different operands. The
existing retained width register is the latter, and must not be substituted for
the former. The classifier also requires problem.formulaClauseSlotCount in its
protected sidecar.

The already evaluated bodySlotCountPolynomial is exactly the product of
formulaClauseCountPolynomial and formulaClauseTokenPolynomial, plus one.
Its retained postorder registers therefore include both the first divisor and
the total clause count. Before adding any evaluation, derive their precise
register offsets and reuse those values. Build a literal copier/operand preparer
that preserves the cursor, source input and emitted output, then matches the
exact shielded divider/classifier entry. The existing tape-bridge copy phases
and evaluator register-copy phases are relevant reuse candidates; their supplied
entry layouts alone do not prove this new source-derived preparation. Charge
all traversal and copying, and keep operand construction distinct from execution.

### Preserved-register copy interface

Expose a small facade over the unary evaluator's already proved separator/copy
phases. One finite table depends only on the number of intervening registers;
it appends the selected unary value while restoring that source and preserving
every intervening register, the older word and all inside tape. Allocation
consumes exactly source-value-plus-one exterior cells. The theorem must account
for that changed span rather than falsely promise preservation of overwritten
scratch. Its exact time polynomial and uniform quadratic bound must include
allocation and every outward, return, copy and restore scan.

Prepare the facade, 18 paired regression examples and all 11 public-theorem axiom
probes together. Tests cover zero and nonzero registers, intervening zero-valued
registers, marker-like preserved surroundings, the exact consumed tail, malformed
entry rejection, deterministic literal rules, general endpoint and exact/bounded
time contracts. Reuse the existing copy proof rather than implementing another
arithmetic engine. This remains an internal operand-preparation component: source
register offsets, entry traversal, exact divider layout, cleanup and return to the
cursor are still required. It earns neither a row nor a weighted checkpoint.

The facade is implemented in
PNP.Concrete.CookLevin.BuilderUnaryPolynomial.RegisterCopy. The permanent module
build, all 18 paired regressions and all 11 public-theorem axiom probes passed
at source commit 3ed17a12c7f3d6c67c973dad915bc3b9ebdc2a66. One closure is axiom-free;
the other ten use only propext and Quot.sound. The tests exercise actual table
runs as well as the uniform theorem and polynomial contract. No existing copy
proof, mathematical statement or test contract was weakened. Completed proof
runs were reused when reconciling the disposable evidence wrapper.

Next derive the exact retained register offsets from the initializer's eager
postorder evaluation, traverse from the source cursor to the active end, and
compose the copier with that actual tape. Then construct the divider layout and
restore the cursor after selection. The current facade alone does not derive
operands from raw input, execute a complete body iteration or earn M230. Keep
publication deferred and the current progress ledger unchanged.

### Source-connected operand access

Connect a fixed outward scan to the preserved-register copier, charging the
real transition between them. Derive the token-width and clause-count offsets
from the already materialized eager postorder values; the cursor index is the
penultimate register. The first divisor has nodeCount(widthPolynomial) + 6
newer registers, the clause count has nodeCount(tokenPolynomial) +
nodeCount(widthPolynomial) + 6, and the index has one. These are fixed control
parameters for a verifier, not new values supplied at runtime.

Prove the exact source cursor tape matches each selected register view. Compose
initialization and access as one actual finite machine from raw input, preserving
the canonical header and original register data while appending the selected
value. Include every initialization, traversal, allocation, copy and phase-bridge
step in the source-size polynomial bound. This stops at the new scratch end:
it does not yet construct the shielded divider layout, recover scratch, emit a
body token or complete the loop.

Prepare both source modules, 18 register-access regressions,
25 source-operand regressions and all 32 public-theorem axiom
probes before compilation. Pin the distinct first divisor and clause-count
interfaces, fixed offsets, zero registers, malformed scan rejection, preserved
inner tape, actual table runs, all-input initialization handoff and complete
phase bounds. Retain the no-project-axiom/no-classical-choice audit. This remains
an M230 component with no milestone row or weighted credit; defer publication.

Implemented in
[BuilderRegisterAccess](../../lean/PNP/Concrete/CookLevinBuilderRegisterAccess.lean)
and [BuilderOperandRegisters](../../lean/PNP/Concrete/CookLevinBuilderOperandRegisters.lean).
The permanent leaf build, all 43 paired regressions and all 32 public-theorem
axiom probes passed at source commit 76156ef0bb76777f92e5e20c76b9d3651ce0362c.
Seven closures are axiom-free, one uses only propext, and 24 use only propext
and Quot.sound. No project axiom or classical choice enters these interfaces.

The register views and fixed offsets now agree with the initializer's actual
postorder word. For every fixed verifier and operand kind, one literal machine
starts from raw input, constructs the canonical header and registers, then scans
and copies the selected value. The endpoint remains at the new scratch end.
The complete source-size bound includes initialization, the scan, allocation,
copying and both phase bridges. General access also preserves arbitrary existing
output and admits the cursor balance invariant for later iterations.

Next combine the required copies with adjusted fixed offsets and convert their
actual tape to the shielded divider entry. Reuse the existing scratch-end position
for subsequent copies where possible, rather than needlessly scanning from the
input again. Prove the exact divider layout and later cleanup/return handoff;
do not infer them from a prepared-entry theorem. Constraint-family selection,
emission and the full loop remain open. No row, checkpoint or gate is earned,
and PNPLabs publication stays deferred.

### Source-derived four-register divider assembly

The next source-to-selector edge appends the clause count, an empty boundary
register, the cursor index and the token width, in that order. The empty register
is allocated by a two-step machine; it is not copied from an index assumed to
be zero. After copying the clause count, reuse the scratch-end position. The
index copier crosses three newer registers, and the token-width copier crosses
its original fixed offset plus three. These control parameters depend only on
the verifier, not on input values or caller-supplied operand data.

Implemented in
[BuilderDividerOperands](../../lean/PNP/Concrete/CookLevinBuilderDividerOperands.lean)
with its paired
[regression contracts](../../lean-regression/PNPConcreteCookLevinBuilderDividerOperands.lean).
The permanent module build, all 24 regressions and all 17 public-theorem axiom
probes passed at source commit 2fc44c607033f902fa7327e3894c0fbb13d17055.
Three closures are axiom-free, one uses only propext, and 13 use only propext
and Quot.sound. No project axiom or classical choice enters this component.

For every source problem, fromRaw_workRunExact connects raw input through
canonical-header and register initialization to all four appended registers.
The more general workRunExact also accepts an arbitrary balanced cursor and
existing output. The endpoint preserves the original register word and inside
tape, and drops exactly clauseCount + index + tokenWidth + 4 cells from the
exterior tail. It does not assume that this remaining tail is empty.

The source-size polynomial includes the input-to-end scan, every allocation and
copy, and all physical bridges. If S is the original register span and
Q(x) = 4(x + 1)^2 + 9(x + 1) + 5, assembly costs at most
S + 4 + Q(S) + 5 + 2Q(3S + 3) work steps. Compilation charges six raw transitions
per work step; the raw-input composition also charges initialization and its
bridge. Tests pin zero and nonzero registers, marker-like preserved surroundings,
malformed delimiter entry, the distinct source-derived operands, fixed offsets,
exact endpoints and complete phase bounds. They were prepared with the source.
After a regression-only formatting correction, the unchanged successful module
build was reused rather than repeated.

Next convert this actual word into the mirrored divider entry and its two
protective boundaries. Prove the needed exterior/blank-tail property from
initialization before applying a divider theorem requiring an empty expansion
side. Do not discard explicit tail cells or assume a cleanup/return handoff.
Divider execution, constraint-family selection, body emission, scratch recovery
and the full loop remain open. This is an internal M230 component, not an earned
milestone row or weighted checkpoint. Keep PNPLabs publication deferred.

### Derived divider expansion footprint

The operand assembly's exterior is now derived from initialization rather than
assumed empty. The header and conservative variable-count polynomials have
different expression associations in paired mode, so equality of their root
values would not establish equality of eager scratch footprints. Bound the
actual header footprint by twice the variable-count footprint. The retained
dimension-width subtree contains two complete variable-count evaluations, and
the source-input register footprint also dominates the input framer's leftover
packed cells.

Implemented in
[BuilderDividerFootprint](../../lean/PNP/Concrete/CookLevinBuilderDividerFootprint.lean)
with its paired
[regression contracts](../../lean-regression/PNPConcreteCookLevinBuilderDividerFootprint.lean).
The permanent module build, all 20 regressions and all 12 public-theorem axiom
probes passed at source commit e5842a7726f856fa1df3e9b47636dbf46e46305f.
Every closure uses only propext and Quot.sound; there are no project axioms
or classical choice.

The exact header-exterior length is the maximum of its scratch span plus one
and the old framer-exterior length. The new preparation span covers that maximum.
Consequently preservedTail_eq_nil proves the actual initializer tail is empty,
and operandFinal_left_eq_nil and fromRawFinal_left_eq_nil establish the empty
expansion side at the already verified operand-assembly endpoints. These are
unconditional source-derived theorems, not premises added to the machine
contract or host-side removal of tape cells. No operational program or runtime
bound changed.

The source-to-divider handoff is discharged by the components below. Later
cleanup must still prove its own cursor/tail invariant; the initialization result
does not silently justify dropping blank padding after an arbitrary later run.
Body selection, emission and the full loop/reduction remain open. No milestone
row, weighted checkpoint or global gate is earned; keep publication deferred.

### Literal copied-operand divider layout

Implemented in
[BuilderDividerLayout](../../lean/PNP/Concrete/CookLevinBuilderDividerLayout.lean)
with its paired
[regression contracts](../../lean-regression/PNPConcreteCookLevinBuilderDividerLayout.lean).
An eleven-rule machine scans the appended token width, index and clause count,
rewrites three copied delimiters, and stops at the reflected dividend's first
cell. It leaves two protective boundaries, the clause-count sidecar and the
complete original workspace intact. The generic trace handles zero registers
and arbitrary preserved inside/exterior tape; malformed boundary slots reject.

The permanent leaf build, all 17 regressions and all nine public-theorem axiom
probes passed at source commit 6dbeeb23c146bc96f152cc40b2322853c088a768.
Five closures are axiom-free, one uses only propext and three use only propext
and Quot.sound. The exact work cost is W + I + 2C + 7. When the three copied
values are at most S, this is at most 4S + 7. Compilation charges six raw
transitions per work step. The source and complete expectation/probe set were
prepared together; the first targeted run passed without fixture corrections.

### Source-derived body-coordinate divider execution

Implemented in
[BuilderDividerSourceExecution](../../lean/PNP/Concrete/CookLevinBuilderDividerSourceExecution.lean)
with its paired
[regression contracts](../../lean-regression/PNPConcreteCookLevinBuilderDividerSourceExecution.lean).
The exact operand endpoint, the derived empty expansion tail and the converter
now produce the actual reflected shielded-divider entry. Reuse the existing
literal divider and generic spatial-reflection theorem; do not create another
divider or infer a prepared-entry premise. Positivity of the token width is
derived from the source formula, not supplied by the caller.

The permanent leaf build, all 27 regressions and all 21 public-theorem axiom
probes passed at source commit 0c936a6c8cc7a817c2f91ec54c22e91b67523d3a.
One closure is axiom-free, six use only propext and 14 use only propext and
Quot.sound. No project axiom or classical choice enters either new component.
The import chain for the reused mirror was rebuilt because its dependency had
changed; no unchanged complete core suite or PNPLabs verification was repeated.

The general workRunExact connects the source-derived cursor tape to the actual
quotient I / W and remainder I % W, preserving the count sidecar, original
registers, input and previously emitted output behind two boundaries.
fromRaw_workRunExact additionally runs canonical initialization from every raw
source input and enters body coordinate zero. It does not skip the first body
slot or claim that the later loop has already been connected.

Under the cursor balance invariant, all three operands are bounded by the
source-derived polynomial register span S. The divider costs at most
20(I + W + 1)^2, hence at most 20(2S + 1)^2. In addition to the already verified
operand-assembly raw bound, conversion, division and both bridges cost at most
6(4S + 9 + 20(2S + 1)^2) raw transitions. The raw-input theorem also charges the
complete initialization and its bridge. These are complete phase bounds,
not yet a runtime theorem for the complete formula builder.

Next connect this actual quotient/remainder endpoint to body/Finish
classification and the source-derived clause-occupancy decoder. Continue with
selected body-token construction and emission, scratch recovery including blank
padding, and the full cursor loop before packaging the reduction. Do not
substitute a supplied selected clause, request, prepared tape or cleanup
certificate for any of these physical handoffs. The full-builder checkpoint is
still open: proof estimate 35%, uncertainty 20% to 40%, formal artefact coverage
205/207 and global gates 0/5 remain unchanged. Keep PNPLabs publication deferred
and continue meaningful verified-submilestone notifications.

### Source-derived body/Finish classification

The source-to-classifier edge now reuses the existing post-divider sidecar
copy and unary comparator after the actual source-derived division. A fixed
243-rule tail contains the reflected 180-rule copy bridge, the reflected 54-rule
comparator and one serial transition table. It is composed with the verified
source-to-divider machine; no caller supplies its entry tape or selected route.

Implemented in
[BuilderSourceClassifier](../../lean/PNP/Concrete/CookLevinBuilderSourceClassifier.lean)
with its paired
[regression contracts](../../lean-regression/PNPConcreteCookLevinBuilderSourceClassifier.lean).
The permanent module build, all 31 regressions and all 19 public-theorem axiom
probes passed at source commit 2e316eb7472f1d8bc980c4c5d684869fd1b6cf09.
Three closures are axiom-free, three use only propext, and 13 use only propext
and Quot.sound. No project axiom or classical choice enters this component.

The workRunExact contract holds for every source problem, natural cursor
index/remaining count and existing token output:

~~~lean
workRunExact? (machine problem.verifier) (workSteps problem index remaining)
    (initialConfiguration problem index remaining output) =
  some (finalConfiguration problem index remaining output)
~~~

The endpoint preserves the divider ledger, original registers, input and
output. For every index below bodySlotCount, RouteAgreement identifies the
canonical body clause/token coordinates or the unique Finish route. The reused
comparator's accept state means body; its reject state means Finish only under
that in-range condition. A larger quotient also reaches reject and is not
misreported as Finish. fromRaw_workRunExact includes the complete canonical
initialization at coordinate zero; fromRaw_routeAgreement classifies that actual
first opportunity rather than skipping it.

If S is the source-derived retained register span, the classifier bridge size
is at most 4S + 2 and the quotient is at most S. In addition to the already
verified source-to-divider bound, copying, comparison and both serial bridges
cost at most 6(20(4S + 2)^2 + 6(S + 1)^2 + 2) raw transitions. The raw-input
composition also charges initialization and its bridge. This remains a phase
bound, not the complete-builder runtime.

The source, complete generic execution/state/tape/bound contracts, literal
body/Finish/zero-count runs, out-of-range non-Finish regression and complete
public-theorem probe set were prepared together. The first targeted compile
found two missing explicit operand-specification rewrites in the route proof.
Those equalities were added without changing the machine, intended theorem or
test expectations; the targeted build, regression and axiom phases then passed.
No unchanged earlier component suite, full core build or site audit was repeated.

Next derive the selected clause-occupancy construction from this actual body
endpoint. The first quotient is the clause index; the second divisor is
formulaClauseSlotsPerConstraint, not formulaTokensPerClause. Preserve or copy
the live quotient and obtain the second divisor from the actual retained source
registers. Do not replace this handoff by a caller-prepared divider tape, selected
constraint or semantic occupancy function. Body-token selection/emission,
scratch recovery including explicit blank padding, the complete loop and
packaged reduction remain downstream. The initialization-only empty-tail proof
does not justify discarding later cleared cells. No row, weighted checkpoint
or gate is awarded, and publication stays deferred. Proof estimate 35%,
uncertainty 20% to 40%, formal artefact coverage 205/207 and global gates 0/5
remain unchanged.

### Literal classifier-register restoration (verified component)

[Source](../../lean/PNP/Concrete/CookLevinBuilderClassifierRegisterRestore.lean) and
[paired regressions](../../lean-regression/PNPConcreteCookLevinBuilderClassifierRegisterRestore.lean).

The nineteen-rule literal normalizer is verified at source commit
44d6382f3f53381a29664cb970e47d1c9bf69fcb, tree
6d751948fda0b2932733f037941b2e41870182d3. Its actual machine scans left to the
current scratch end, normalizes count, quotient and consumed-dividend markers,
converts the three temporary boundaries and old sidecar end to register
separators, then returns to the current end.

The generic tape view describes existing cells; it is not a correctness
certificate or a parameter used to generate machine control. The kernel-checked
exact trace produces the ordinary register word
[sidecarCount, 0, remainder + consumed, width, quotientRest + quotientMarked,
countRest + countMarked], preserving arbitrary workspace and outer tail,
including explicit blank padding. All scans and delimiter transitions are
charged: countRest plus twice the sum of the five reconstructed magnitudes,
plus thirteen. Five magnitudes bounded by S give at most 11S + 13 work steps.

The permanent module build, 23 paired regression examples and all nine public
theorem axiom probes passed with a terminal zero result. Six public theorems
are axiom-free and three use only propext and Quot.sound. No project-specific
axiom or Classical.choice occurs in these closures. Tests cover the fixed
control table, exact values, body/equal/greater/zero inputs, malformed markers,
one-step-short rejection, arbitrary workspace/tail preservation, exact generic
runs, compiled runs and the linear bound. The initial proof-only fixes used the
pinned library's constructive replicate-suffix lemma and an explicit start-state
projection; no machine, theorem contract or test expectation was weakened.

### Source-bound register restoration (verified component)

[Source](../../lean/PNP/Concrete/CookLevinBuilderSourceRegisterRestore.lean) and
[paired regressions](../../lean-regression/PNPConcreteCookLevinBuilderSourceRegisterRestore.lean)
are verified at source commit 5278be635b557d57aa64920d6ee95753bcb1103f,
tree 662d29ed68db4cfc76c855d150d60bcea5a72e31.

The normalizer is now bound to the tape actually produced by the source
classifier. A constructive induction proves that every comparator outcome
retains both original magnitudes. Its exact tape view and the existing division
identity restore the original index without a supplied tape, correctness
certificate or selected route.

The resulting ordinary word is the unchanged live source workspace with
retainedValues ++ [clauseCount, 0, index, tokenWidth, quotient, clauseCount].
The exact standalone restoration trace covers every comparison outcome.
The composed body machine starts at the actual source cursor and continues
under the precise guard index / tokenWidth < clauseCount. The non-body
classifier endpoint is separately proved to reject. This does not claim that
a serial accept-only bridge also executes Finish.

The permanent module build, 39 prepared regression examples and all 20 public
theorem axiom probes passed with terminal zero status. One theorem is
axiom-free, seven use propext only and twelve use propext and Quot.sound.
No project-specific axiom or Classical.choice occurs in these closures.
The tests cover comparator magnitudes, actual body/equal/greater/zero endpoint
tapes, source-workspace preservation, exact work and compiled runs, branch
separation, and source-size bounds. Their expectations passed unchanged;
the proof-only fixes supplied a constructive conjunction and an explicit
configuration projection without unfolding the full composed machine.

The restoration bound is at most 11S + 13 work steps, where S is the previously
proved source-register span. The body bound is the existing classifier raw
bound plus 6(11S + 14); it includes the extra serial bridge and six raw
transitions per work step. This is a bound for this component, not a claim
that the complete formula builder or all of PCCMin is implemented.

### Source-derived second division operands (verified component)

[Source](../../lean/PNP/Concrete/CookLevinBuilderClauseDividerOperands.lean) and
[paired regressions](../../lean-regression/PNPConcreteCookLevinBuilderClauseDividerOperands.lean)
are verified at source commit d67e5f20a41483154bbb907a2be63398048f851a,
tree 37da9dbf857930fcf74908ccda38b010a8fa9bce.

The retained clause-count polynomial factors as constraints * (1 + variables^2).
The new selection theorem locates that already-compiled positive right factor,
equal to formulaClauseSlotsPerConstraint, in the original postorder registers.
Its original offset is the token and dimension node counts plus seven. After
the six restored registers, allocated zero and copied quotient, the final
copy offset is those node counts plus fifteen. These are proved projections
of source-defined register positions, not guessed control parameters.

The actual machine preserves the final clauseCount sidecar, allocates zero,
copies the live first quotient across two newer registers, then copies the
source clause width. Its ordinary endpoint is
retainedValues ++ [clauseCount, 0, index, tokenWidth, quotient] ++
[clauseCount, 0, quotient, clauseWidth].
The guarded body composition executes that preparation exactly once from the
actual source cursor. It does not launch from a rejecting Finish endpoint.

The permanent module, all 41 prepared regressions and all 33 public theorem
axiom probes passed with terminal zero status. Five public theorems are
axiom-free, five use propext only and twenty-three use propext and Quot.sound.
No project-specific axiom or Classical.choice occurs. The two proof-only
offset fixes used definitional equalities; all test expectations passed
unchanged. Regression boundaries include wrong-offset rejection, one-step-short
rejection, distinction from tokenWidth, arbitrary workspace preservation,
source-derived values/offsets, compiled body execution and source-size bounds.

For original source-register span S, preparation takes at most
4 + 2Q(7S + 8) work steps, Q(x) = 4(x + 1)^2 + 9(x + 1) + 5.
The new register word fits 8S + 9 cells, excluding the preserved input/output
workspace. Both internal serial bridges, empty-register allocation, every copy
scan, the outer body bridge and six raw transitions per work step are charged.
This is a component bound, not completion of the formula builder or PCCMin.

### Source-bound clause division (verified component)

[Source](../../lean/PNP/Concrete/CookLevinBuilderClauseDividerExecution.lean) and
[paired regressions](../../lean-regression/PNPConcreteCookLevinBuilderClauseDividerExecution.lean)
are verified at source commit f1b7a9e2af750236a80c2ebd71dfbb903906cfc3,
tree 6d58e56c765983e1e44e45b7815d30586a99cd88.

The fixed 119-rule tail composes the existing divider-layout converter and
mirrored raw divider. Its generic exact trace starts at
endTape (older ++ [clauseCount, 0, quotient, clauseWidth]) inside [].
The source handoff identifies this with the actual operand endpoint and derives
positive clauseWidth from its definition. The complete guarded body composition
starts at the source cursor and executes operand preparation exactly once.

The final tape holds constraintIndex = quotient / clauseWidth in quotient marks
and clauseIndex = quotient % clauseWidth in residual units, preserving the older
registers and input/output workspace behind the two scratch boundaries.
The local clause index is strictly below formulaClauseSlotsPerConstraint.
Under the body guard, the constraint index is strictly below
formulaConstraintSlotCount. The two coordinates reconstruct quotient, and
( constraintIndex * clauseWidth + clauseIndex ) * tokenWidth +
index % tokenWidth = index. The preserved sidecar is still clauseCount,
not constraintCount.

The permanent module, all 38 prepared regressions and all 28 public theorem
axiom probes passed on the first run with terminal zero status. Three public
theorems are axiom-free, eight use propext only and seventeen use propext and
Quot.sound. No project-specific axiom or Classical.choice occurs. The unchanged
regression expectations cover exact generic quotient/remainder cells, positive
and zero-dividend cases, zero-divisor and one-step-short rejection, arbitrary
workspace preservation, source handoff, guarded body execution, both coordinate
ranges, reconstruction, fixed control and compiled source-size bounds.

When clauseCount, quotient and clauseWidth fit the established source span S,
the tail takes at most 4S + 8 + 20(2S + 1)^2 work steps.
The source and body bounds include their respective previously verified
preparation, one serial bridge and six raw transitions per work step.
These are component bounds, not a complete formula-builder runtime theorem.

### Next: source-derived general clause selection

Reuse the existing general
[occupancy contract](../../lean/PNP/Concrete/CookLevinClauseOccupancy.lean) and
[division interface](../../lean/PNP/Concrete/CookLevinClauseOccupancyDivision.lean).
The verified coordinates_match_schedule theorem connects
ClauseOccupancy.constraintSlot at the two actual computed coordinates to
(formulaClauseSchedule[quotient]?).map Option.isSome under the body guard,
using constraintSlot_div_mod and formulaSlot_eq_schedule. This is semantic
handoff evidence only; it does not execute the remaining selector.

Close the physical dependency edge from this source-derived endpoint to the
general formulaConstraintSlotDirect decoder and local clause-count comparison,
for every in-range constraint and local clause index. Derive the selected
constraint and occupancy from the original source workspace; do not accept them
or their correctness as supplied data. Keep padded empty opportunities
distinct from out-of-range failure. The finite control must depend only on the
fixed verifier, and its polynomial bound must charge the actual normalization,
decoding, comparison and dispatch traces.

The generic
[coordinate-register handoff](../../lean/PNP/Concrete/CookLevinBuilderDividerCoordinateRegisters.lean)
and its
[paired regressions](../../lean-regression/PNPConcreteCookLevinBuilderDividerCoordinateRegisters.lean)
are verified at source commit 1a70540dc9814d7ddeab2cd6844cc9a6e65d618c,
tree 953cda12e946f94fc344d43b216c380fb532f758.

The fixed 41-rule machine inserts a real separator, preserves consumed cells and
remainder separately, retains the quotient, and restores the ordinary word
[sidecarCount, 0, consumed, remainder, width, quotient]. Its exact trace preserves
arbitrary source workspace and tail.drop 2 after consuming two outer blank cells.
Empty tails supply implicit blanks; explicit padding and arbitrary exterior
beyond the two cells are covered without identifying different tape lists.

The exact cost is 3 * quotient + 4 * width + 4 * remainder + 2 * consumed +
2 * sidecarCount + 19 work steps, at most 15S + 19 when the five magnitudes fit S.
The permanent target, 31 prepared regressions and all 11 public theorem axiom
probes passed with a terminal zero result. Six public theorems are axiom-free,
two use propext only and three use propext and Quot.sound. No project-specific
axiom or Classical.choice occurs. Syntax and induction-normalization fixes
did not change the machine, theorem contracts or regression expectations.

### Source-bound coordinate handoff (verified component)

[Source](../../lean/PNP/Concrete/CookLevinBuilderClauseCoordinateRegisters.lean) and
[paired regressions](../../lean-regression/PNPConcreteCookLevinBuilderClauseCoordinateRegisters.lean)
are verified at source commit 47e160fba8b4a73c5178e116293f77c570aa6e89,
tree 3e70feaa5696979e8c94922a7c8d7eacfcd69730.

The generic handoff is bound to the actual second-divider endpoint. The complete
guarded body trace starts at cursorTape, computes the body divisions once, and
restores the actual constraint/local-clause coordinates. Its endpoint is the
original retained registers followed by
[clauseCount, 0, index, tokenWidth, quotient, clauseCount, 0,
constraintIndex * clauseWidth, clauseIndex, clauseWidth, constraintIndex].
It requires the actual body guard quotient < clauseCount; this does not claim
that a rejecting Finish endpoint executes an accept-only bridge.

All five normalizer magnitudes are derived from the established source span.
The restored register word fits 9S + 11 cells, excluding and preserving the
original source workspace. The complete component raw-time bound is the
previous source body-division bound plus 6(15S + 20), including the serial bridge.
The semantic occupancy equation follows from the existing constraintSlot_div_mod
and formulaSlot_eq_schedule theorems applied to the actual computed coordinates.
It is not execution of formulaConstraintSlotDirect.

The permanent target, all 22 prepared regressions and all 16 public theorem
axiom probes passed on the first run with terminal zero status. One public
theorem is axiom-free, five use propext only and ten use propext and Quot.sound.
No project-specific axiom or Classical.choice occurs. The original expectations
passed unchanged, covering source projections, exact handoffs, guarded work/raw
execution, canonical occupancy meaning, source bounds, the eleven-register
suffix, footprint, runtime and composed finite control. The unchanged generic
handoff regressions and earlier division suites were not rerun.

### Next: general source-derived constraint-region dispatch

Follow the semantic order in the
[complete direct decoder](../../lean/PNP/Concrete/CookLevinFormulaCursor.lean):
shape, initial, control, preservation, accepting. For source-derived time, tape,
state, fuel and certificate bounds, the ordered region lengths are

1. time * (tape + 2);
2. 3 + 2 * ((certificate + 1) * tape);
3. 9 * ((fuel * tape) * states);
4. 3 * ((fuel * tape) * tape);
5. 1.

Do not infer this order from the
[constraint-size polynomial](../../lean/PNP/Concrete/CookLevinFormulaSize.lean).
Its syntax groups shape, control, preservation, the constant 4, then the
certificate/tape term. The constant 4 combines the initial three opportunities
with final acceptance; the whole initial-region length is not an existing
standalone subtree. Derive its ordered source descriptor, register selections
and required arithmetic construction explicitly. Prove that the five lengths
sum to constraintCount, not the different clauseCount sidecar.

Then prove one physical dispatcher theorem for every valid constraint index
across all five regions. Derive its selected region and local coordinate from
the source registers; do not supply a region, constraint or correctness
certificate. Record exact output, workspace/padding, branch and polynomial-cost
contracts with their tests before compilation. Preserve padded empty cases and
both verifier input modes. No additional fixed-position fixture substitutes for
this general dependency edge.

Local constraint decoding and clause-count comparison, literal emission,
Finish and the complete loop remain open. Recover the token remainder from
retained source data with an actual proved construction when emission needs it.
Publish/defer: defer; neither verified handoff alone earns a publication row or
weighted checkpoint, or materially changes the published bottom line.


Prepare the new theorem/type, exact tape, all route-family and padding cases,
negative handoff, axiom and compiled-cost expectations with the source.
Run only the changed target, its paired regressions and public theorem audit.
Reuse the established semantic and division evidence instead of rebuilding it
as a substitute for the missing physical selector.

Clause selection, body emission, Finish integration, later blank-padding
cleanup/loop and the complete reduction remain open. Publish/defer: defer.
These verified components do not materially change the public bottom line or
earn a publication row or weighted checkpoint. Completing the entire all-input
builder and packaged reduction would meet the major-publication threshold;
another local component alone does not. Meaningful submilestone notifications
continue independently.

Proof estimate 35%, uncertainty 20% to 40%, formal artefact coverage 205/207 and
global gates 0/5 remain unchanged.

### Verified ordered region-register access

Source component: `476c491ff17cfea4ce2b26efc9a9b696b5d07b77`.
[The source-derived region register layer](../../lean/PNP/Concrete/CookLevinBuilderConstraintRegionRegisters.lean)
now identifies all four required retained polynomial terms. Its ordered
five-region descriptor agrees with the existing direct decoder for arbitrary
inputs, including both input modes and the nested option distinction between
padding and out-of-range. The lengths sum to constraintCount, not clauseCount.

The physical copy machine reads a selected term from the actual post-division
register word and appends its value. Its offset depends only on verifier syntax,
term kind and a fixed number of additional registers. Original registers,
additional frame data and input/output workspace survive. The exact exterior
tail is dropped only by the physically overwritten value-plus-separator length;
the source endpoint with no additional registers is explicitly connected.

The initial term still needs its literal +3 adjustment and acceptance its literal
1. This is source operand access, not a physical region selector. No supplied
region-correctness certificate or selected constraint replaces the dispatcher.

[All 31 prepared regressions](../../lean-regression/PNPConcreteCookLevinBuilderConstraintRegionRegisters.lean)
passed on their first execution. All 16 public theorem axiom closures contain
only the permitted foundations: two are axiom-free, two use only `propext`,
and twelve use `propext` and `Quot.sound`. Four initial proof-normalization
errors were corrected without changing definitions, statements or prepared
expectations. The permanent target reached its terminal success marker.
Unchanged copier and coordinate suites were not rerun.

The copy cost is bounded by `4 * (B + 1)^2 + 9 * (B + 1) + 5`, where
`B = 9*S + 11 + appended.length + appended.sum` and `S` is the original
source-span polynomial. The exact compiled execution charges six raw
transitions per work step. These are component costs, not a complete-builder
runtime claim.

Next construct the literal adjusted lengths and assemble them for physical
dispatch. An end-focused ordinary register layout can append
`[1, preservation, control, initial, shape, constraintIndex]`; reading inward
then meets the constraint coordinate and the five lengths in schedule order.
Use the proved source-term offsets with each fixed additional-register count.
The original constraint coordinate remains in the preserved source word and
must be physically copied, not supplied. Account for the constant +3, literal
acceptance 1, every chain bridge, extra delimiter, and consumed exterior cell.

Then prove one literal dispatcher over every valid coordinate, including empty
regions and exact boundaries, deriving the selected region and local coordinate
through actual comparisons/subtractions. Reuse the semantic decoder equality;
do not replace missing execution with a semantic wrapper. Source-bit/constraint
decoding, local clause counts, token emission, Finish, explicit blank-padding
invariants and the full builder/reduction remain open.

Prepare source, exact endpoint, negative boundary, compiled-cost and axiom
expectations together before the next targeted check. Full root/inventory and
publication work remain deferred until the intended builder interface is
complete. Publish/defer: defer. No publication row, checkpoint, proof estimate
or coverage changed; meaningful verified progress notifications continue.

### Verified source-bound region operand assembly

Source component: `9a65cab0eaed831d05362760ae0b5e790c119875`.
[The literal operand assembly](../../lean/PNP/Concrete/CookLevinBuilderConstraintRegionAssembly.lean)
now runs all seven stages: acceptance 1, preservation copy, control copy,
initial-tail copy, its three literal increments, shape copy and the original
computed constraint-index copy. The two-transition increment preserves arbitrary
older registers/workspace and consumes exactly one overwritten exterior cell.
Acceptance allocation costs five work steps; three increments cost eight,
including both internal bridges.

The general assembly appends
`[1, preservation, control, 3+initialTail, shape, constraintIndex]`.
Its reverse faces the dispatcher as the coordinate followed by the five lengths
in canonical schedule order. The lengths sum to constraintCount; the appended
frame has six delimiters and sum `constraintCount + constraintIndex`. The
arbitrary exterior tail is preserved after exactly
`constraintCount + constraintIndex + 6` physically overwritten cells. No
semantic host operation discards a tape cell or supplies a region result.

The guarded source-body theorem executes the previously verified coordinate
computation exactly once, then this assembly with its single additional bridge.
It derives the final coordinate's validity from the existing body guard. The
source input/output workspace and all original registers remain present.

The proved final register span is at most `11*S + 17`. Assembly costs at most
`5*Q(10*S + 16) + 19`, where `Q(b) = 4*(b+1)^2 + 9*(b+1) + 5`.
This charges all five copies, literal writes and every internal and assembly
bridge. Raw execution is six transitions per work step. The full body bound
also includes the prior source-coordinate bound and six raw transitions for
its bridge. These are actual component bounds, not complete-builder runtime
or checkpoint credit.

[All 50 prepared regressions](../../lean-regression/PNPConcreteCookLevinBuilderConstraintRegionAssembly.lean)
passed on their first execution, including literal positive runs, short-run and
invalid-start negatives, arbitrary frames/exterior tails, both exact composed
execution interfaces and their source-size bounds. All 30 public theorem axiom
closures use only the permitted foundations: five are axiom-free, two use only
`propext`, and twenty-three use `propext` and `Quot.sound`. The permanent
target reached its terminal success marker. Initial proof-normalization errors
were fixed without changing machines, statements or prepared expectations.

Keep simplification around large composed machines narrow: name exact frame
length equalities and unfold only the current wrapper. Unfolding the full frame
definitions through a composed machine can reach the elaborator's recursion
limit despite low resource use. Do not raise limits or change the machine to
solve a normalization problem. Keep replication orientation explicit:
`List.replicate_succ` prepends and `List.replicate_succ'` appends. Normalize
the empty reverse after choosing the required orientation.

Next implement actual region selection, rather than another operand wrapper.
First inspect the existing arbitrary-coordinate comparator in
[the general header router](../../lean/PNP/Concrete/CookLevinBuilderArbitrarySlotHeaderRouter.lean)
and any already-proved framed variants. It handles arbitrary natural coordinates
and boundaries, including zero, but its viewed endpoint fixes its outer markers;
it must not be assumed to preserve this assembly's workspace without proof.
Its less branch retains the matched local coordinate. Equality advances with
zero remainder. Its greater branch retains a `remainingCoordinate` that needs
one added unit to recover the next-region residual; do not lose that unit.

Prove every marker/frame adapter, actual comparison/subtraction continuation,
selected region/local-coordinate output and polynomial cost. Cover zero-length
regions, exact boundaries, the accepting singleton and out-of-range rejection.
Reuse the established semantic decoder equality; it cannot replace missing
machine execution. Source-bit/constraint decoding, local clause counts, token
emission, Finish, explicit blank-padding invariants and the full loop/reduction
remain open.

Prepare those producer/endpoint/negative/cost/axiom contracts together before
targeted checks. No unchanged region-register or coordinate suite was repeated.
Full root/inventory/publication work remains deferred until the intended builder
interface is complete. Publish/defer: defer. The proof estimate remains 35%,
uncertainty 20% to 40%, formal artefact coverage 205/207 and global gates 0/5.

## Verified physical register-pair comparison

The [pair-comparison module](../../lean/PNP/Concrete/CookLevinBuilderRegionPairComparison.lean)
now executes the existing arbitrary-Nat comparator on two disposable ordinary
unary registers. A five-rule adapter scans the copied boundary and coordinate,
changes their inner delimiter into the protective boundary, and turns back into
the pair. Spatial reflection reuses the existing exterior-shielded comparator
theorem; it does not add another comparison implementation or assume that
unproved framing holds. The composed literal machine has 68 rules.

The input is the actual ordinary register layout
`endTape (older ++ [coordinate, boundary]) workspace []`. Its empty outer tape
is explicit, not an arbitrary-exterior claim. Every older register and every
arbitrary workspace cell remains behind the boundary. Exact execution accepts
if and only if `coordinate < boundary`, and rejects if and only if
`boundary <= coordinate`. Zero operands and equality are covered without extra
premises. The final tape is exactly the mirrored canonical comparison result:
the greater branch retains one additional marked coordinate unit, so its
unmarked remainder is one less than the residual needed for the next region.

The adapter costs `boundary + coordinate + 3` work steps. Composition charges
one bridge and every step of the existing comparator. For both copied operands
at most `B`, the full comparison costs at most
`2*B + 4 + 6*(B+1)*(B+1)` work steps, with exact sixfold raw-machine compilation.
This is a bound for this physical comparison, not for the complete builder.

The [focused regression](../../lean-regression/PNPConcreteCookLevinBuilderRegionPairComparison.lean)
checks 31 universal, literal-tape, zero/equality, greater-residual, malformed,
short-run, framing, control and cost contracts. All 17 public theorem closures
passed: seven are axiom-free, two use only `propext`, and eight use `propext` and
`Quot.sound`. No project-specific axiom or `Classical.choice` occurs. Assertions
were prepared with the source; subsequent corrections changed proof scripts
and record formatting, not the machine, theorem statements or expected results.
The permanent module was built before imported regressions and axiom probes.
Its successful compilation was reused after the regression-format-only edit;
no unchanged assembly or earlier component suite was repeated.

Next, physically copy the computed coordinate and required region length from
the assembled source frame into this pair, then restore the comparison result
and continue through the general five-region dispatcher. Equality must advance
with residual zero; the greater branch must recover the extra marked unit.
Neither a selected region nor a residual-correctness certificate may be supplied
as a premise. Local decoding, occupancy, emission, Finish, explicit blank-padding
invariants and the complete loop/reduction remain open.

Publish/defer: defer. This is a verified component of the unearned M230 builder,
not a new publication row or weighted checkpoint. The proof estimate remains
35%, uncertainty 20% to 40%, formal artefact coverage 205/207 and global gates
0/5. No website, inventory, status or report regeneration is warranted yet.

## Verified source-derived comparison operands

The [operand module](../../lean/PNP/Concrete/CookLevinBuilderRegionComparisonOperands.lean)
now copies the actual computed coordinate and selected boundary from ordinary
registers, then executes the protected comparison. For a fixed newer-register
offset, the input word is
`older ++ [boundary] ++ newer ++ [coordinate]`. Two existing register-copy
machines append `[coordinate, boundary]` without changing that original word
or the arbitrary protected workspace. Their control offsets are fixed, not
programs selected from input data. Copying alone supports arbitrary exterior
tails; the composed comparison explicitly starts with an empty exterior tail.

The source-bound entry starts at the existing source cursor and executes the
complete body assembly once. It proves that the resulting word physically
contains `constraintIndex` and the shape-region length at the required places,
then performs both copies and the comparison. Its exact work-machine and
sixfold compiled raw-machine runs are proved under the existing body guard.
Acceptance is equivalent to the computed index being below the shape-region
length; rejection is equivalent to the opposite weak inequality. Original
registers, source input and accumulated output remain protected.

The cost includes both copy runs, their bridge, the comparison bridge and the
complete existing comparator. If both operands and the encoded newer-register
span are bounded by `B`, the two-copy cost is at most `2*Q(3*B+2)+1`, where
`Q(x) = 4*(x+1)*(x+1)+9*(x+1)+5`. The comparison's established bound is then
charged in full. The source entry derives both operand bounds from the existing
encoded-source-span polynomial and the balanced body cursor; its raw polynomial
also charges the assembly and every bridge. This is not a complete-builder
runtime theorem.

The [focused regression](../../lean-regression/PNPConcreteCookLevinBuilderRegionComparisonOperands.lean)
passed all 37 prepared contracts. All 28 public theorem closures passed:
two are axiom-free, four use only `propext`, and 22 use `propext` and `Quot.sound`.
No project-specific axiom or `Classical.choice` occurs. Initial elaboration
corrections only exposed wrapper equalities and used schematic composition
lemmas; no machine, public statement, regression expectation or resource limit
was changed. The permanent module was rebuilt before the imported checks.
The exact successful source and regression hashes are reused for this
documentation-only integration, without repeating their proof checks.

Next restore the actual comparator tape and continue the general five-region
dispatcher. Equality must yield zero residual; the greater case must recover
its extra marked coordinate unit. Both cases currently share the rejecting
control state, so their tape distinction must be handled by actual rules.
No selected region or residual-correctness certificate may be supplied.
Local decoding, clause occupancy, emission, Finish, blank-padding invariants
and the full loop/reduction remain open.

Publish/defer: defer. M230 and its fixed complete-builder checkpoint remain
unearned. No publication row, score, gate or public bottom-line transition is
claimed. Proof estimate: 35%; uncertainty: 20% to 40%; formal artefact coverage:
205/207; global gates closed: 0/5. No website or generated-report cycle is needed.

## Verified component: physical residual-field restoration

`BuilderRegionResidualRegisters` implements one fixed 42-rule normalizer for
arbitrary physical field lengths: boundary-rest `a`, boundary-marked `b`,
coordinate-rest `c` and coordinate-marked `d`. It inserts a real separator by
shifting the outer prefix into one explicitly blank exterior cell, normalizes
marks to unary units, restores the inner delimiter and rewinds. The actual run
returns `endTape [d, c, a+b] workspace (tail.drop 1)` and preserves the arbitrary
protected workspace without traversing it.

Its finite control toggles for every marked cell. The compiled theorem binds
the descriptive view to every actual mirrored canonical comparator result:
less/equal contain `p+p` marks and halt in the even state; greater contains
`p+(p+1)` marks and halts in the odd state. This derives the greater/equal
distinction from physical transitions, not a supplied verdict or certificate.

The exact charged work is `5*a + 4*b + 4*c + 2*d + 13`, with sixfold raw-machine
compilation. When every field is at most `B`, work is at most `15*B+13` and raw
time at most `90*B+78`. This component bound is not yet a composed source-input
polynomial theorem for the residual handoff or complete builder.

Evidence: the permanent Lake target built successfully; all 35 prepared
regressions and all 14 public-declaration axiom closures passed in one terminal
zero-status run. Five public declarations are axiom-free, two use only
`propext`, and seven use only `propext` and `Quot.sound`. No project-specific
axiom or `Classical.choice` is present. The regressions include universal
work/raw/exterior contracts and literal zero, equal, less, greater with zero or
positive unmarked remainder, arbitrary-field, protected-workspace, missing-blank,
malformed and short/overrun checks.

Initial feedback corrected proof scripts and Lean record layout only: a reserved
local identifier, explicit Boolean negation, scan-definition unfolding, repeated
unit orientation and a constructive list-concatenation induction. All 42 machine
rules, public theorem statements, exact costs and 35 regression assertions were
preserved. All regression assertions passed on their first actual execution.
Unchanged verified dependency checks and broad core/site suites were not repeated.

## Verified component: actual residual copy and branch handoff

`BuilderRegionResidualSelection` materializes one fixed seven-node, 602-rule
graph. Its entry runs the actual disposable-pair comparator. The selected branch
restores the physical fields then copies register offset two. The non-selected
branch restores them, copies offset one, and increments only on the physically
computed odd-parity outcome. Unexpected local failures lead to the dead endpoint.
All node names, programs and successors are independent of input values.

| Node | Program | Accept successor | Reject successor |
| --- | --- | --- | --- |
| Compare | Existing pair comparator | Restore selected | Restore residual |
| Restore selected | Field normalizer | Copy selected | Dead |
| Restore residual | Field normalizer | Copy zero | Copy remainder |
| Copy selected | Register copy, offset two | Selected endpoint | Dead |
| Copy zero | Register copy, offset one | Residual endpoint | Dead |
| Copy remainder | Register copy, offset one | Increment | Dead |
| Increment | Existing literal increment | Residual endpoint | Dead |

For every natural coordinate and boundary, arbitrary original register list and
protected workspace, the exact run starts at
`endTape (older ++ [coordinate, boundary]) workspace []` and returns the
unchanged `older` frame plus four ordinary scratch registers. The last register
equals `if coordinate < boundary then coordinate else coordinate - boundary`;
the recovered boundary register equals the original boundary. The accepting
endpoint is reached exactly when the coordinate lies below the boundary; the
rejecting endpoint exactly when the boundary is at most the coordinate.

All physical scans, copies, increments and graph bridges are charged. Less/equal
traverse three bridges; greater traverses four plus the increment's two steps.
For coordinates and boundaries at most `B`, the proved work bound is

```text
17*B + 23 + 6*(B+1)*(B+1) + 4*(2*B+3)*(2*B+3) + 9*(2*B+3) + 5
```

The compiled raw run has exactly six times the work steps, with a matching
`NatPolynomial` bound. This is an operand-bound theorem, not yet the full
source-encoded-size theorem for preparation, region dispatch and formula emission.
Graph well-formedness, distinct local queries and absence of rules at both local
halting states are proved, not supplied as caller premises. Neither a branch
verdict nor a residual-correctness certificate is supplied to the machine.

The permanent target built, all 38 prepared regressions passed, and all 19 public
theorem axiom closures passed in one terminal zero-status verification. Five
public declarations are axiom-free, two use only `propext`, and twelve use only
`propext` and `Quot.sound`. No project-specific axiom or `Classical.choice`
remains. The regressions cover universal exact work/raw/result/control/exterior
contracts, literal zero/equal/less/greater cases, retained workspace, one-step-short
and overrun boundaries, malformed input, and the polynomial bound.

The machine, public statements and all expected results were unchanged throughout
feedback. Structural length lemmas avoided expanding the entire graph to count
rules. A bounded evaluator-depth setting allowed kernel-checked literal lookup
through its 602 rules. The axiom audit caught an `omega`-generated classical
decidability proof when negating a conjunction: explicitly constructing each
conjunct in the two arithmetic helpers removed the dependency. The final audit
ran before the final regression pass. No broad core or site suite was repeated.

## Verified component: source-derived residual selection

[`BuilderRegionResidualOperands`](../../lean/PNP/Concrete/CookLevinBuilderRegionResidualOperands.lean)
now composes the two actual register-copy operations with the complete residual
selector. For each fixed offset, the input word is
`older ++ [boundary] ++ newer ++ [coordinate]`, where `newer.length = offset`.
The resulting machine has `9*offset + 818` rules, distinct rule queries and no
rules at either halting state. All offsets and program tables are independent of
input values; neither a verdict nor a residual certificate is supplied.

For arbitrary natural operands and protected workspace, the exact run preserves
that complete original frame and appends four ordinary scratch registers.
The last register equals the original coordinate when it is below the boundary,
and its natural subtraction by the boundary otherwise. Acceptance and rejection
are equivalent to those respective inequalities. The returned coordinate never
increases, and the scratch registers' unary length-plus-sum is at most
`4 + 4*B` when both operands are bounded by `B`. This also bounds data that
later region-copy operations must traverse.

The source entry starts at the actual builder cursor, executes
`BuilderConstraintRegionAssembly.bodyMachine` once, and then runs preparation
and residual selection for the shape-region boundary. It reuses the existing
body guard for the exact execution theorem. The balanced cursor supplies the
encoded-source-span bounds; the complete builder loop must still establish
these physical invariants for every source input.

Writing `Q(x) = 4*(x+1)*(x+1)+9*(x+1)+5` and `S(B)` for the preceding
selector's proved work bound, the general work bound is
`2*Q(3*B+2)+2+S(B)`. This charges both copies and all bridges as well as
comparison, restoration, copy and increment. The raw run costs exactly six
times the work steps. The source polynomial additionally charges the complete
assembly and its bridge, without executing the assembly a second time.

The [paired regression](../../lean-regression/PNPConcreteCookLevinBuilderRegionResidualOperands.lean)
passes all 50 contracts. All 31 public-declaration axiom closures pass: four are
axiom-free, six use only `propext`, and 21 use only `propext` and
`Quot.sound`. No project-specific axiom or `Classical.choice` occurs.
Coverage includes general work/raw execution, actual final tape and coordinate,
both outcomes, protected registers/workspace, zero/equal/less/greater runs,
nonzero offsets, wrong offsets, short/overrun and malformed staging, control
separation and source-encoded runtime and scratch bounds.

Initial compilation exposed a namespace qualification error; qualifying the
namespace and reusing the already proved tape projection resolved it without
changing the machine or theorem statements. One negative fixture had assumed
that a total symbol table stopped before taking its explicit malformed-input
transition. Inspection of `separatorSpecs` and `deadAction` showed that the
first step preserves the tape and enters the copier's dead state; the second
step has no rule. The corrected regression asserts both facts. All valid-input
outputs and exact costs remained unchanged. The successful source build and
axiom evidence were byte-bound and reused for that regression-only correction.
The terminal verification result is successful; no broad core or site suite
was repeated.

## Verified component: complete five-region register dispatch (2026-09-07)

[CookLevinBuilderConstraintRegionDispatch.lean](../../lean/PNP/Concrete/CookLevinBuilderConstraintRegionDispatch.lean)
now implements one fixed ten-node, 5,080-rule dispatcher. The input register
frame contains five arbitrary natural lengths and an arbitrary coordinate.
Those data never construct its control table or supply a classification
certificate. Five actual comparisons use the proved fixed offsets zero, five,
ten, fifteen and twenty. Each rejected comparison leaves the original registers
intact and appends the next residual coordinate. Each successful comparison
runs its own literal tag writer, built from delimiter/increment transitions,
and returns both the selected region tag and its local coordinate.

The universal `workRunExact` theorem covers the complete dispatcher, not a
prefix or selected instance. `run_compile_exact` transports it to the compiled
raw machine at six raw transitions per work transition. The proved verdict is
acceptance exactly below the sum of the five lengths and rejection otherwise;
equality therefore proceeds to the following region. A selected local
coordinate is strictly below its own region length. The final tape contains
the original frame followed only by the recorded scratch fields and tag.
Empty regions, including five empty regions, require no added premise.

The runtime argument charges all intermediate scratch scans. If the initial
coordinate and all five lengths are at most `B`, every later newer-register
span is at most `24*B + 20`. The whole run is bounded by
`5 * BuilderRegionResidualOperands.workBound (24*B + 20) + 20`.
Its raw polynomial includes all five selector bridges and the literal tag
writer/bridge. This is a polynomial in an operand bound; deriving that bound
from the actual source input remains part of the source linkage below.

The prepared
[regression module](../../lean-regression/PNPConcreteCookLevinBuilderConstraintRegionDispatch.lean)
passes all 53 examples, including independent expected fuels and output words
for every selected region, exact boundaries, zero-length chains, the all-empty
rejection, arbitrary workspace preservation and malformed-input rejection.
All 36 public theorem closures pass the strict audit: ten are axiom-free, four
use only `propext`, and 22 use `propext` and `Quot.sound`. None uses a
project-specific axiom, `Classical.choice` or a proof placeholder.

Focused verification succeeded at source/regression tree
`08ff19bd1e57c746d20b79ca586d2635761c1172`. Two local proof-normalization
corrections left the control table and intended statements unchanged.
Regression record-layout syntax was corrected without changing expected costs
or tapes. One literal negative lookup over the fixed 5,080-rule table uses a
fixture-local recursion-depth option; source options and resource limits were
not raised. The source build and axiom audit were byte-bound and reused for
the regression-only correction. No broad core or site suite was repeated.

## Verified implementation: source-bound whole-region selection

[CookLevinBuilderConstraintRegionSource.lean](../../lean/PNP/Concrete/CookLevinBuilderConstraintRegionSource.lean)
connects the actual source assembly once to the complete fixed dispatcher.
The canonical frame
`[1, preservation, control, initial, shape, coordinate]` is derived from
the verifier/input and actual cursor, not supplied to the machine by a caller.
This closes the source-to-whole-region-selection dependency within the same
canonical manuscript formula construction.

The universal `workRunExact` starts at
`BuilderCursorSource.cursorTape problem index remaining output` under the
existing body guard `quotient problem index < count problem`. It performs
the complete assembly and dispatcher, including their handoff, for every
verifier tableau problem, cursor index, remaining budget and output prefix.
It accepts no supplied region, frame, decoder result or correctness certificate.
The resulting tape preserves the assembled frame and protected workspace,
appends the physically computed local coordinate and literal region tag, and
has empty outer tape. The actual body guard proves that a region is selected,
that its local coordinate lies within that region, and that execution accepts.

The semantic interpretation of the written pair is exactly
`formulaConstraintSlotDirect`. The theorem preserves both option layers:
an out-of-range `none` is not a padded empty constraint `some none`.
This is a specification theorem, not execution of the local decoder; the
finite machine never evaluates the semantic decoder as a shortcut.

Under the existing cursor-balance invariant, put
`B = (sourceSpan verifier).eval input.length`. The source-derived bounds are:

- Raw steps are bounded by the complete assembly polynomial, plus six raw
  transitions for the handoff, plus the complete dispatcher's polynomial at
  the source span. No region reassembles the source.
- All appended selection scratch registers, including every rejected
  predecessor and the literal tag, occupy at most `20 * B + 25` symbols.
- The entire retained register word occupies at most `31 * B + 42` symbols.
  This does not claim a bound on an arbitrarily supplied output prefix or
  the still-incomplete formula-builder output.

The [regression module](../../lean-regression/PNPConcreteCookLevinBuilderConstraintRegionSource.lean)
was prepared with the source before its first compile. All 34 examples pass:
universal exact work/raw execution, source and tape linkage, actual body-guard
acceptance, source-size bounds, control separation, canonical slot equality,
and the absent-versus-padded distinction. All 27 public theorem closures pass:
four use no axioms, eight use only `propext`, and fifteen use
`propext` with `Quot.sound`; none uses a project-specific axiom,
`Classical.choice` or `sorryAx`.

The first compile exposed only proof-elaboration issues: concrete chain
normalization and a split on the outer option match instead of the numeric
guards. An abstract chain lemma and explicit guard cases fixed those scripts.
The machine, public statements and prepared regression expectations were not
changed. The final permanent target, axiom audit and regressions reached their
terminal zero result. Unchanged dispatcher evidence was reused; no broad core
or website suite was repeated.

## Verified implementation: register-preserving mixed-radix execution

[CookLevinBuilderRegionCoordinateDivision.lean](../../lean/PNP/Concrete/CookLevinBuilderRegionCoordinateDivision.lean)
and
[CookLevinBuilderRegionRadixDecoder.lean](../../lean/PNP/Concrete/CookLevinBuilderRegionRadixDecoder.lean)
provide the shared executable coordinate arithmetic for the canonical
rectangular regions. They implement general data-dependent division, not
another fixed coordinate or supplied quotient/remainder.

The single-split machine starts on
`older ++ [width] ++ newer ++ [coordinate]`.
Only the register offset is fixed in its finite control. It physically
allocates two zero registers, copies the coordinate and width, executes the
existing literal divider, and restores the result to ordinary registers.
Its universal exact work/raw execution theorem covers every coordinate,
positive width and older/newer register frame with the specified offset.
It preserves that entire frame and the protected workspace and appends
`[0, 0, consumed, remainder, width, quotient]`, ending with empty outer tape.
The written quotient/remainder satisfy reconstruction, the strict remainder
bound and the existing canonical rectangle interpretation, including its
out-of-range guard.

The mixed-radix compiler fixes only the split count and initial offset.
All radices remain input data; the physical initial order is
`older ++ radices.reverse ++ newer ++ [coordinate]`.
After each actual split, seven retained fields separate the next radix from
the new quotient, so the recursive finite-control offset advances by seven.
The general execution theorem covers every positive radix list of that
fixed length, preserves the original frame, and appends one six-register
packet per split. Reading the actual packets and final quotient reconstructs
the original coordinate. Semantic readout functions specify the written
data; the machine does not call them to manufacture a result.

All allocations, copies, divider/restoration steps and chain handoffs are
charged in the exact work count and its sixfold raw-machine refinement.
For coordinate, width and newer-register span bounded by `B`, the single
split has a quadratic work bound and adds at most `3 * B + 6` register
symbols. The repeated machine has a proved `NatPolynomial` bound for each
fixed split count; the recursive size bound advances to `5 * B + 7`.
When the initial coordinate and every radix are bounded by `B`, the actual
appended register span is bounded by `splitCount * (3 * B + 6)`.
This is not a claim of a joint polynomial bound in a runtime-variable
split count, nor a completed source-to-formula execution bound.

The [regression module](../../lean-regression/PNPConcreteCookLevinBuilderRegionRadixDecoder.lean)
was prepared with the source. All 64 examples pass, covering universal
execution/refinement, complete frame preservation, written-result readout,
arithmetic and size bounds, control separation, zero splits, invalid width,
rectangle boundaries and the literal malformed-entry transition.
All 43 public theorem closures pass: two are axiom-free, fourteen use only
`propext`, and twenty-seven use `propext` with `Quot.sound`.
None uses a project-specific axiom, `Classical.choice` or `sorryAx`.

After the source and axiom audit passed, one regression required explicit
namespace qualification in its proof. Its assertion and the machine were
unchanged. The final regression run verified source-byte continuity and
reused those completed checks; no broad core or website suite was repeated.

## Verified implementation: source-derived radix branch entries

[CookLevinBuilderPolynomialRegisterCopies.lean](../../lean/PNP/Concrete/CookLevinBuilderPolynomialRegisterCopies.lean)
gives typed structural addresses into the polynomial postorder already
materialized by initialization. Its finite copy-list compiler preserves the
entire original register frame and protected workspace. The polynomial syntax
and address list determine control; no input value selects a table or supplies
a result. General execution, raw refinement and fixed-program polynomial
time/register-span bounds apply to arbitrary polynomials and addresses.

[CookLevinBuilderRegionRadixSource.lean](../../lean/PNP/Concrete/CookLevinBuilderRegionRadixSource.lean)
uses these addresses to read the actual stored tape width, shape width,
state count and literal three. Their exact connection to the concrete
tableau dimensions and positivity is proved without supplied width premises.
The canonical least-significant-first radix lists are:

- Shape: `[W + 2]`.
- Control: `[3, 3, states, W]`.
- Preservation: `[3, W, W]`.

Each branch entry physically copies the reversed radix list, then copies
the local coordinate from immediately before the retained region tag.
It executes the checked mixed-radix machine from that exact prepared frame.
The universal `source_workRunExact` starts on the actual
`BuilderConstraintRegionSource.finalConfiguration` tape under its
selected-region equality. It does not rerun source assembly or selection,
nor accept an independently supplied width, coordinate, quotient or result.
The complete original source, selected tag and workspace survive; the actual
written packets and final quotient reconstruct the local coordinate.

Under the existing body, cursor-balance and selected-region invariants,
the entry has a proved polynomial bound in encoded source length. Put
`B = 31 * sourceSpan(input.length) + 42`.
The source-copy span bound advances by `2 * B + 1` for each fixed address,
and the coordinate copy is charged before applying the radix execution bound.
The exact work count and its sixfold raw refinement include every field copy,
coordinate copy, division/restoration and control handoff. The final register
span is bounded as well; arbitrary existing output prefixes are preserved,
not misrepresented as newly generated bounded output. These bounds are for
fixed region schemas, not a runtime-variable split count.

All 62 prewritten [regression examples](../../lean-regression/PNPConcreteCookLevinBuilderRegionRadixSource.lean)
pass. They cover universal structural addressing, complete copying, source
handoff, branch execution/refinement, schema order and positivity, preservation,
written-coordinate reconstruction, time/space bounds and control separation.
All 58 public theorem closures pass: eight are axiom-free, thirteen use only
`propext`, and thirty-seven use `propext` with `Quot.sound`.
None uses a project-specific axiom, `Classical.choice` or `sorryAx`.
Initial failures were copy-layer proof normalization and state-projection
issues. Correcting those scripts did not change the machine definitions,
public theorem statements or prepared regression expectations. The region
entry module and all regressions passed their first execution after that
dependency compiled. No unchanged broad core or website suite was repeated.

## Verified implementation: tape-preserving runtime tag comparison

[CookLevinBuilderUnaryTagMatch.lean](../../lean/PNP/Concrete/CookLevinBuilderUnaryTagMatch.lean)
provides the general literal tag test needed by the runtime branch graph.
Its finite table depends only on the expected tag. For arbitrary actual tags,
older registers, protected workspace and exterior tape tail, the machine
reads the unary register physically and restores the entire tape and original
focus on both outcomes. It accepts exactly equal tags and rejects unequal
tags; it never generates a program from the actual tag or a semantic decoder.

The exact work count is `2 * min actual expected + 3`, bounded by
`2 * expected + 3`. An oversized tag therefore cannot force an unbounded
scan. The raw refinement costs six transitions per work step. Deterministic
rule queries and separated, rule-free accept/reject endpoints are checked.
An invalid entry marker enters a dead state rather than accepting.

All 25 prepared [regression examples](../../lean-regression/PNPConcreteCookLevinBuilderUnaryTagMatch.lean)
pass on their first execution. These include universal work/raw execution,
both tape-preserving outcomes, finite control contracts, the cost bound,
literal tags zero through four, shorter and oversized tags, nonempty
surrounding tape, missing markers and malformed unary input.
All 11 public theorem closures use only `propext` and `Quot.sound`;
none uses a project-specific axiom, `Classical.choice` or `sorryAx`.
Source development corrected record layout and proof normalization, replaced
an unavailable list-lemma name with a constructive induction, and made its
zero-add rewrite explicit. No machine behavior, public execution contract or
prepared regression assertion was weakened. The terminal targeted run passed;
no unchanged broad core or website suite was repeated.

## Verified implementation: uniform runtime region-entry dispatch

[CookLevinBuilderRegionRadixDispatch.lean](../../lean/PNP/Concrete/CookLevinBuilderRegionRadixDispatch.lean)
connects the five fixed tag checks to the five fixed source-derived radix
entries. The verifier determines the ten-node graph once. The actual tag is
read from tape; neither a semantic selected region nor a supplied branch
verdict constructs or chooses a runtime program. Failed comparisons preserve
the full selected frame before the next check.

The universal `dispatch_workRunExact` enters the matching radix program from
its actual selected frame. `reject_invalid_tag` rejects every unary tag at
least five in exactly 40 work steps, preserving older registers, protected
workspace and both tape tails. The five successful checking paths, including
their bridges, cost 4, 10, 18, 28 and 40 work steps respectively. The entry
execution and its final bridge are additionally charged.

The source-facing `workRunExact` starts at the original
`BuilderCursorSource.cursorTape`. It runs the existing source assembly and
region selection exactly once, then executes the fixed tag/entry graph.
The existing body guard derives the selected-region equality; there is no
extra caller-supplied region or branch-correctness premise. Raw refinement
includes every work step. The original source and workspace survive, and the
actual written radix packets and quotient reconstruct the local coordinate.

Under the existing body and cursor-balance invariants, `rawTimeBound_le`
bounds this entire execution by one polynomial in encoded source length.
It combines the source polynomial, the five fixed entry polynomials, and
252 raw transitions for all new tag/control bridges. The separate
`final_register_span_le` bounds generated register space by one polynomial
as well. Arbitrary previous output is preserved in the workspace, not
misrepresented as newly produced bounded output.

All 45 prepared [regression examples](../../lean-regression/PNPConcreteCookLevinBuilderRegionRadixDispatch.lean)
pass on their first execution. They check the fixed graph/entry connections,
all five route costs, general matching and out-of-schema execution, source
handoff, exact work/raw runs, preservation, reconstruction, complete time and
register-span bounds, and deterministic separated endpoints.
All 27 public theorem closures pass: five are axiom-free, five use only
`propext`, and seventeen use `propext` with `Quot.sound`.
None uses a project-specific axiom, `Classical.choice` or `sorryAx`.
The first source attempt exposed fixed-name, node-reference and arithmetic
index-normalization issues. Explicit mapped-name and path-step equalities
fixed those scripts without changing the machine, theorem statements or
prepared assertions, and without increasing resource or heartbeat limits.
No unchanged broad core or website suite was repeated.

## Representation contract: canonical local constraint payloads

The next dependency edge of the same legacy SAT-transport / complete
Cook-Levin construction is an unambiguous payload that the physical regional
constructors will write. Define that interface before building the writer.

Use delimiter-separated unary registers, in reversed reader order so the
finite tag is nearest the active end marker. Reader-order forms are:

- `[0]`: absent coordinate.
- `[1]`: an in-range padded empty constraint.
- `[2, sign, index]`: required literal.
- `[3, count, conclusionSign, conclusionIndex, premiseSign, premiseIndex, ...]`:
  implication, preserving the ordered list of all premises.
- `[4, count, variableIndex, ...]`: exactly-one constraint, preserving the
  ordered list of all variables.

Signs are exactly zero or one, indices must be strictly below the canonical
formula width, and list counts must match the entire payload. Reject unknown
tags, missing fields, trailing fields, odd literal pairs and invalid members.
Parse failure is a separate outer option, not either kind of empty slot.

The universal contract is `decode width (values slot) = some slot` for
every `Option (Option (LocalConstraint width))`, with injectivity, tag
placement and unary-space bounds. The source-specialized specification must
decode to `problem.formulaConstraintSlotDirect coordinate` at every
coordinate and agree with `BuilderConstraintRegionSource.slotForCoordinate`.
Derive its list-size premise from the existing canonical schedule theorem,
not from a caller-supplied size or correctness certificate. Bound the actual
unary register word, not just the number of registers, by one polynomial
in encoded source size.

Prepare source and regressions together: every constructor, arbitrary
literal/variable lists, exact signed/list order, both option layers, hostile
tags/signs/counts/widths, source equality and space bounds. Build only the
new permanent module, then audit every public theorem closure and run the
focused regression. Unchanged source-routing, root and website suites do not
establish a new boundary here. Root/inventory/publication registration waits
for the complete M230 capability.

This interface is not physical construction. In particular,
`canonicalValues` is an endpoint specification only, never an executable
call to the host-side semantic decoder. A successful codec/space theorem
does not prove the writer's runtime or earn the complete-builder checkpoint.

## Verified interface: canonical local constraint payloads

[CookLevinBuilderLocalConstraintPayload.lean](../../lean/PNP/Concrete/CookLevinBuilderLocalConstraintPayload.lean)
establishes the universal representation and size contract for the next
physical writer. The parser preserves both slot option layers, and its
separate outer result distinguishes malformed data from an absent or padded
opportunity. Exact signs, indices, list order and list counts survive the
roundtrip. Injectivity prevents two different constraints or slot states
from sharing a payload.

The tag is proved to be the final logical register, nearest the active
end marker. For a canonical variable bound `B`, the representation has
at most `2 * B + 10` registers, each at most `2 * B + 4`. Consequently
the complete delimiter-separated unary word has at most
`(2 * B + 10) * (2 * B + 5)` cells. The source-specialized theorem
derives `B` and constraint boundedness from the existing canonical
formula schedule and gives one polynomial in encoded input length for
every constraint coordinate. It does not take a supplied size certificate.

All 52 prepared [regression examples](../../lean-regression/PNPConcreteCookLevinBuilderLocalConstraintPayload.lean)
pass on their first execution. Besides the universal roundtrips and bounds,
they independently check signed/order fixtures and reject unknown tags,
extra or missing fields, invalid signs, odd literal pairs, inconsistent
counts and out-of-width indices. All 20 public theorem closures pass:
one is axiom-free, four use only `propext`, and fifteen use
`propext` with `Quot.sound`. None uses a project-specific axiom,
`Classical.choice` or `sorryAx`.

Two earlier source attempts exposed a reserved binder name and explicit
option reduction, map-argument and list-membership grouping issues. The
corrections preserved the representation, parser behavior, mathematical
statements and all prepared regression expectations. The successful
permanent target, complete public closure audit and regression run reached
a terminal zero result. No unchanged broad core or website suite was repeated.

This remains an interface, not a physical writer. `canonicalValues`
specifies the required result using the semantic slot definition; no finite
machine is permitted to call that semantic function at runtime. Constructing
and timing that result from the actual source/radix frame remains the next
obligation, with no score, row or full-builder credit for this interface.

## Physical input-reader contract

The initial-row constraints in both verifier input modes require bits from
the actual source. For the same legacy SAT-transport / complete-builder
dependency, implement one fixed machine with no source-dependent program
generation. Its entry is the existing scratch-end tape with an arbitrary
requested index in the nearest unary register.

Use temporary marks to pair consumed index units with skipped input cells.
Return 0 for an absent bit, 1 for false and 2 for true, in one appended
unary register. Restore the original index, every older register and every
visited input cell. Preserve the source boundary, tally and arbitrary previous
output; stop at the source terminator without scanning output. Include the
focused blank cell of the empty input and arbitrary pre-existing exterior
garbage, charging the cells overwritten by the new result register.

The intended universal endpoint is `BuilderIndexedInputRead.workRunExact`:
for all older registers, indices, inputs, outputs and exterior tails, actual
execution ends at `endTape (older ++ [index, resultCode input[index]?])`,
with unchanged `inside input output` and only the allocated result cells
dropped from the exterior tail. Prove raw refinement, exact scan/restore
costs, polynomial work in the materialized register span and index, and the
constant added register-space bound. No index bound or supplied bit answer
is a premise of exact execution; source-size bounds for the physical index
must be derived when this primitive is connected to regional construction.

Prepare the source with tests for the universal work/raw runs, every result
code, empty source, boundary/out-of-range reads, order-sensitive inputs,
arbitrary output and garbage preservation, independent literal table traces,
cost formulas, complete time/space bounds and invalid entry markers. Build
the permanent reader first, audit every public theorem closure, then run
the focused regression. Reuse unchanged source/payload/routing evidence.

This reader is a physical dependency of canonical initial constraints, not
a completed constraint writer, formula loop or reduction. Do not award
M230, a publication row or weighted progress credit for this primitive alone.

### Verified input-reader implementation

The fixed 162-rule machine in
[`CookLevinBuilderIndexedInputRead.lean`](../../lean/PNP/Concrete/CookLevinBuilderIndexedInputRead.lean)
now proves the intended universal execution and six-step raw refinement.
It reads the requested source position, restores all index/source marks and
appends the result code. Empty and past-end reads return absence without
crossing into the tally or arbitrary prior output. The exact allocated
exterior span is `resultCode + 1`, so the new register adds at most three
cells. No requested-index bound or supplied bit answer is required for
the execution theorem.

The complete work bound is
`(index + 1) * (2 * olderSpan + 6 * index + 12)`.
If the materialized older-register span and index are both bounded by
`B(input.length)`, raw execution is bounded by
`6 * (B(input.length) + 1) * (8 * B(input.length) + 12)`.
This conditional source-size bound does not supply those bounds for a future
caller: regional construction must derive them from its actual written data.

All 17 public theorem axiom closures passed: two are axiom-free, two use
only `propext`, and thirteen use only `propext` and `Quot.sound`.
The
[46 focused regressions](../../lean-regression/PNPConcreteCookLevinBuilderIndexedInputRead.lean)
passed, including independent literal rule-table executions, order-sensitive
reads, empty and out-of-range sources, arbitrary output/exterior preservation,
exact costs, polynomial bounds, result-space growth and invalid entry markers.
Three unreachable function-equality branches needed explicit constructive
contradictions to avoid an incidental `Classical.choice` dependency. Source
proof and record-layout corrections did not change the machine, intended
theorem statements or regression assertions. The syntax-only regression fix
reused the unchanged successful source build and full public axiom audit.

The reader is now available for physical initial-row construction; it does
not itself derive a regional request, build a canonical payload, or complete
the formula loop. M230 and the complete-builder checkpoint remain unearned.

## Next implementation: physical canonical constraint construction

Construct the payload from the physically written regional coordinates and
actual source. Preserve the canonical shape, initial, control, preservation
and accepting constraints and both option layers. Derive all widths, literal
indices, transition choices and mode-dependent input symbols from the
verified frame; do not supply a constraint, input answer, branch verdict,
result map or correctness certificate. Reuse actual branch control without
rerunning the original source assembly.

Cover the unbounded families, including input-only and paired initial symbol
opportunities and padded preservation diagonals. Initial and accepting empty
radix lists do not construct their constraints. Derive and copy source indices
from those regional opportunities, then use the verified indexed reader.
Its complete execution preserves prior output without scanning it; retain that
boundary and derive the caller's actual register-span and index bounds.
Do not charge an arbitrary output prefix as automatically source-size bounded.

The physical writer must prove that decoding what it actually writes equals
the canonical slot, with its complete execution cost. Physical clause
occupancy, token emission, scratch recovery, Finish, explicitly cleared padding
and the complete loop/packaged reduction remain downstream obligations.

M230 and its fixed complete-builder checkpoint remain unearned. Publication
is deferred because the full end-to-end construction is not yet complete.
Risk-weighted proof completion estimate: 35%; uncertainty: 20% to 40%;
formal artefact coverage: 205/207; global gates closed: 0/5.

## Runtime coordinate arithmetic contract

The next canonical-constraint dependency needs literal indices formed from
already materialized dimensions and runtime regional coordinates. Continue
the same legacy Final SAT decision / concrete Cook-Levin reduction anchor.
Reuse the existing unary evaluator's proved constant, addition and
multiplication phases rather than rebuilding their scans.

Expose preserved-register arithmetic with a finite operator/offset-dependent
table, universal exact work/raw execution, unchanged operands and inside tape,
exact exterior allocation and bounds in the actual operand-register span.
A constant is fixed program syntax; binary operand values must be read from
the tape and must not be compiled into a source-dependent machine.

Then structurally compile expressions over a fixed-size register environment.
The AST contains constants, statically addressed arguments, addition and
multiplication. The intended universal endpoint
`BuilderRegisterExpression.workRunExact` starts from the original environment
plus retained scratch, appends the postorder values with the correct root
value, and preserves the entire original frame. The machine depends only on
the AST and structural register counts, never on the environment's values.
Prove the complete execution cost and actual unary-space bounds by polynomial
majorants, including copies, intermediate arithmetic and every chain join.
Environment presence/count is a physical layout invariant, not a supplied
value or correctness certificate.

Use this compiler for the canonical symbol, head, state, certificate-bit and
certificate-length layout formulas. Derive their argument frames from the
existing source and regional registers before claiming a canonical writer.
The full constraint payload still needs bounded family loops, fixed verifier
transition selection, derived input requests and payload assembly; all
occupancy, emission, scratch recovery, Finish and complete-builder obligations
remain downstream.

Prepare universal arithmetic/compiler work and raw refinements, positive
and negative literal execution fixtures, nontrivial operand order, zero
products, arbitrary retained data, static control shape, exact allocation and
complete time/space expectations with the sources. Build changed dependencies
before imported axiom probes, then run focused regressions. Reconcile root,
inventory, publication and generated contracts only once the complete M230
target stabilizes. No weighted checkpoint, row or site-publication credit is
awarded merely for these arithmetic components.

## Verified: preserved arithmetic and canonical literal-index kernels

The preserved-register constant/addition/multiplication interface is now
proved in
[the unary evaluator](../../lean/PNP/Concrete/CookLevinBuilderUnaryPolynomial.lean).
It reuses the existing phase rules and proofs. Binary operands come from
the tape; the operator and structural separation determine the finite table.
Exact work/raw execution preserves both operands, intermediate registers
and arbitrary inside data. Allocation is exactly the result plus its
separator. Bounds include every copy and multiplication step and use the
actual unary operand span, not merely the number of registers.

[The fixed expression compiler](../../lean/PNP/Concrete/CookLevinBuilderRegisterExpression.lean)
now proves `BuilderRegisterExpression.workRunExact` and its raw refinement
for every expression over a fixed-size environment. The entire original
frame survives; the postorder values are appended, with the evaluated root
as the last register. Its complete time and surviving-space majorants include
argument copies, intermediate results and both joins at each binary node.
The machine depends on expression syntax and structural offsets, never on
runtime register values. An initial encoded-span polynomial yields the
complete expression execution and output-span polynomials.

[The literal-index kernels](../../lean/PNP/Concrete/CookLevinBuilderLiteralIndexExpression.lean)
apply that compiler to all five canonical families: symbol, head, state,
certificate bit and certificate length. Every typed request satisfies
`eval_eq_index`, `workRunExact` and `run_compile_exact` for the unchanged
canonical layout. The materialized environment has the fixed order
`[T, W, S, C, time, position, state, symbolCode]`; existing layout bounds
give its complete unary span, including separators, at most
`8 + 8 * layout.variableCount`. The source-size theorem derives this
bound from the verifier's formula-variable-count polynomial. One fixed
polynomial pair bounds all five kernels, independent of runtime kind or
coordinates; the retained-context bound remains an explicit caller obligation.

The prepared
[36 arithmetic](../../lean-regression/PNPConcreteCookLevinBuilderRegisterArithmetic.lean),
[33 compiler](../../lean-regression/PNPConcreteCookLevinBuilderRegisterExpression.lean)
and
[42 literal-index](../../lean-regression/PNPConcreteCookLevinBuilderLiteralIndexExpression.lean)
regressions passed. All 19 new arithmetic theorem closures plus four reused
primitive endpoints, all 16 compiler closures and all 12 literal-index
closures were audited. They use at most `propext` and `Quot.sound`, with
no project-specific axiom or `Classical.choice`. Compiler/list-layout
proof corrections and a constructor-shadowing binder correction did not
weaken the intended statements or prepared regression assertions. Each
unchanged green component was reused by exact source and regression digests.

These are register arithmetic kernels, not a completed canonical writer.
Typed requests specify the expected layout index; they neither materialize
the eight argument registers nor select a runtime branch. The next physical
construction must derive those registers from the already written source
dimensions and regional coordinates, and connect its actual output to this
environment. Initial-row requests must likewise derive their source index
before using the verified indexed reader. Bounded family iteration, fixed
verifier transition selection, payload assembly, clause occupancy, token
emission, scratch recovery, Finish and cleared padding still precede the
complete formula loop and packaged reduction. No supplied request, constraint,
input answer or correctness certificate may replace that construction.

M230 and `reductions-complete-cook-levin-builder` remain unearned.
Risk-weighted proof completion estimate: 35%; uncertainty: 20% to 40%;
formal artefact coverage: 205/207; global gates closed: 0/5.
No publication row or score was added; PNPLabs publication remains deferred.

## Source-derived literal argument construction contract

Continue the same pinned Final SAT decision / Accepted package implies P=NP
dependency: literal indices must be computed from the builder's actual written
data before the canonical constraint and formula can be emitted.

The next physical component must pack a fixed list of constant/register
references without reevaluating source polynomials. Compile the list using the
proved one-register constant/argument cases of the expression compiler.
Its universal `BuilderRegisterPack.workRunExact` endpoint must preserve the
original environment, retained registers and arbitrary inside/exterior data,
append exactly the selected values, and charge every copy and chain join.
Prepare order-sensitive literal executions, repeated references, constants,
zero/empty cases, preserved scratch and complete time/space expectations with
the source before testing.

Then bind fixed argument references to the actual
`BuilderRegionRadixSource.finalValues` frame. Source dimensions come from
structural addresses in the already evaluated clause-count polynomial.
Certificate width is zero for input-only mode and the copied certificate bound
for paired mode. Regional digits come from their six-register result packets;
the final quotient and any retained loop-counter registers must also have
proved physical addresses. The source-frame length and all offsets depend
only on the verifier, branch schema and structural register counts.

A fixed eight-reference plan must physically append its eight derived values
and compose with the selected fixed literal-index expression. The intended
`BuilderLiteralArgumentSource.workRunExact` and raw refinement start from
the existing radix frame plus retained registers; neither an environment nor
a supplied literal answer is an endpoint premise. Prove source-size bounds
from the existing radix-span theorem and the actual retained-context bound.
The plan is finite program syntax, not a runtime decoder or a correctness
certificate.

This closes argument materialization, not canonical branch selection. The
complete writer must still derive the required plans and counters for every
canonical constraint family, wire the branch continuation into the existing
uniform graph, and prove the exact decoded payload. Initial input requests,
bounded family iteration, transition selection, occupancy/emission, scratch
recovery, Finish, cleared padding and the full loop/reduction remain open.
Do not award a row, weighted point or M230 merely for this component.

Run changed leaves and their axiom probes before focused regressions; reuse
the unchanged arithmetic/expression/radix evidence. Reconcile root, inventory
and publication contracts only at the complete M230 integration boundary.
PNPLabs publication remains deferred; the coherent M229 snapshot is unchanged.

## Verified: source-derived argument packing and literal execution

[The fixed register packer](../../lean/PNP/Concrete/CookLevinBuilderRegisterPack.lean)
now compiles constant/register references into consecutive fields using the
existing one-register expression cases. It preserves the complete original
environment, retained registers and arbitrary inside/exterior data. Its exact
work/raw endpoints account for every copy, constant write and chain handoff,
including the final identity endpoint. The polynomial bounds cover both the
complete execution and the surviving unary register span.

[The source-bound argument constructor](../../lean/PNP/Concrete/CookLevinBuilderLiteralArgumentSource.lean)
connects that packer to the actual
`BuilderRegionRadixSource.finalValues` frame. Structural source addresses
select time count, tape width, state count, certificate bound and fuel from
the already evaluated clause-count polynomial. Certificate width is written
as zero in input-only mode and copied in paired mode. Regional digits are
read from the proper six-field division packets; the final quotient and
retained counter references have separate proved physical addresses.

The eight-field output always begins with the actual `T, W, S, C).
A fixed plan contains only four coordinate references and cannot replace those
source dimensions. Its references may select existing source fields, packet
digits, the final quotient, retained registers or fixed syntax constants.
`environment_values` and `field_eval` prove that these references read the
actual written frame. `pack_workRunExact` appends the eight derived values;
`workRunExact` and `run_compile_exact` then execute the selected literal
expression from that physical endpoint. No environment or literal answer is
supplied as an execution premise. `final_index_register` identifies the
last written result, and `source_polynomial_bounds` includes packing plus
the literal computation and their join. It derives the source-frame bound
from the existing radix theorem and retains the actual counter-span bound
as an explicit caller obligation.

All
[35 packer regressions](../../lean-regression/PNPConcreteCookLevinBuilderRegisterPack.lean)
and
[52 source-binding regressions](../../lean-regression/PNPConcreteCookLevinBuilderLiteralArgumentSource.lean)
passed. The packer's ten and constructor's eighteen public theorem closures
use at most `propext` and `Quot.sound`, with no project-specific axiom or
`Classical.choice`. The original prepared assertions cover both certificate
modes, control/preservation packet order, empty-radix branches, retained
counters, exact physical endpoints and complete bounds. A reserved binder
and an unspecified rewrite input needed elaboration corrections; no machine,
theorem statement or regression assertion was weakened. Existing green
arithmetic, expression, packer and literal-index evidence was reused by
exact source/test digests, with changed imports rebuilt before axiom probes.

This does not establish that every chosen plan is a valid canonical request.
The complete writer must derive the required coordinate plans and bounded
counters for every canonical family, prove their type/range and layout-index
linkage, and wire these continuations into the existing uniform branch graph.
Initial source-index derivation, transition selection, exact payload assembly,
occupancy/emission, scratch recovery, Finish, cleared padding and the complete
formula loop/reduction remain open. The four-reference plan is finite program
syntax, never a caller-supplied correctness certificate.

M230 and `reductions-complete-cook-levin-builder` remain unearned.
Risk-weighted proof completion estimate: 35%; uncertainty: 20% to 40%;
formal artefact coverage: 205/207; global gates closed: 0/5.
No publication row or score was added. PNPLabs publication remains deferred
until the complete capability changes the public bottom line.

## Source and expectation preflight

Prepare each producer change and its consumers together, before its first
verification command. Reconcile the entire affected family after any discovered
stale expectation, not just the first failing assertion.

| Changed contract | Expectations prepared with the change | First evidence |
| --- | --- | --- |
| Physical selector and successor | Intended all-input theorem type, literal fixtures for every route family, workspace preservation and negative staging/claim cases | Changed module, focused Lean regression and public-declaration axiom probe |
| Complete loop and encoded output | Arbitrary-prefix invariant, zero/full boundary cases, timeout and exact-output regressions | Loop module and focused root-import regression |
| Complete polynomial construction | Encoded-input-size bounds covering selection, handoff, loop and output; mutations that omit a phase or use semantic-only execution | Complete builder and reduction tests |
| Theorem registration | Root imports, reviewed declaration names, required-name contract, fingerprint key set and milestone entry | Name-set comparison before compiled inventory extraction |
| Generated evidence and progress | Generator inputs, canonical ledger state and history, status/mirror fields and all current documentation consumers | Generate after successful compilation, then targeted check mode |
| Publication and workflows | Source pins, current-value fixtures, all latest-milestone trust-layer mutations and embedded workflow assertions | Focused positive and negative publication preflight before a broad audit |

Keep historical milestone snapshots fixed. Derive current values from canonical
data, but retain independent theorem/type, axiom, security and hostile-mutation
invariants. Do not invent future declaration counts, digests or score changes.

## Verification ownership and release

All processing runs on the configured remote builder. Reuse the exact starting
tree's verified build cache; rebuild modified dependency chains and the root
before audits import them. Run focused checks first. Delay generated inventory,
status and report work until the proof source and expectation inputs stabilize.

The core repository owns Lean compilation, regressions, axiom auditing, compiled
inventory and proof-report generation. Require its normal PR and post-merge
checks and exact-merge verification. PNPLabs then verifies the exact core pin,
byte-identical mirrors, conservative claims, generated pages, links, browser
behavior, hostile publication cases and release provenance. It must not repeat
the core Lean build or regenerate the proof report. Deploy only the verified
site merge and independently verify production.

Send concise progress notifications for meaningful completed phases and
actionable blockers. Keep proof estimate, artefact coverage and global gates
separate. A phase completion is not an earned full-builder checkpoint.

## Remaining project obligations

Even a complete Cook-Levin reduction does not provide a deterministic SAT
algorithm. The unconditional residual-band minimizer, global ZeroSlack,
PCCMin exactness and total polynomial/certificate bounds, deterministic CNFSAT
membership in P, required final model linkage and the exact eligible root theorem
remain separate obligations. Publication stays fail-closed until its own exact
root/type/fingerprint/axiom requirements pass.

### Control-family implementation contracts

The active transition work retains the canonical three-premise implication and
all three conclusions. The coordinate contract covers every transition step,
tape position, verifier state, read symbol and conclusion slot, not a finite
fixture. The runtime action is the fixed verifier's actual `localAction`:
halting states and missing rules stutter, left motion saturates at zero, and
right motion stays put at the final tape cell.

Compile the finite action table from the verifier alone. Its runtime selector
must read the actual source-derived state/symbol index, preserve the original
register frame and both tape tails, and write the selected action fields without
a supplied lookup answer. Empty or out-of-range lookups must reject with an
unchanged tape. A fixed table is allowed here because the verifier, not the
source input, determines its entire state space; the input-dependent formula,
positions and time coordinates must never be compiled into a control table.

Prepare universal coordinate, payload-order/decoder, action-selection,
wrong-index rejection, exterior-preservation, exact-run and polynomial-bound
regressions alongside their producers. Audit the complete new public theorem
interfaces. Reuse unchanged dependency evidence; no existing publication or
inventory producer changes until the full M230 integration. The final control
payload, movement calculation, clause emitter, loop and packaged reduction
remain required even after the coordinate and action-selection components pass.

### Verified control coordinates and physical source-derived actions

The complete control rectangle is now reconstructed in
[`CookLevinBuilderControlCoordinates.lean`](../../lean/PNP/Concrete/CookLevinBuilderControlCoordinates.lean).
Every valid step, position, verifier state, read symbol and one of the three
conclusions maps to the unchanged canonical direct slot. The written radix
packet determines all five coordinates. The payload specification has the
original three premises in their exact order and signs, the selected canonical
conclusion, and the existing implication tag; its decoder returns that slot.

[`CookLevinBuilderRegisterTable.lean`](../../lean/PNP/Concrete/CookLevinBuilderRegisterTable.lean)
compiles an arbitrary fixed finite table. A physical unary test selects each
row; a match writes its constants, and failure proceeds to the next fixed key.
The exact run covers every actual key, including an empty table, an empty
successful row, a key below the first entry and an oversized key. Rejection
leaves the entire tape unchanged; successful allocation drops exactly the
selected register-word span from the exterior. The complete lookup has a
fixed-table runtime ceiling and an output-span polynomial. It is not permission
to generate an input-sized table as finite program syntax.

[`CookLevinBuilderControlActionSource.lean`](../../lean/PNP/Concrete/CookLevinBuilderControlActionSource.lean)
binds that compiler to the actual verifier. `rowValues_input_independent`
proves that the empty-input carrier used to construct the finite table has
the same action fields as every source input. Its proof covers halting-state
stuttering, missing-rule stuttering and the actual selected rule; the carrier
is not a restriction to an empty-input fixture.

The source expression reads the state and read-symbol radix fields and writes
`[state, 3, state * 3, symbol, state * 3 + symbol]`. The fixed lookup then
writes target state, write-symbol code and movement code. The complete machine
depends only on the verifier. Its exact work/raw execution requires the actual
control-region premise, not a supplied state, action, verdict or payload.
The original source/radix frame and arbitrary interior are retained; the final
exterior drops precisely the key-expression span plus the selected action span.
Encoded-input polynomial bounds cover expression work, the entire lookup,
their chain bridge and the complete retained output.

The three components passed 93 regression contracts: 33 coordinate, 31 fixed
lookup and 29 source-action checks. All 50 public-theorem axiom audits passed:
six closures use no axioms, four use only `propext`, and forty use only
`propext` and `Quot.sound`. No project-specific axiom or
`Classical.choice` occurs. Proof-script fixes resolved scalar reassociation,
endpoint/conditional normalization and elimination of proof-indexed transition
matches without changing the finite machines or intended theorem statements.
Two fixture notation fixes narrowed imported names and normalized a true
conditional; no expected execution result or mathematical assertion changed.
Successful unchanged build and axiom phases were reused, including the fixed
table's build after its regression-only import correction.

### Next control-family dependency

Use the derived action fields to compute the canonical moved position
physically. Prove the complete stay/left/right dispatcher for every position,
including saturated subtraction at zero and a right move at the last tape
cell. The code must read the written movement code; neither the branch nor the
moved position may be supplied as a runtime answer.

Then derive next time and all four literal indices from the same source/action
frame, select the actual conclusion digit, and assemble the complete three-
premise implication payload. Preserve one fixed register-count interface and
account for every cleared or allocated exterior cell across all branches.
Prepare generic boundary, literal-order, source-link, exact-run and polynomial-
bound regressions before compilation. The existing `movePosition` and
`controlConstraints` remain the canonical specification.

M230 and `reductions-complete-cook-levin-builder` remain open. The complete
control payload, initial and accepting families, canonical clause emission,
full physical successor, main loop and packaged reduction are still required.
No publication row or weighted checkpoint was earned by these components.
PNPLabs publication remains deferred; the published M229 coordinate and all
progress values remain unchanged.

## Active control movement: exact exterior boundary

The next implementation closes the physical head-movement dependency of the
same legacy Final SAT decision / SAT NP-completeness reconstruction above.
Its unbounded interface reads the source-derived movement code and position,
implements stay, saturated predecessor and the right-edge clamp for every
valid tape position, and leaves one fixed retained-register count.

Before wiring in comparison, establish that the existing disposable-pair
comparator preserves its outer end marker. A generic exact-trace framing
theorem must derive preservation of arbitrary exterior data from the finite
rule table and the starting boundary, not from a supplied footprint or an
empty-exterior assumption. Reuse the unchanged comparator trace and cost.
Any newly allocated restoration cell must be physically reserved or blanked,
charged, and reflected in the exact exterior suffix.

The comparison/cleanup interface must return the actual strict-less verdict
while restoring the older source registers on both branches. The movement
graph must select its branch by reading the written movement code. It must
not accept the moved position or comparison verdict as supplied data.
The final control implication still needs next time, all four literal indices,
the actual conclusion selector and the complete canonical payload.

Prepare exact generic run, raw-compilation, nonblank-exterior, boundary-safety,
zero/last-cell, branch-outcome, register-count and encoded-size polynomial
regressions together with the source. Audit every new public theorem; reject
project axioms and choice. Unchanged source-action, preservation and shape
evidence is reused. No source statements or test expectations are weakened,
and no progress, publication or immutable historical data changes.

## Verified control-movement comparison and recovery boundary

The exact arbitrary-exterior comparison boundary is now implemented in
[`WorkMachineLeftBoundary.lean`](../../lean/PNP/Concrete/WorkMachineLeftBoundary.lean)
and
[`CookLevinBuilderRegisterPairExterior.lean`](../../lean/PNP/Concrete/CookLevinBuilderRegisterPairExterior.lean).
The first theorem transports an existing exact trace across a protected left
boundary, deriving safety at every step from the finite rule table. The second
checks that rule condition for the unchanged disposable-pair comparator and
connects its terminal tape to the existing restoration view. It preserves the
entire arbitrary exterior suffix without identifying it with blank cells.
The original comparator, its verdict and its execution bound are unchanged.

[`CookLevinBuilderRegisterLessThan.lean`](../../lean/PNP/Concrete/CookLevinBuilderRegisterLessThan.lean)
now implements one fixed six-node comparison/recovery graph for every pair of
natural-number operands and arbitrary interior/exterior data. Its reserve
machine increments and decrements the newest operand in five work transitions:
the operand is restored, one exterior cell is prepared, and the untouched
exterior is exactly its original tail after that cell. The graph then executes
the existing comparator, restores its actual marked result and erases the three
disposable registers. The comparison verdict is carried by physical control,
not by a supplied premise or a host-side choice.

For input `endTape (older ++ [coordinate, boundary]) inside outside`, both
outcomes return the exact tape

```lean
endTape older inside
  (List.replicate (coordinate + boundary + 3) WorkSymbol.blank ++ outside.drop 1)
```

Acceptance is equivalent to `coordinate < boundary`; rejection is equivalent
to `boundary ≤ coordinate`. Equal operands, the zero cases and a right-move
candidate at the last cell are covered by the generic contracts. All original
older registers and the interior are retained. The allocated exterior cell and
every cleared cell are accounted for explicitly. Exact raw execution charges
six raw transitions per work transition, and the quadratic polynomial bound
includes reservation, comparison, restoration, erasure and every graph bridge.

All 51 prepared regression contracts passed: 20 boundary/comparator and 31
comparison/recovery checks. All 27 public-theorem axiom audits passed: five
closures use no axioms, six use only `propext`, and sixteen use only
`propext` and `Quot.sound`. No project axiom or `Classical.choice` occurs.
Proof-script corrections addressed finite Boolean reflection, graph-entry
normalization and Lean record notation without changing the machines, intended
theorem statements or expected outcomes. When only regression notation changed,
the successful build and axiom phases were reused against their exact source
trees; failed whole runs were not reported as green.

### Next exact control-head contract

The next machine must read `[width, position, moveCode move]` from tape and
append exactly one moved-position register while retaining those inputs.
Its intended universal execution interface is:

```lean
workRunExact? machine (workSteps width position move)
  (workStartConfiguration machine
    (endTape (older ++ [width, position, moveCode move]) inside outside)) =
  some {
    state := machine.acceptState
    tape := endTape
      (older ++ [width, position, moveCode move, moved width position move])
      inside (finalOutside width position move outside) }
```

Here `moved` is position for stay, `position - 1` for left, and
`if position + 1 < width then position + 1 else position` for right.
The planned fixed dispatcher tests the written movement code, copies the
position, and physically tests zero before a left decrement. The right branch
increments the copied position, copies that candidate and the actual width,
executes the now-verified strict comparison, and decrements the candidate only
on the non-less branch. Invalid direction codes must reject, not silently
select a default move.

Bind this generic machine to the existing eight source-derived action registers:
copy the source width and position plus retained movement field seven, then
append the moved position. The combined retained count is fixed, and the
canonical `VerifierTableauProblem.movePosition` equality must hold for every
valid position. Next time, all four literal indices, the actual conclusion
digit and the complete three-premise implication remain required afterwards.

This component does not yet implement that complete movement dispatcher, the
control payload, remaining constraint families, clause emission, full successor,
loop or packaged reduction. M230 and `reductions-complete-cook-levin-builder`
remain open. Formal artefact coverage stays 205/207; the risk-weighted proof
estimate stays 35% with uncertainty 20% to 40%; global gates closed stay 0/5.
PNPLabs publication remains deferred at its coherent M229 source pin.

## Verified source-derived control-head movement

The control-clause dependency now has a complete physical movement operation,
not another fixed position or schedule prefix. The legacy anchor remains the
Cook-Levin local transition implication and its canonical bounded head update
in `VerifierTableauProblem.movePosition`. This retires the movement edge of
the current control-payload plan; it does not retire the full formula-builder
checkpoint.

[`CookLevinBuilderRegisterHeadMove.lean`](../../lean/PNP/Concrete/CookLevinBuilderRegisterHeadMove.lean)
implements one fixed thirteen-node graph for every natural width and position.
Its runtime input is `[width, position, moveCode move]`; its output retains
those three registers and appends the computed position. Stay copies the
position. Left tests zero before decrementing. Right increments a copied
candidate, compares it with the actual width, restores the original frame, and
decrements only when the candidate is not strictly inside the width. The
general result equals the canonical bounded head operation at every
`Fin width` position. Invalid movement codes reject with the full input tape
unchanged; they do not silently select a default move.

The theorem accounts for arbitrary older registers and arbitrary interior and
exterior tape data. The right-path comparison exterior is exactly

```lean
List.replicate (position + width + 4) WorkSymbol.blank ++
  outside.drop (2 * position + width + 6)
```

and a clamped right move adds one cleared cell. The other paths account for
their copied and cleared cells explicitly. Exact raw execution includes every
graph bridge and six raw transitions per work transition. The retained-space
and complete runtime bounds are polynomial in a bound on the encoded input
register frame, not merely a termination argument.

[`CookLevinBuilderControlHeadSource.lean`](../../lean/PNP/Concrete/CookLevinBuilderControlHeadSource.lean)
binds that operation to the existing source-derived control action. Its program
depends only on the verifier. It executes the transition lookup, copies the
source width and position and retained movement field seven, and then runs the
fixed movement graph. The execution specification uses the source coordinate
to identify the intended action; no action or moved position is supplied to
the executable machine. The control-region premise establishes valid slot
membership rather than a caller-supplied movement verdict.

The combined result keeps twelve retained registers: the existing eight action
registers, the three copied movement operands, and the moved position. The
final frame equality, canonical moved-position equality, exact work/raw runs
and polynomial runtime and retained-space bounds all hold for every valid
source-derived control slot. The composed bounds are in the original encoded
source-input length and charge action lookup, copying, movement and both
composition bridges.

All 67 prepared regression contracts passed:
[`PNPConcreteCookLevinBuilderRegisterHeadMove.lean`](../../lean-regression/PNPConcreteCookLevinBuilderRegisterHeadMove.lean)
contains 41, and
[`PNPConcreteCookLevinBuilderControlHeadSource.lean`](../../lean-regression/PNPConcreteCookLevinBuilderControlHeadSource.lean)
contains 26. The checks pin the universal execution interfaces, edge behavior,
invalid-code rejection, canonical source binding, preserved frame, exact
exterior and polynomial bounds. All 42 public-theorem axiom audits passed:
five closures use no axioms, three use only `propext`, and thirty-four use only
`propext` and `Quot.sound`. No project axiom or `Classical.choice` occurs.
The source-binding implementation and its prepared regressions passed on the
first compilation. Initial dispatcher proof-script corrections changed no
machine, theorem statement or expected outcome.

The unchanged comparison/action dependencies were reused at their exact
verified source identities. After the dispatcher passed, its 41 regressions
and 23 axiom audits were not repeated for the source-binding-only addition.
The complete milestone still requires its root, inventory, publication and
release verification after the remaining construction is implemented.

### Next complete control-payload contract

Starting with these twelve source-derived retained registers, physically derive
next time and all four literal indices. The original current state, read symbol
and position remain in the radix frame; action fields five and six contain
target state and write symbol, and retained field eleven contains the verified
moved position. The actual conclusion digit must select the state, head or
symbol conclusion at next time through runtime control.

For every valid control slot, the complete branch must write the canonical
three-premise implication payload:

```text
[readIndex, 1, headIndex, 1, stateIndex, 1, conclusionIndex, 1, 3, 3]
```

Prove this against `BuilderControlCoordinates.candidate_payload` and
`source_slot`, retaining exact frame/exterior accounting and an encoded-input
polynomial bound. A caller-supplied conclusion, selected branch, action,
literal index or correctness certificate is not an implementation of this
contract. This must be one all-slot construction covering every conclusion
kind, not a sequence of new fixed-coordinate milestones.

Next time, all four literal indices, the complete implication payload,
remaining constraint families, clause emission, full successor, loop and
packaged reduction remain open. M230 is not earned, and
`reductions-complete-cook-levin-builder` remains open. Formal artefact coverage
stays 205/207; the risk-weighted proof estimate stays 35% with uncertainty 20%
to 40%; global gates closed stay 0/5. PNPLabs publication remains deferred:
this is a verified dependency component, while the coherent public snapshot
remains pinned to M229.

## Verified source literals and static control-implication branches

The next-time and literal-index dependencies of the legacy Cook-Levin
transition implication now have source-derived executable implementations.
The unbounded domain is every valid control slot for every source input,
rather than another fixed circuit, position or schedule prefix.

[`CookLevinBuilderControlLiteralSources.lean`](../../lean/PNP/Concrete/CookLevinBuilderControlLiteralSources.lean)
extends the verified action/head construction with physical next-time
arithmetic. It writes the current time, one and their sum after the twelve
existing retained registers, producing fifteen source-derived registers.
Next time is therefore at retained position fourteen. All three premise roles
and all three possible conclusion roles have fixed source-reference plans:

- Current state uses current time and the decoded state.
- Current head uses current time and the decoded position.
- Current read symbol uses current time, position and read code.
- Next state uses the computed next time and action target field five.
- Next head uses the computed next time and moved-position field eleven.
- Next write symbol uses next time, the original position and action field six.

One universal environment/index theorem covers all six roles and arbitrary
later scratch registers. The canonical request is an execution specification;
the machine receives neither a request nor a literal index as a supplied
answer. Each first-literal program physically executes the complete
action/head/time preparation and the existing source-fed index machine.
Exact work and raw execution, retained-register counts, exact exterior
accounting and polynomial bounds in original encoded input length are checked.

[`CookLevinBuilderControlImplicationPayload.lean`](../../lean/PNP/Concrete/CookLevinBuilderControlImplicationPayload.lean)
implements all three static conclusion branches. Each branch computes the
conclusion index and the three premise indices, retains their roots at
positions derived from the expression-node counts, and physically copies the
canonical ten-register payload:

```text
[readIndex, 1, headIndex, 1, stateIndex, 1, conclusionIndex, 1, 3, 3]
```

The output decodes to the exact control constraint with that static conclusion
kind. When the branch's code equals the source conclusion digit, the decoded
output equals `controlConstraintSlotDirect` at the actual source coordinate.
That equality is a branch-selection interface, not a supplied premise closing
the still-open runtime dispatcher. The final payload is exposed on the tape
with the previous source and scratch frame intact. The exterior formula
accounts for the head-movement cleanup and every subsequent written register.
Complete branch runtime and retained-space bounds include all four index
constructions, packing and composition bridges.

All 66 prepared regression contracts passed:
[`PNPConcreteCookLevinBuilderControlLiteralSources.lean`](../../lean-regression/PNPConcreteCookLevinBuilderControlLiteralSources.lean)
contains 37 and
[`PNPConcreteCookLevinBuilderControlImplicationPayload.lean`](../../lean-regression/PNPConcreteCookLevinBuilderControlImplicationPayload.lean)
contains 29. They cover all source roles and static conclusion kinds, canonical
root retention, exact execution, payload decoding and polynomial bounds.
A negative length contract prevents replacing the control payload with the
old eight-register preservation shape. All 48 public-theorem axiom audits passed: two closures use no axioms
and forty-six use only `propext` and `Quot.sound`. No project axiom or
`Classical.choice` occurs in the final verified closures.

The strict audit caught a classical dependency introduced by proving a
conjunction of arithmetic bounds in one tactic invocation. Constructing the
conjunction explicitly and proving each inequality separately removed that
dependency without changing any mathematical statement, machine or expected
outcome. Explicit intermediate tape contracts also avoided unfolding composed
machine internals during elaboration. Failed or audit-rejected runs are not
verification evidence. The unchanged source-literal build, 37 regressions and
27 axiom audits were reused while checking the assembler addition.

### Next source-driven conclusion dispatcher

Implement one fixed graph that reads the actual conclusion digit from the
existing control radix frame and executes the matching verified branch. No
caller-selected conclusion or branch-correctness certificate may enter the
public execution interface. The intended program is:

1. Copy radix digit zero into one disposable register.
2. Test the written tag against zero, one and two.
3. On each matching path, erase that disposable register and restore the exact
   original source frame before executing the corresponding static branch.
4. Reject unmatched tags; never silently select a default branch.
5. Use the observed successful tag test to prove the branch-selection equality,
   then derive the exact canonical source-slot payload without an additional
   selection premise.

The existing `BuilderRegisterErase.one_workRunExact` takes `tag + 2` work
transitions and returns the exact exterior

```lean
List.replicate (tag + 1) WorkSymbol.blank ++ outside.drop (tag + 1)
```

after the preceding tag copy. Thus neither a tag register nor an unaccounted
scratch cell may remain at the branch entry. The source tag is a decoded
`Fin 3` value. The planned three tag tests, erasure and graph bridges have a
constant bound; copying and the selected full branch retain their existing
encoded-input polynomial bounds. Prove the graph, physical execution, source
selection, canonical payload, exact exterior and uniform polynomial bounds
together, with regression and axiom expectations prepared before compilation.

The runtime dispatcher, remaining constraint families, clause emission, full
successor, loop and packaged reduction remain required. The complete control
family is not yet earned, M230 is not earned, and
`reductions-complete-cook-levin-builder` remains open. Formal artefact coverage
stays 205/207; the risk-weighted proof estimate stays 35% with uncertainty 20%
to 40%; global gates closed stay 0/5. PNPLabs publication remains deferred at
the coherent M229 source pin until a major complete capability or other
publication trigger is actually verified.

## Verified runtime control-family payload construction

The control-family dependency of the legacy SAT-transport reconstruction now
has a complete physical payload constructor at the source-derived control
radix-frame entry.
[`CookLevinBuilderControlPayload.lean`](../../lean/PNP/Concrete/CookLevinBuilderControlPayload.lean)
fixes one ten-node graph from the verifier alone. It copies source conclusion
digit zero, tests tags zero, one and two, erases that disposable register, and
executes the matching verified state, head or symbol implication branch.
An invalid written tag rejects without invoking any payload branch.

The universal work/raw execution and canonical decoding interfaces take no
caller-selected conclusion, action, literal index or selection certificate.
The source coordinate itself derives the equality previously required by the
static branch interface. The constructed ten-register payload decodes to
`problem.controlConstraintSlotDirect` at the actual local coordinate.
The exact final tape retains the source/scratch frame and accounts for the
erased tag's exterior before the selected branch allocates its own registers.

All tests and graph bridges, tag erasure and the final branch bridge contribute
at most 25 work transitions beyond the source-tag copy and selected complete
payload construction. Raw execution multiplies work by six. The universal
source-size theorem includes the tag-copy polynomial, all branch-construction
costs and the constant overhead. The final register span is polynomial in
the original encoded input length; a branch result is not supplied as an
unpriced answer.

The prepared
[`PNPConcreteCookLevinBuilderControlPayload.lean`](../../lean-regression/PNPConcreteCookLevinBuilderControlPayload.lean)
regression has 34 passing contracts, including source-only selection,
all three kinds, exact cleanup, canonical source-slot equality, compiled
execution, invalid-tag rejection and encoded-input polynomial bounds.
All 24 public-theorem axiom audits passed: two are axiom-free and twenty-two
use only `propext` and `Quot.sound`. No project axiom or `Classical.choice`
appears. The first build's proof-normalisation errors were corrected without
changing machine definitions, intended theorem statements or test outcomes.
Only the changed dispatcher dependency was rebuilt; the already verified
literal, static implication, head-movement and source-action evidence was
reused. Failed runs are not verification evidence.

### Next complete initial-row family contract

Continue the same all-input construction, not a sequence of initial fixed-slot
fixtures. The remaining initial family is defined by
`VerifierTableauProblem.initialConstraintSlotDirect` in
[`CookLevinFormulaCursor.lean`](../../lean/PNP/Concrete/CookLevinFormulaCursor.lean).
Its two initial state/head constraints precede the padded mode-dependent
symbol program. The initial region has no radix factors, so its retained
quotient is still the entire local coordinate, not a decoded cell answer.

The intended `BuilderInitialPayload.machine verifier` must start from
`BuilderRegionRadixSource.finalValues problem index remaining .initial`,
derive every branch/index from that frame and the actual source, and write a
payload whose decode is exactly `some (problem.initialConstraintSlotDirect
(BuilderConstraintRegionSource.localCoordinate problem index .initial))`.
Its public exact-execution interface must not require a selected cell,
certificate length, source bit, slot, payload or correctness certificate.

Cover both input modes and all valid initial coordinates:

- Input-only cells derive their actual initial symbol, using the verified
  indexed reader where needed and preserving blank/input boundaries.
- Paired mode begins with the certificate-length exactly-one constraint.
  Subsequent blocks are the canonical flattened one- or two-constraint cell
  programs for every permitted length and tape position. Derive the variable
  block widths and offsets; a rectangular replacement is not equivalent by
  definition and must not silently change the formula or slot order.
- Blank/fixed cells produce length-conditional implications. Certificate cells
  produce both signed-bit implications in their existing order.
- Preserve the distinction between in-range padding and an absent coordinate.

Prove a complete coordinate-selection abstraction for these variable-width
blocks and connect it to literal machine operations. Bind reader requests to
source-derived indices and charge their actual retained span. Reuse the
reader's source/output restoration theorem: arbitrary prior output is
preserved without being assumed source-size bounded or scanned gratuitously.
Prepare universal type, axiom, hostile-padding and source-order expectations
with the implementation. Do not replace a failed general derivation by a
supplied cell-selection premise or another fixed initial slot.

The initial and accepting constructors, whole-region payload wiring, clause
occupancy/emission, scratch recovery, full successor, loop and packaged
reduction remain open. M230 is not earned and the fixed
`reductions-complete-cook-levin-builder` checkpoint remains open.
Formal artefact coverage remains 205/207. The risk-weighted proof estimate
remains 35%, with uncertainty 20% to 40%; global gates closed remain 0/5.
PNPLabs publication remains deferred at the coherent M229 pin: completing
one regional payload entry is not the full all-input formula builder.

### Initial-cell arithmetic and compressed-width implementation contract

Before implementing the physical initial-row dispatcher, derive arithmetic
cell requests in `BuilderInitialCellCoordinates`. This closes the concrete
cell-location and variable-block-width dependency named above. It is not an
alternative formula, a supplied-data completion result or a runtime claim.

For every input, allowed certificate length, center and tape position,
resolve the arithmetic request to exactly the existing `initialCellAtCoordinate`
over `pairedInitialCells` or `inputOnlyInitialCells`. A source-bit request
contains only an index; its semantic resolution is not permission for a
finite machine to receive the bit as an answer. Prove that every paired
source-bit request lies within the actual source length.

Preserve the existing two length-prefixed frames. The certificate-variable
interval starts at `center + 2 * input.length + length + 2` and has exactly
`length` cells. Derive each cell's one/two-constraint width from this interval.
For an arbitrary clipped tape window, prove the exact width sum
`count + min length (count - start)`, including empty/outside intervals.
Then derive the paired model's interval coverage from the actual dimensions,
so every canonical length row has width `tapeWidth + length`.

Prepare universal resolution, field-order, delimiter, empty/boundary,
clipped-interval, source-index, exact-width and axiom-closure regressions with
the source. The physical length/cell selector, indexed-reader handoff,
literal/payload writer and full initial-row execution remain required; the
coordinate result alone does not earn M230 or change either public metric.

### Derived paired length-row selector contract

Use the proved `tapeWidth + length` row width to implement
`BuilderInitialLengthSelection.locate count width coordinate`.
Compare the residual coordinate with the current width; when it does not fit,
subtract that width, increment the width and consume one remaining row.
Return the derived row and residual offset, or absence after all rows are
exhausted. Do not accept a precomputed width table or selected length.

Prove equivalence to the canonical `DirectSlot.flatFinite` lookup over
widths `width + row`, including zero-width and out-of-range cases. Every
returned offset must fit its row and reconstruct the original coordinate
from the exact preceding-row span. Absence must be equivalent to passing
the complete span. Derive the source-specialized equality with
`problem.pairedCellsSlotDirect` from the compiled exact row-width theorem.

The arithmetic comparison count is at most the permitted number of lengths;
the total span has a polynomial numeric bound in row count and tape width.
Neither fact is a raw finite-machine execution theorem. The physical cursor
must still implement and charge comparison, residual subtraction, row-count
decrement, width/index increment and all bridges, retaining its source frame.
Keep that distinction in tests, progress reporting and subsequent wiring.

### Verified initial-cell arithmetic and paired length selection

[`CookLevinBuilderInitialCellCoordinates.lean`](../../lean/PNP/Concrete/CookLevinBuilderInitialCellCoordinates.lean)
now derives every initial-cell request from arithmetic coordinates, preserving
both length prefixes, their delimiters, source-bit order, certificate-variable
indices, left blank cells and past-end blanks. Universal resolution equals
the existing canonical initial-cell definitions in both input modes.
Every paired source-bit request is proved to lie within the actual input.

The one/two-constraint cell width equals the indicator of the exact
certificate-variable interval. Its clipped sum is
`count + min length (count - start)`. The actual paired tape dimensions
contain the complete interval, yielding exactly `tapeWidth + length`
constraints for each canonical length row. No width table is supplied.

[`CookLevinBuilderInitialLengthSelection.lean`](../../lean/PNP/Concrete/CookLevinBuilderInitialLengthSelection.lean)
uses those widths in one arithmetic cursor: test the residual coordinate,
or subtract the current width, increment it and consume another row.
Its derived row/offset reproduces `DirectSlot.flatFinite` and the exact
`problem.pairedCellsSlotDirect` order. A successful result has an in-row
offset, an exact preceding-span equation and a complete-span bound.
Absence is equivalent to exhausting the canonical span, including zero-width
and out-of-range cases. Arithmetic row comparisons are bounded by
`certificateLimit + 1`; total span has the stated numeric polynomial bound.
These are specification and loop-invariant results, not a claim that the
physical selector has been implemented or has polynomial raw runtime.

All 73 prepared regression contracts passed: 42 in
[`PNPConcreteCookLevinBuilderInitialCellCoordinates.lean`](../../lean-regression/PNPConcreteCookLevinBuilderInitialCellCoordinates.lean)
and 31 in
[`PNPConcreteCookLevinBuilderInitialLengthSelection.lean`](../../lean-regression/PNPConcreteCookLevinBuilderInitialLengthSelection.lean).
All 35 public-theorem axiom audits passed: four use only `propext` and
thirty-one use only `propext` and `Quot.sound`. No project axiom or
`Classical.choice` occurs. Proof-normalisation, conditional-rewrite and
constructor-bridge fixes preserved the definitions, theorem statements and
regression outcomes. The length-selector check reused the exact verified
cell-coordinate source, its 42 regressions and 22 axiom audits.

### Next exact cell offset and physical selector boundary

For a selected paired row, let `W` be tape width, `L` the derived
certificate length, `A = center + 2 * input.length + L + 2`, and `j`
the derived row offset. The proved model gives `A + L <= W` and
`j < W + L`. Derive the canonical position and within-cell offset by:

- `j < A`: position `j`, within-cell offset zero.
- `A <= j < A + 2 * L`: position `A + (j - A) / 2`,
  within-cell offset `(j - A) % 2`.
- Otherwise: position `j - L`, within-cell offset zero.

Prove equality to the existing flattened cell program, not a rectangular
replacement. Include zero-length, first/last certificate bit and both
transition boundaries. Derive all bounds from the selected row and actual
model, not from a supplied cell-selection certificate.

Then realize the row cursor with physical retained registers for remaining
rows, selected-length counter, current width and residual coordinate.
Maintain `remainingRows + length = certificateLimit + 1`,
`currentWidth = W + length`, and the proved original-coordinate/prefix-span
equation. The loop must decrease remaining rows even if a width were zero.
Implement and charge every comparison, subtraction/restoration, decrement,
increment, scratch allocation and graph bridge. Reuse existing comparison
and recovery interfaces, but do not mistake their restored operands or
discarded temporary registers for an updated residual result.

Exhaustion of paired cells inside a valid padded initial region must produce
the canonical empty-slot payload, not silently become an invalid-coordinate
claim. After physical row/cell selection, bind the verified indexed reader
to the actual source and derive required state, head, symbol, certificate-bit
and certificate-length literal indices. Any new index-expression cases must
update their complete test/producer/consumer contracts in the same change.
The one-hot length prefix and two leading state/head requirements remain
part of the complete initial family.

Physical initial-row construction remains open, as do accepting payloads,
whole-region wiring, occupancy/emission, scratch recovery, successor, loop
and packaged reduction. M230 is not earned and
`reductions-complete-cook-levin-builder` remains open. Formal artefact
coverage remains 205/207; the risk-weighted proof estimate remains 35%,
with uncertainty 20% to 40%; global gates closed remain 0/5.
PNPLabs publication remains deferred at the coherent M229 pin.

### Within-row selector implementation contract

Continue the same pinned manuscript/Cook--Levin initial-tableau dependency,
without substituting a rectangular schedule. The new unbounded arithmetic
decoder will return `(position, withinCell)` from the actual row offset.
Its universal contract is `position < W`,
`withinCell < intervalWidth A L position`, and
`j = position + min L (position - A) + withinCell` whenever
`A + L <= W` and `j < W + L`. The source-facing function derives the
containment premise from the actual paired tableau dimensions.

The exact consumer is `problem.pairedCellsForLengthSlotDirect`, followed
by `problem.pairedCellsSlotDirect` through the verified length cursor.
Prove pointwise equality for every coordinate, including exhaustion, by
matching the existing `DirectSlot.flatFinite` prefix. No selected cell,
width table, source bit, family or correctness certificate is supplied to
the source-facing selection function.

Prepare the producer and regression contracts together in
`CookLevinBuilderInitialCellSelection.lean` and its matching regression.
Test zero width/length, both interval joins, both certificate polarities,
the final cell, exhaustion and arbitrary source-specialized theorem types.
Audit every public theorem after building its permanent Lake target.
Reuse the unchanged initial-coordinate and length-selection evidence.
This dependency addition does not change a generated publication contract,
inventory name set, status, weighted checkpoint or public site pin; complete
M230 integration must still update the root and all release consumers.
Physical row/cell selection, initial literal production and the remaining
whole-builder obligations above stay open until independently proved.

### Verified canonical paired-cell coordinate selection

[`CookLevinBuilderInitialCellSelection.lean`](../../lean/PNP/Concrete/CookLevinBuilderInitialCellSelection.lean)
now proves the planned within-row inverse for every contained certificate
interval and every valid row coordinate. It derives a bounded cell, a
within-cell offset and the exact preceding-span equation. The generic
prefix lemma connects that arithmetic result to the existing compressed
`DirectSlot.flatFinite` order, including the exhausted tail.

The source-facing `selectedCell` derives interval containment from the
actual paired tableau dimensions. `selectedInitialCell` composes it with
the verified length cursor, deriving certificate length, cell position
and within-cell offset from a single paired-cell coordinate. Its lookup
is pointwise equal to `problem.pairedCellsSlotDirect`, and absence is
equivalent to exhausting `problem.pairedCellsWidthDirect`. There is no
supplied row, selected cell, width table, source bit or correctness premise
in that selection function.

All 44 prepared contracts in
[`PNPConcreteCookLevinBuilderInitialCellSelection.lean`](../../lean-regression/PNPConcreteCookLevinBuilderInitialCellSelection.lean)
pass, including zero width/length, both interval joins, both slots of
certificate cells, the final cell, exhaustion, wrong rectangular offsets
and arbitrary source-facing theorem types. All 11 public-theorem axiom
audits pass with only `propext` and `Quot.sound`; no project axiom or
`Classical.choice` occurs. A comment-delimiter fix and finite-index,
induction and reflexive-goal proof corrections preserved the intended
definitions, statements and regression expectations. A runner-only failed
preflight launched no Lean work; the final complete target run passed.
The exact unchanged cell-coordinate and length-selection evidence was
reused rather than rerun.

### Physical row-loop residual boundary: inspected next interfaces

The next implementation must return a usable residual, not just the
existing `BuilderRegisterLessThan` verdict: that helper restores and then
erases all three comparator registers. Its lower-level
`BuilderRegionResidualRegisters.ofComparison_restoredValues` instead
returns these exact ordinary registers:

- Less: `[coordinate, 0, boundary]`.
- Equal: `[boundary, 0, boundary]`.
- Greater: `[boundary + 1, coordinate - boundary - 1, boundary]`.

These shapes follow the actual comparator result with initial processed
count zero; they still need the corresponding derived arithmetic lemma
and a physical residual-return adapter. In the greater case, the second
register alone is one below the required residual.

`BuilderRegisterPack` appends selected copies and preserves its original
frame; it does not compact away the restored registers. Do not assume
otherwise when specifying the row loop. A fixed branch graph can recover
the comparator tape, append boundary plus the appropriate residual copy,
and increment that copy only on the actual greater branch. Its proposed
output is `older ++ restoredValues ++ [boundary, nextCoordinate]`, where
`nextCoordinate = coordinate` for the accepting less branch and
`coordinate - boundary` for the non-less continuation. Derive that result
from the actual comparator; do not accept a caller-supplied verdict.

Before implementation, finalize the adapter's exact exterior allocation,
work-step count and source-polynomial bounds using the existing reserve,
copy, increment and recovery theorems. Explicitly account for the three
retained scratch registers in each row iteration, the remaining-row
decrement and the selected-length/current-width increments. Either clean
them physically or carry a proved bounded history and recover it later;
a copying packer is not an eraser. The entire row selector must still be
one fixed finite graph, not an input-dependent unrolling.

The arithmetic decoder and its tests do not establish that physical
adapter, the row loop, initial literal production or polynomial execution
of the complete construction. M230 is not earned. Formal artefact coverage
remains 205/207; risk-weighted proof estimate remains 35%, with uncertainty
20% to 40%; global gates closed remain 0/5. No weighted checkpoint changed.
PNPLabs publication remains deferred at the coherent M229 pin.

### Physical comparison/residual-return implementation contract

Continue the same M230 all-input initial-row cursor dependency. Implement
`CookLevinBuilderRegisterCompareResidual` as one fixed eight-node graph:
reserve, compare, less/non-less recovery, three fixed packing branches and
the greater-only increment. Its machine must not depend on the coordinate,
boundary, comparator result or an execution certificate.

For every natural coordinate and boundary, arbitrary older registers and
arbitrary inside/exterior tape data, prove an exact `workRunExact?` trace
from `endTape (older ++ [coordinate, boundary]) inside outside`.
The result must retain the actual three recovered registers and append
`[boundary, nextCoordinate]`, where `nextCoordinate` is the original
coordinate for the less branch and `coordinate - boundary` otherwise.
Accept means strict less; reject is the non-less continuation, not an
invalid-input claim. Derive both from the actual comparator.

The exact exterior is
`outside.drop (boundary + nextCoordinate + 3)`: one restoration cell,
two appended register delimiters, their unary contents and any required
greater-branch increment. Include each graph transition in the work-step
count and derive the six-step raw refinement from the exact work trace.
Prove encoded-source-polynomial final span and runtime from the actual
input register-span bound. In particular, neither a finite trace nor a
standalone arithmetic subtraction supplies the physical result.

Prepare tests for zero operands, less/equal/greater, the greater-by-one
correction, preserved older/source/exterior data, exact graph control,
the generic execution/refinement types and polynomial-bound contracts.
Audit all public theorems after the permanent target build. Reuse unchanged
arithmetic-selector and primitive evidence. No generated status, inventory
or website values change for this internal dependency; full M230 root and
release integration remain due. The bounded row loop, physical cell
decoder, initial payloads and the complete packaged reduction remain open.

### Verified fixed physical comparison and residual return

[`CookLevinBuilderRegisterCompareResidual.lean`](../../lean/PNP/Concrete/CookLevinBuilderRegisterCompareResidual.lean)
implements the planned single eight-node graph. It reserves the restoration
cell, runs the actual comparator, recovers the three ordinary registers,
packs the appropriate fixed references and increments the copied residual
only on the actual greater branch. The public `workRunExact` theorem
covers every natural coordinate/boundary and arbitrary older registers,
inside data and exterior suffix. No verdict or execution certificate is
supplied. Acceptance is exactly strict less; rejection is the non-less
continuation.

The final tape retains the three restored registers and appends the
boundary plus the original coordinate when less, or the exact subtraction
otherwise. Its exterior is exactly
`outside.drop (boundary + nextCoordinate + 3)`.
The source-derived boundary and residual identities, fixed control,
six-step raw refinement and polynomial final-span/runtime bounds all
compile. The span bound includes the retained recovery scratch; the
runtime bound includes packing, the correction and every graph bridge.
These bounds concern this primitive, not the complete formula builder.

All 39 prepared contracts in
[`PNPConcreteCookLevinBuilderRegisterCompareResidual.lean`](../../lean-regression/PNPConcreteCookLevinBuilderRegisterCompareResidual.lean)
pass, including zero operands, all three branches, greater by one, exact
retained registers, arbitrary inside/exterior data and a concrete exterior
sentinel. All 19 public-theorem axiom audits pass: four are axiom-free, two
use only `propext`, and thirteen use only `propext` and `Quot.sound`.
No project axiom or `Classical.choice` occurs. Record-layout and constant
proof-normalisation corrections preserved the machine and theorem types.
The long-exterior regression needed typed intermediate equalities rather
than deeper definitional reduction; its expected output was unchanged.
The final regression pass reused the identical successful permanent target
and axiom transcript. No unchanged selector proof was rerun.

### Next bounded row loop: concrete four-register layout

Use the ordinary newest frame `[length, width, residual, remainingRows]`
rather than placing the countdown underneath newly generated fields.
The existing `BuilderUnaryTagMatch.machine 0` tests that newest register
and preserves the tape; the existing decrement handles its positive case.
This avoids a new marked-counter representation or a scan across a
non-register marker when copying source fields.

At the loop head, maintain the remaining-row/length, width and original
coordinate/prefix-span invariants already specified above. For one attempt:

1. Test the newest remaining count. Zero means canonical row exhaustion.
   Otherwise decrement it physically before preparing the comparison.
2. From `[L, W, j, R - 1]`, append copies `[j, W]` using fixed
   arity-four references. Feed those two copies to the verified residual
   adapter. The result is nine retained registers: the original four,
   the adapter's three recovered registers, then `[W, nextCoordinate]`.
3. On strict less, return the found row. Its length and within-row offset
   remain at fixed addresses in that nine-register suffix. The already
   decremented count belongs to the attempt phase, not the loop-head
   invariant.
4. On non-less, append the next newest frame
   `[L + 1, W + 1, j - W, R - 1]` and loop. Starting from the nine
   registers above, the four physical copy offsets are 8, 2, 2 and 8,
   with a physical increment immediately after the first two copies.
   These offsets count newer registers at the moment of each copy.

Thus a continuing iteration retains nine history registers and installs
one new four-register frame. Do not call a packer an eraser. Define that
history and the exterior transformation recursively, prove exact
execution by induction on the physically decreasing remaining count, and
derive polynomial bounds for the whole history and loop before accepting
the selector. Explicitly charge the zero test, decrement, comparison
preparation, residual adapter, four copies, two increments and all bridges.
A zero-width row still consumes one remaining count.

The source-facing initial case is `length = 0`,
`width = tapeWidth`, `remainingRows = certificateLimit + 1`.
Bind the loop result to `BuilderInitialLengthSelection.locate` and
`selectedLength`, using the actual source-derived registers. Derive
exhaustion and successful selection rather than supplying either one.
The fixed graph must be independent of the number of rows, and its
retained history must subsequently be recovered in the initial-payload
integration.

The complete row loop, physical within-row decoder, initial and accepting
payloads, whole-region wiring, emission/recovery/successor loop and
packaged reduction remain open. M230 is not earned. Formal artefact
coverage remains 205/207; the risk-weighted proof estimate remains 35%,
with uncertainty 20% to 40%; global gates closed remain 0/5.
No fixed checkpoint changed. PNPLabs publication remains deferred at the
coherent M229 source pin.

### Bounded physical row-loop implementation contract

Continue the initial-row selection dependency of M230's pinned **Final SAT
decision / Accepted package implies P=NP** transport, without changing the
canonical formula or adding a selection premise. Implement
`CookLevinBuilderInitialRowLoop` as one fixed five-node cyclic graph:
zero-test, decrement, comparison-operand packing, comparison/residual return,
and a fixed six-operation continuation. The continuation copies offsets
8, 2, 2 and 8, incrementing the first two copies; it does not depend on
the number or values of rows.

For every remaining count, current length, current width and coordinate,
arbitrary older registers and inside/exterior data, prove exact
`workRunExact?` execution from the ordinary newest frame
`[length, width, coordinate, remaining]`. Derive the entire retained history
and exterior transformation recursively from the actual comparison, and
derive the six-step raw-machine refinement. Prove that acceptance/exhaustion
matches `BuilderInitialLengthSelection.locate`, including zero counts,
zero-width rows and coordinates beyond the whole family. Bind the
source-facing initial case to the canonical `selectedLength`; successful
row/offset data must be physically present, not merely named by the semantic
specification.

Charge every test, decrement, copy, increment, comparison and bridge.
Derive a polynomial bound for the complete surviving history and the whole
loop from the encoded input-register span. The row counter decreases
physically even for a zero-width row. Do not infer polynomial time merely
from termination or use a supplied bound table or execution certificate.

Prepare the generic theorem/type and exact tape/control regressions with
the source, including first-row, later-row, exhaustion, zero-width,
greater-correction and arbitrary exterior preservation cases. Run the
permanent target before public-theorem axiom extraction and the focused
regression. Reuse unchanged primitive evidence. Complete M230 root,
inventory, release and exact-merge checks remain due at integration.
The physical within-row decoder, initial/accepting payloads, full formula
loop and packaged reduction remain open. No status, weighted checkpoint or
PNPLabs publication change is earned by this component alone.

### Verified bounded physical initial-row loop

[`CookLevinBuilderInitialRowLoop.lean`](../../lean/PNP/Concrete/CookLevinBuilderInitialRowLoop.lean)
now implements the fixed five-node cyclic graph. It tests and physically
decrements the newest remaining-row register, prepares actual coordinate
and width copies, runs the verified comparison/residual adapter, then
either accepts or installs the next four-register frame. Its continuation
uses exactly the planned copy offsets and two physical increments. Neither
the number of rows nor a supplied branch result generates the program.

The general `workRunExact` theorem derives the complete trace for every
count, current length, width and coordinate, arbitrary older registers,
inside data and exterior suffix. It includes zero-width rows, which still
consume one remaining count. `run_compile_exact` establishes the literal
six-step raw refinement. `finishValues` and `finishOutside` account for
the entire retained comparison history and exact exterior transformation;
the loop does not pretend that copying erases its inputs.

Acceptance and exhaustion agree with
`BuilderInitialLengthSelection.locate`, and the source-facing interfaces
bind those outcomes to `selectedLength` and the canonical paired-family
width. `found_suffix` proves that the selected length and offset are
physically present at the first and last positions of the final
nine-register suffix, with exactly seven intervening registers. They are
not merely names for an externally supplied semantic answer.

The encoded-register-span bound covers the complete retained history.
For an incoming span bounded by the polynomial `B`, the final span is at
most `B + (B + 1) * (9 * B + 13)`. The whole-loop raw runtime is bounded
by a fixed per-attempt polynomial times `B + 1`. The proof charges every
test, decrement, operand copy, comparator/restorer step, continuation copy,
increment and bridge. It uses a physically decreasing counter and
source-span-derived bounds, not finite termination as a substitute for
polynomial runtime. These are bounds for this complete row-loop component,
not for the still-unfinished formula builder or PCCMin construction.

All 42 prepared contracts in
[`PNPConcreteCookLevinBuilderInitialRowLoop.lean`](../../lean-regression/PNPConcreteCookLevinBuilderInitialRowLoop.lean)
pass: fixed control/copy addresses, first and later rows, exact threshold
exhaustion, zero widths, greater-branch correction, retained history,
exterior sentinels, generic execution/refinement, physical result suffix,
canonical source binding and polynomial bounds. All 27 public-theorem
axiom audits pass: four are axiom-free, six use only `propext`, and
seventeen use only `propext` and `Quot.sound`. No project axiom or
`Classical.choice` occurs. Tape/list normalization, field-identity and
arithmetic-rewrite fixes preserved the machine, theorem statements and
expected outputs. The final regression pass corrected only its namespace
import and reused the identical successful permanent target and axiom
transcript.

### Next dependency: physical within-row decoding and history recovery

Implement the already specified general
`BuilderInitialCellSelection.cellCoordinate` on physically present
certificate-start, selected-length and within-row-coordinate registers.
Use a fixed first comparison against the certificate start, then a fixed
comparison of the residual against twice the selected length. In the
paired interval, physically derive quotient and remainder modulo two;
outside it, derive the ordinary cell position and zero offset. Preserve
the exact canonical ordering and prove the result/encoded-size contracts
for arbitrary inputs. Do not generate a machine from a selected cell,
quotient, residual or branch verdict.

Bind the interval start and row-width data to the actual source model.
Before wiring the decoder into the initial payload, resolve access to
older source metadata and recovery across the variable retained row
history. The final suffix has fixed addresses, but the original source
frame does not acquire a fixed copy offset merely because its contents
were preserved. Include explicit history handling and its cost; retain
the complete row-loop evidence instead of recompiling it during unchanged
downstream checks.

The physical within-row decoder, complete initial and accepting payloads,
whole-region wiring, emission/recovery/successor loop and packaged
reduction remain open. M230 is not earned. Formal artefact coverage
remains 205/207; risk-weighted proof estimate remains 35%, with uncertainty
20% to 40%; global gates closed remain 0/5. No fixed checkpoint changed.
PNPLabs publication remains deferred at the coherent M229 source pin.

### Physical halving reuse contract for the within-row decoder

Continue the same pinned **Final SAT decision / Accepted package implies
P=NP** transport. The paired-cell decoder's middle interval requires a
physical quotient and remainder modulo two. Reuse the existing fixed
`BuilderClauseDividerExecution.divisionMachine` and
`BuilderDividerCoordinateRegisters.machine`; do not reimplement their
already verified division and restoration traces.

The reuse boundary is the builder's fresh outer frontier. The existing
divider theorem takes an empty outer tail, while preserving arbitrary
older registers and inside/source/output data. Prove
`BuilderInitialRowLoop.finishOutside remaining length width coordinate [] = []`
and the corresponding final-tape projection in the new adapter. This
derives the row-loop handoff instead of silently treating arbitrary
nonempty exterior data as blank. Do not claim a general nonempty-tail
divider transport that has not been proved.

Implement `CookLevinBuilderRegisterHalve` as one fixed composition:
pack `[0, 0, value, 2]` from the actual newest value, divide, restore the
six ordinary result registers, then append their quotient and remainder.
The program must not depend on the value, quotient, remainder or branch
answer. For every natural value, arbitrary older registers and arbitrary
inside data, prove exact execution from
`endTape (older ++ [value]) inside []`, the exact retained output word,
a fresh final frontier, raw refinement and encoded-register-span
polynomial runtime/output bounds. Both division operands are physically
constructed; positivity is the literal divisor two, not a supplied premise.

Prepare the generic execution, canonical quotient/remainder, retained
scratch, zero/even/odd, source-frontier handoff, control and polynomial
regressions with the source. Audit every public theorem after the
permanent target build. Keep the row-loop source and its successful
verification unchanged. The complete three-branch cell decoder,
source-metadata/history recovery, initial and accepting payloads, full
formula loop and packaged reduction remain open. This internal component
does not earn M230, a weighted checkpoint or a PNPLabs publication.

### Verified fixed halving adapter at the builder frontier

The permanent target
[`CookLevinBuilderRegisterHalve`](../../lean/PNP/Concrete/CookLevinBuilderRegisterHalve.lean)
now composes the existing physical divider and restorer with two fixed
register packs. For every natural input value, it physically constructs
`[0, 0, value, 2]`, divides by the literal positive divisor two, restores
ordinary registers, and appends the computed quotient and remainder.
The fixed program receives neither value-dependent control nor supplied
quotient/remainder data.

The exact retained output word is:

```text
[value, 0, 0, (value / 2) * 2, value % 2, 2, value / 2,
 value / 2, value % 2]
```

The last two fields are the quotient and remainder. The output has nine
registers and exact encoded span `3 * value + 11`; the intermediate
scratch is represented rather than silently discarded. Arbitrary older
ordinary registers and arbitrary inside/source/output data are preserved.

The public `row_loop_frontier` and `row_loop_final_frontier` theorems
derive the empty outer frontier from every execution description of the
existing initial-row loop, including exhaustion and zero-width cases.
`division_restore_handoff` proves the exact divider-to-restorer tape
identity. This makes the fresh-frontier reuse boundary explicit:
`workRunExact` starts from `endTape (older ++ [value]) inside []` and
`final_frontier` proves that the resulting outer frontier remains empty.
No arbitrary nonempty-tail divider transport is claimed.

The adapter's `workRunExact`, `run_compile_exact`, final-tape,
control-disjointness and terminal-state theorems all build. For an
incoming encoded register-span bound `B`, `source_polynomial_bounds`
proves output span at most `3 * B + 8` and a polynomial raw-time bound
accounting for preparation, division, restoration, result packing and
all three composition bridges. The bound reuses the existing divider
execution theorem; no uncounted search or supplied runtime certificate
is introduced.

All 38 prepared contracts in
[`PNPConcreteCookLevinBuilderRegisterHalve`](../../lean-regression/PNPConcreteCookLevinBuilderRegisterHalve.lean)
pass: generic and concrete zero/even/odd execution, retained scratch,
quotient/remainder reconstruction, negative field expectations,
source-frontier handoff, arbitrary older/inside preservation, exact
output span, compiled refinement, polynomial bounds and fixed-control
contracts. All 22 public-theorem axiom audits pass: seven are axiom-free,
five use only `propext`, and ten use only `propext` and `Quot.sound`.
No `Classical.choice` or project-specific assumption enters the closure.

The permanent target, public axiom probe and complete prepared regression
file passed in one terminal successful targeted run. Reuse that exact
source/toolchain/boundary evidence while documenting this result; the
unchanged row loop and underlying division components do not need
separate duplicate builds.

### Next dependency: complete three-branch cell decoding

Compose the existing comparison/residual adapter, fixed register
operations and this halving adapter into one physical implementation of
the canonical before-interval, paired-interval and after-interval cell
coordinate cases. Prove exact input-derived branch selection,
position/offset fields, tape preservation and encoded-span polynomial
bounds. Retain the actual frontier invariant through each handoff.

The decoder must then be connected to the proved terminal row suffix
and source-derived certificate interval. Source metadata hidden behind
variable row history still requires actual machine-level recovery;
do not replace that obligation with a supplied family, branch answer
or correctness certificate. Initial and accepting payload production,
the full formula loop and the packaged all-input polynomial reduction
remain open. M230 is not earned. Formal artefact coverage remains
205/207; risk-weighted proof estimate remains 35%, with uncertainty
20% to 40%; global gates closed remain 0/5. No fixed checkpoint changed.
PNPLabs publication remains deferred at the coherent M229 source pin.

### Complete physical cell-decoder contract

Continue the pinned **Final SAT decision / Accepted package implies
P=NP** dependency by implementing the complete canonical within-row map
`BuilderInitialCellSelection.cellCoordinate start length coordinate`.
Use one fixed finite graph, independent of every input and branch answer,
on the actual newest register frame `[start, length, coordinate]`.

Compare the actual coordinate with the start. The before-interval branch
must append `[coordinate, 0]`. Otherwise physically construct
`length + length` and compare the recovered coordinate-minus-start
with it. The paired branch must use the verified halving adapter and
physical addition to append
`[start + (coordinate - start) / 2, (coordinate - start) % 2]`.
The after-interval branch must reconstruct `coordinate - length`
by adding start, length and the second comparison residual, then append
offset zero. Both comparisons and every arithmetic operation belong to
the executable graph; none receives a supplied branch certificate.

For every natural start, length and coordinate, arbitrary older ordinary
registers and arbitrary inside/source/output tape data, prove:
`workRunExact? machine (workSteps start length coordinate)
  (initialConfiguration start length coordinate older inside) =
  some (finalConfiguration start length coordinate older inside)`.
The input has the previously derived fresh outer frontier. Prove exact
output and retained scratch, a preserved empty frontier, canonical final
position/offset, compiled raw refinement, fixed-control properties and
encoded-register-span polynomial bounds for the entire three-branch
execution, including all graph bridges.

Prepare generic, zero-width, interval-endpoint, odd/even, retained-tape,
wrong-coordinate rejection and polynomial/control regression contracts
before the first target check. Audit every public theorem after building
the permanent target; reuse unchanged divider and row-loop evidence.
This closes the complete cell-arithmetic machine dependency, not the
source-metadata/history derivation. Connecting the actual source-derived
interval and terminal row suffix, initial/accepting payload production,
full formula emission loop and packaged all-input polynomial reduction
remain required. M230 and its weighted checkpoint remain open; no
publication, evidence-row or proof-score credit is awarded here.

### Verified complete three-branch physical cell decoder

The permanent target
[`CookLevinBuilderInitialCellDecoder`](../../lean/PNP/Concrete/CookLevinBuilderInitialCellDecoder.lean)
now implements the entire canonical within-row position/offset map as one
fixed eleven-node graph. It reads the actual newest
`[start, length, coordinate]` frame and executes both required comparisons;
no runtime value determines its control graph or supplies a branch verdict.

Before the paired interval, the machine appends `[coordinate, 0]`.
Inside the interval, it physically constructs `length + length`,
uses the recovered coordinate-minus-start, invokes the existing halving
adapter, and physically adds start to the quotient. After the interval,
it physically adds start, length and the second comparison's residual.
The resulting last two registers equal
`BuilderInitialCellSelection.cellCoordinate start length coordinate`
for every natural start, length and coordinate, including zero-length
intervals and both endpoints.

The public `workRunExact` theorem proves actual execution of that fixed
graph. `canonical_output` and `final_tape` identify the exact retained
prefix followed by canonical position and offset. The three branch
outputs contain ten, twenty-nine and twenty-three registers respectively;
comparison recovery, expression postorder fields and divider scratch
are all retained explicitly. Arbitrary older ordinary registers and
arbitrary inside/source/output data are preserved. `final_frontier`
proves the fresh outer frontier remains empty, and
`run_compile_exact` proves the exact six-step raw refinement.

The whole-decoder `source_polynomial_bounds` theorem composes the
existing pack, expression, comparison and halving bounds from the
actual incoming encoded register span. It bounds all retained output
and every visited operation, with at most eight graph bridges. The
bound is uniform over all natural register values, not a collection
of fixed cursor cases. `decoded_bounds` retains the original canonical
cell bounds and prefix reconstruction under the existing interval
and in-row hypotheses.

All 47 prepared contracts in
[`PNPConcreteCookLevinBuilderInitialCellDecoder`](../../lean-regression/PNPConcreteCookLevinBuilderInitialCellDecoder.lean)
pass. They cover generic execution and raw refinement, all three
branches, zero-length intervals, start/end equality, odd/even paired
coordinates, exact retained data, rejected wrong output expectations,
source-side tape preservation, canonical bounds, polynomial bounds and
fixed-control properties. All 17 public-theorem axiom audits pass:
six are axiom-free and eleven use only `propext` and `Quot.sound`.
No `Classical.choice` or project-specific assumption enters the closure.

The final permanent-target build, all public axiom probes and complete
prepared regression file reached one terminal successful result.
Earlier syntax and list/graph/polynomial normalization corrections did
not change the machine, theorem claims or expected outputs. Reuse the
exact successful source and regression evidence while documenting this
result; do not repeat the unchanged underlying component builds.

### Next dependency: source-derived decoder frame and history recovery

Connect this decoder to the actual terminal suffix proved by
`BuilderInitialRowLoop.found_suffix`. Recover selected certificate
length and within-row coordinate physically. Derive the interval start
from the source specialization already used by
`BuilderInitialCellSelection.selectedCell`:

```text
certificateStart problem.input.length length.val problem.uniformFuel
```

The original source input length and uniform fuel must be accessed
behind the variable retained row history by a proved machine operation,
or carried forward by an explicitly proved source-preserving handoff.
Do not treat arithmetic knowledge of those values as physical access,
and do not replace their derivation with supplied metadata, a family,
a branch verdict or a correctness certificate.

Initial and accepting payload production, complete formula emission
and recovery/successor wiring, and the packaged all-input polynomial
reduction remain open. M230 is not earned. Formal artefact coverage
remains 205/207; risk-weighted proof estimate remains 35%, with uncertainty
20% to 40%; global gates closed remain 0/5. No fixed checkpoint changed.
PNPLabs publication remains deferred at the coherent M229 source pin.

### Source-metadata carry across complete row selection

Continue the same pinned **Final SAT decision / Accepted package implies
P=NP** reconstruction. The complete cell decoder now exists, but the
original input length and uniform fuel sit behind variable retained row
history. The existing register copier has a fixed program-level offset;
do not pass the runtime history length as a machine-construction parameter.

Implement `CookLevinBuilderInitialRowCarry` as a fixed finite outer
countdown loop on the newest actual frame
`[inputLength, fuel, selectedLength, rowWidth, coordinate, remaining]`.
Reuse `BuilderInitialRowLoop.machine` for one physical row attempt.
A fixed pack physically supplies its literal one-attempt budget. When
that inner machine rejects, copy its computed next length, width and
residual together with the unchanged source fields and decremented
outer budget into the next fixed-size frame. When it accepts, append
the complete current metadata frame as a uniform final suffix.
Decrement the outer budget before preparation, and account for its
exposed blank cell: the next real pack must consume that frontier cell.

Prove exact work/raw execution for every natural row budget and
coordinate, including zero-width rows and exhaustion, while preserving
arbitrary older registers and inside/source/output data. Both source
fields must remain actual copied register values through every loop
iteration. Prove that the accept/reject result equals the canonical
row selection and that a found position yields a newest six-register
suffix with the original input length/fuel, selected length, selected
width, within-row offset and unexamined-row budget. Prove the exact
retained history, an empty final outer frontier, and polynomial bounds
for complete-loop raw time and retained encoded register span.

Prepare all boundary, metadata-preservation, selection/exhaustion,
history/suffix, raw-refinement, control and polynomial regression
contracts before the first target check. Reuse the unchanged single-row
machine and decoder evidence. This is a source-preserving workspace
handoff, not a substitute formula or a supplied correctness certificate.
Physically preparing the initial metadata frame from the source packet,
connecting it to the decoder and complete initial/accepting payloads,
and closing the full formula loop and packaged reduction remain due.
M230 is not earned and no weighted checkpoint or publication row changes.

### Verified complete source-metadata-carrying row loop

The permanent target
[`CookLevinBuilderInitialRowCarry`](../../lean/PNP/Concrete/CookLevinBuilderInitialRowCarry.lean)
now provides one fixed six-node outer loop on the actual newest
`[inputLength, fuel, length, width, coordinate, remaining]` frame.
It uses the existing `BuilderInitialRowLoop.machine` with a physically
packed literal one-attempt budget. The outer count controls every
iteration, while the inner machine computes the real row comparison
and, on failure, the next length, width and residual.

Both source fields are copied from the current physical frame into
each successor frame. No input-dependent history length is passed to
a machine constructor or treated as a static register offset. On a
found row, the program appends a uniform six-register result frame;
on exhaustion, the terminal countdown frame is already present.
The unbounded row-selection result is unchanged.

The public `workRunExact` and `run_compile_exact` theorems establish
exact execution for all natural budgets and coordinates. The
`final_accept_iff` and `final_reject_iff` theorems match canonical
`BuilderInitialLengthSelection.locate`, including zero-width rows
and exhausted families. For a selected position and offset,
`found_suffix` identifies the exact newest frame:

```text
[inputLength, fuel, length + position, width + position,
 offset, remaining - (position + 1)]
```

The remaining field counts unexamined rows. Both original source fields
are retained as actual copied values, not reintroduced as supplied
metadata after the loop. Arbitrary older registers and arbitrary
inside/source/output data are preserved.

The outer budget is decremented before preparation. The real pack
consumes the blank cell exposed by that decrement, and the inner
attempt and carry pack leave a fresh frontier. `final_frontier`
proves the final outer tail is exactly empty on success and exhaustion;
no nonempty tail is silently equated with an empty one. Retained
comparison and carry history is represented explicitly.

For incoming encoded register-span bound `B`,
`source_polynomial_bounds` proves total output span at most
`B + (B + 1) * (30 * B + 38)` and a polynomial bound for complete-loop
raw time. The runtime accounts for every zero test, decrement,
preparation, inner attempt, metadata/result copy and graph bridge.
Only fixed-size newest frames are accessed during each iteration.

All 46 prepared contracts in
[`PNPConcreteCookLevinBuilderInitialRowCarry`](../../lean-regression/PNPConcreteCookLevinBuilderInitialRowCarry.lean)
pass: generic and concrete selection/exhaustion, zero-width cases,
unchanged metadata, exact history and result suffixes, rejected wrong
field expectations, tape/frontier preservation, raw refinement,
control properties and whole-loop polynomial bounds. All 19
public-theorem axiom audits pass: seven are axiom-free, two use only
`propext`, and ten use only `propext` and `Quot.sound`. No
`Classical.choice` or project-specific assumption enters the closure.

The final permanent-target build, public axiom probe and complete
prepared regression file reached terminal success. Earlier
true/false and frame-alias normalization fixes changed no machine,
theorem claim, bound or expected output. Reuse the unchanged successful
source/regression evidence while documenting the result.

### Next dependency: source-packet preparation and decoder handoff

Verify the exact written source-packet addresses for input length,
uniform fuel, certificate limit and row width. Physically construct
the initial metadata frame once, before variable row history exists.
Connect its uniform found suffix to a fixed expression computing
`certificateStart inputLength selectedLength fuel`, then pack and run
the complete three-branch cell decoder. Preserve the actual source,
remaining workspace and exact canonical coordinate interface throughout.

This result does not yet prove that initial source-packet preparation
or decoder integration. Complete initial/accepting payloads, formula
emission and recovery/successor wiring, and the packaged all-input
polynomial reduction remain open. M230 is not earned. Formal artefact
coverage remains 205/207; risk-weighted proof estimate remains 35%,
with uncertainty 20% to 40%; global gates closed remain 0/5.
No fixed checkpoint changed. PNPLabs publication remains deferred at
the coherent M229 source pin.

### Source-derived paired-cell selection and decoder integration

Continue the pinned **Final SAT decision / Accepted package implies P=NP**
reconstruction, closing the dependency from the actual written initial-region
packet to the canonical paired-cell coordinate. The current initial region
contains two fixed state/head constraints, then the paired length constraint;
cell rows therefore start at coordinate three. Preserve that order exactly.

Extend the existing literal source-field interface with a structural address
for the original input-length leaf in both verifier input modes. Read it from
the already materialized polynomial registers, not from a caller-supplied
environment or a second evaluation. Update its source-field regression contract
with the producer. Existing source fields and literal dimensions must not change.

Implement one verifier-dependent finite program that, for every paired-mode
source packet and initial-region coordinate, physically computes the certificate
row budget, packs source input length/fuel/tape width, compares against the
three-constraint prefix, and uses the computed residual for the complete
metadata-carrying row loop. Prefix entries and exhausted row families must
reject this cell branch. A found row must feed an actual register expression for
the certificate interval start and the existing complete cell decoder.

The machine must depend only on the verifier, never on the runtime coordinate,
selected length, history size, or a supplied path/correctness certificate.
Prove exact work/raw execution, source/workspace preservation, a fresh final
frontier, canonical selected length/position/offset, and complete-component
encoded-size polynomial bounds. The paired input-mode premise is the static
branch boundary, not a supplied runtime selection result.

Prepare the new physical execution, prefix/padding rejection, canonical mapping,
raw-refinement, control and polynomial tests with the source. Audit all new public
theorems and the affected source-field interface. Rebuild only the changed target
dependency chain and affected regressions; reuse the unchanged row-loop/decoder
evidence. Complete initial/accepting payloads, full formula-loop wiring and the
packaged reduction remain downstream. M230 is not earned, no fixed progress
checkpoint or publication row changes, and PNPLabs publication stays deferred.

### Verified source-derived paired initial-cell coordinates

The permanent
[`CookLevinBuilderInitialPairedCellSource`](../../lean/PNP/Concrete/CookLevinBuilderInitialPairedCellSource.lean)
target now reads the actual initial-region packet and computes the canonical
paired-cell position and within-cell offset. Its finite nine-node program
depends only on the verifier. No runtime coordinate, selected length, history
size or caller-supplied route answer determines its control.

The existing
[`CookLevinBuilderLiteralArgumentSource`](../../lean/PNP/Concrete/CookLevinBuilderLiteralArgumentSource.lean)
interface now includes the original input length. Its structural address selects
a variable leaf in the already written formula-bound polynomial registers in
both verifier input modes. Existing source fields are unchanged; the source
packet is neither replaced with supplied values nor reevaluated.

For the paired branch, an actual register expression computes the certificate
row budget. A physical pack copies input length, uniform fuel and tape width
together with the initial coordinate and budget. The program compares the
coordinate against three: the initial state, head and length constraints are
not cell rows. It rejects those prefix entries and passes the computed residual
to the complete metadata-carrying row selector.

Every row is selected by the actual finite program. An exhausted family rejects
the cell branch, including canonical paired-cell padding. A found row supplies
its uniform six-register suffix to the interval-start expression and the
complete three-branch physical cell decoder. The final two registers contain
the exact canonical position and within-cell offset. Earlier source metadata
and scratch remain explicitly preserved; arbitrary inside/source/output tape
data is unchanged and the final outer frontier is empty.

The public `workRunExact` and `run_compile_exact` theorems cover every
source packet coordinate under the static paired-mode branch condition.
The execution theorem has no supplied selection, history, or correctness
certificate premise. `found_output` identifies the canonical final pair;
`decoded_bounds` derives its valid tape position and within-cell offset from
the actual tableau geometry. Prefix rejection and exhausted-family rejection
have separate regression contracts.

The component-wide `packet_polynomial_bounds` theorem accounts for the
source-budget expression, metadata pack, prefix comparison, complete row
search, interval-start computation, decoder pack and full decoder execution.
It includes all retained workspace and at most nine outer graph bridges.
`source_polynomial_bounds` binds the result to polynomial encoded-source
input size using the existing source-coordinate invariants. This is not the
global runtime gate or the complete formula-builder theorem.

All 45 prepared contracts in
[`PNPConcreteCookLevinBuilderInitialPairedCellSource`](../../lean-regression/PNPConcreteCookLevinBuilderInitialPairedCellSource.lean)
pass, including exact execution, source-derived metadata, prefix/padding
rejection, wrong-field expectations, canonical output, control, raw refinement
and complete-component bounds. All 26 public theorem axiom audits pass:
six are axiom-free, two use only `propext`, and eighteen use only
`propext` and `Quot.sound`. No `Classical.choice`, project-specific
assumption or incomplete proof enters those closures.

The affected source-field interface separately passed all 58 regressions in
[`PNPConcreteCookLevinBuilderLiteralArgumentSource`](../../lean-regression/PNPConcreteCookLevinBuilderLiteralArgumentSource.lean)
and five selected public axiom audits: one axiom-free and four using only
`propext` and `Quot.sound`. Those successful source hashes were reused by
the final integration run. The source and expected outputs were prepared
together; fixes to graph-field syntax, private helper duplication, structural
addresses and explicit execution-state normalization did not relax a theorem,
bound or test expectation. Both final targeted runs reached terminal success.

### Next dependency: complete initial-constraint payloads

Reconstruct the complete canonical initial family: fixed state/head constraints,
paired length selection, all paired initial cells and the input-only initial
cells. Connect the physically derived position/offset to the exact fixed-bit,
source-bit and certificate-bit literal requests and existing generic payload
machinery. Preserve the selected length and source metadata through the finite
decoder branches wherever the payload handoff requires them; do not turn a
runtime history length into a static register-copy offset.

This coordinate program does not yet emit the complete initial constraints.
The initial payloads, accepting family, formula emission and recovery/successor
wiring, and the packaged all-input polynomial reduction remain open. M230 is
not earned. Formal artefact coverage remains 205/207; risk-weighted proof
estimate remains 35%, with uncertainty 20% to 40%; global gates closed remain
0/5. The root theorem is absent and the publication gate remains false.
No fixed checkpoint changed. PNPLabs publication remains deferred at the
coherent M229 source pin.

### Active complete initial-family payload contract

The next dependency is the canonical payload specification for every initial
coordinate, grounded in the same manuscript SAT-transport anchor and unchanged
formula schedule. Derive source-bit requests from the actual input, both
certificate signs and symbol conclusions from the within-cell offset, and the
selected row/cell from the existing all-coordinate selectors. Preserve the two
initial require constraints, the complete paired length exactly-one list, all
input-only and paired cells, padding and absence.

The intended public boundary is universal:
`BuilderInitialConstraintPayload.values problem coordinate` must equal
`BuilderLocalConstraintPayload.values (problem.initialConstraintSlotDirect coordinate)`
and the encoded payload must decode to that exact slot. The producer uses explicit
register layouts and actual indexed input reads; it must not simply call the
canonical constraint decoder and claim that as a physical construction.

Prepare positive and hostile regression expectations for tags, literal order,
both certificate signs, true/false/absent source reads, both input modes, fixed
prefixes, exhausted families and out-of-range schedule coordinates before the
target build. Audit every public theorem closure and reuse unchanged selector,
source-reader and payload-codec evidence. No existing theorem, fixture,
inventory, progress ledger, workflow or published source pin should change in
this internal component.

This specification is not a physical payload writer. Metadata handoff through
the decoder, runtime request dispatch, actual literal-index construction,
payload packing, accepting constraints and complete formula/reduction wiring
remain downstream obligations. M230 remains open and receives no new checkpoint,
publication row or public-site update from the specification alone.

### Verified complete initial-family payload specification

The permanent
[`CookLevinBuilderInitialConstraintPayload`](../../lean/PNP/Concrete/CookLevinBuilderInitialConstraintPayload.lean)
target now gives the exact logical-register payload for every initial-region
coordinate. `values_canonical` identifies that payload with the unchanged direct
slot, `values_schedule` identifies it with the canonical scheduled initial
constraints, and `decode_values` recovers the exact slot without conflating
absence with padding. These are universal statements, not fixed-coordinate
fixtures or results over supplied constraint lists.

The explicit register layouts cover the state/head require constraints, the
complete paired length exactly-one list, one-premise blank/fixed/source-bit
implications and both two-premise certificate implications. Source requests use
the actual indexed input; the blank/false/true symbol code agrees with the
existing physical indexed reader. A true certificate premise concludes symbol
one, while its negated premise concludes symbol zero. The canonical row and
cell selectors provide the paired coordinates. Input-only cells, exhausted
families and coordinates outside the padded schedule have separate contracts.

All 39 prepared regressions in
[`PNPConcreteCookLevinBuilderInitialConstraintPayload`](../../lean-regression/PNPConcreteCookLevinBuilderInitialConstraintPayload.lean)
pass, including independent hostile literal-order, sign, count and tag checks.
All 22 public theorem axiom audits pass: seven are axiom-free, four use only
`propext`, and eleven use only `propext` and `Quot.sound`. No
`Classical.choice`, project-specific assumption or incomplete proof enters
those closures. The first targeted attempt required source-read and cell-match
normalization repairs; the producer, theorem statements and prepared regression
expectations were unchanged. The final target, audit and regression run reached
terminal success.

### Next dependency: physical initial-payload handoff

Use the complete contract above as the writer's expected output. Preserve the
actual source metadata and selected row through the cell decoder's three finite
exits, with a uniform payload-facing suffix. Any copy offset must come from the
fixed branch layout, never from an unbounded runtime history length. Then connect
physical request dispatch, the existing indexed source reader, literal-index
kernels and canonical payload packers. Reuse the proved all-coordinate selectors
and input-reader execution rather than substituting supplied answers.

The new contract is a semantic specification, not an executable payload writer.
The initial/accepting writers, complete formula emission and recovery/successor
wiring, and packaged all-input polynomial reduction remain open. M230 is not
earned. Formal artefact coverage remains 205/207; risk-weighted proof estimate
remains 35%, with uncertainty 20% to 40%; global gates closed remain 0/5.
The eligible root theorem is absent and the publication gate remains false.
No fixed weighted checkpoint changed. PNPLabs publication remains deferred at
its coherent M229 source pin.

### Active physical cell metadata handoff

The next physical dependency in the unchanged manuscript SAT-transport route is
a uniform writer-facing suffix after the complete cell decoder. Implement one
fixed graph over an actual seven-register input: input length, fuel, selected
length, row width, remaining-row count, interval start and row coordinate.
The program must preserve arbitrary older registers and inside/source/output
tape and append the first five metadata values followed by the canonical
decoded position and within-cell offset.

The existing decoder has three finite return layouts. A branch-aware wrapper
will compare the actual input registers to select the appropriate fixed return
copy layout and reuse the unchanged complete decoder. Its polynomial bound must
charge these routing comparisons, every copy, the full decoder and all graph
bridges. It must not use a runtime history length as a static program parameter
or accept a supplied branch/coordinate answer as an execution premise.

Prepare all three branch-boundary and metadata-order regressions with the
source. The intended universal interfaces are exact work/raw execution, the
uniform seven-register canonical suffix, fresh-frontier and workspace
preservation, deterministic control and whole-wrapper bounds from the actual
encoded incoming register span. Audit every public theorem; reuse the unchanged
decoder, comparison and packer evidence.

Connecting the actual source-row preparation to this handoff and then dispatching
the complete initial-family payload writer remains explicit downstream work.
The wrapper alone earns no checkpoint, publication row or M230 completion claim.
No existing decoder, canonical formula, progress ledger or published source pin
is to be changed by this component.

### Verified physical cell metadata handoff

The permanent
[`CookLevinBuilderInitialCellHandoff`](../../lean/PNP/Concrete/CookLevinBuilderInitialCellHandoff.lean)
target now provides one fixed fourteen-node program for all metadata values,
interval starts, certificate lengths and row coordinates. Its actual incoming
seven registers hold input length, fuel, selected length, row width,
remaining-row count, interval start and row coordinate.

The graph compares the actual coordinate against the interval start and upper
boundary to select one of three fixed return layouts. It physically prepares the
decoder's arguments, runs the unchanged complete decoder, and copies the five
metadata registers followed by the canonical position and within-cell offset.
Every successful return has the same seven-register suffix. There is no
caller-supplied branch answer or runtime-sized static register offset.

The exact work/raw execution theorems preserve arbitrary older registers and
inside/source/output tape and leave a fresh outer frontier. The complete wrapper
bound includes its routing comparisons, argument and result copies, the full
decoder and at most eight outer graph bridges. Reusing the decoder does not
hide that additional runtime. The bound is in the actual encoded incoming
register span, not an uncharged semantic reference computation.

All 53 prepared regressions in
[`PNPConcreteCookLevinBuilderInitialCellHandoff`](../../lean-regression/PNPConcreteCookLevinBuilderInitialCellHandoff.lean)
pass, including both interval boundaries, zero certificate length, all three
fixed copy layouts, metadata order, wrong-field/offset expectations, complete
work/raw execution and the whole-wrapper polynomial bound. All 21 public theorem
axiom audits pass: four are axiom-free, seven use only `propext`, and ten
use only `propext` and `Quot.sound`. No `Classical.choice`,
project-specific assumption or incomplete proof enters those closures.

The initial targeted attempts exposed association and alias normalization
mismatches at tape and bound handoffs. Explicit proof normalization repaired
them without changing the machine, theorem statements, bound polynomials or
prepared regression expectations. The final target, audit and regression run
reached terminal success. The existing decoder source and its successful
verification evidence were unchanged and reused.

### Next dependency: source-bound uniform initial-cell frame

Connect the actual source-row preparation to the verified metadata handoff.
The existing row result supplies input length, fuel, selected length, expanded
row width and remaining-row count; preserve those actual fields alongside the
computed interval start and row coordinate. Prove the complete source-packet
run leaves the uniform seven-register payload-facing suffix, including prefix
and exhausted-family routing, and bind its resource bound to encoded source
input size. Then wire physical request dispatch, indexed source reads, literal
kernels and the complete initial payload specification.

The physical initial/accepting writers and complete formula/reduction wiring
remain open. M230 is not earned. Formal artefact coverage remains 205/207;
risk-weighted proof estimate remains 35%, with uncertainty 20% to 40%;
global gates closed remain 0/5. The eligible root theorem is absent and the
publication gate remains false. No fixed checkpoint changed. PNPLabs
publication remains deferred at its coherent M229 source pin.

### Active source-bound metadata-handoff contract

Continue the same manuscript-anchored M230 complete-builder dependency above.
Integrate the verified cell handoff into the existing
`BuilderInitialPairedCellSource` producer. Its first seven outer stages already
derive the source metadata, reject the three non-cell prefix coordinates, select
the actual row, and compute the interval start. Upgrade the last argument pack
and decoder stage together; do not introduce a second source-machine variant.

The actual fifteen-register row/start frame must supply fields
`[0, 1, 2, 3, 5, 14, 4]`: input length, fuel, selected length, expanded row width,
remaining-row count, interval start and local row offset. One fixed nine-node
outer graph, depending only on the verifier, must run the complete handoff and
leave a uniform suffix containing the first five metadata fields and the
canonical position/within-cell pair. Prove that the remaining count is the
certificate limit minus selected length, and that the selected length recovers
the certificate limit together with that count.

The exact `workRunExact` and `run_compile_exact` statements retain only the
paired-mode execution premise, not a supplied selection or branch answer.
`final_uniform_suffix` must cover every computed result; prefix and exhausted
cell-family paths remain rejecting. Upgrade `packet_polynomial_bounds` and
`source_polynomial_bounds` to charge the new seven-field pack, complete metadata
handoff and every outer bridge, with the final bound in encoded source input
size under the existing genuine source-coordinate invariants.

Consumer review found only the dedicated paired-cell regression and this plan;
no root, inventory, generated status or workflow consumer imports this pending
component. Update the producer, complete expected output layout, positive and
wrong-field cases, universal suffix and axiom-name probes in one patch before
compilation. Rebuild the changed permanent source target and run its prepared
regressions and public axiom audits. Reuse the unchanged decoder, row carry and
standalone handoff evidence; no complete proof suite or site audit is warranted
for this internal component. Full M230 release audits remain due at integration.

Physical request dispatch, indexed source reads, literal kernels, complete
initial/accepting writers and formula/reduction wiring remain downstream.
M230 is not earned; no progress checkpoint or publication value changes.

### Verified source-bound cell metadata handoff

The existing
[`CookLevinBuilderInitialPairedCellSource`](../../lean/PNP/Concrete/CookLevinBuilderInitialPairedCellSource.lean)
target now integrates the complete metadata-preserving handoff. Its first seven
outer stages are unchanged; the final physical pack reads the seven reviewed
fields from the actual fifteen-register row/start frame, and the final node runs
the verified handoff. The outer graph still has nine nodes and depends only on
the verifier, not on any runtime length, position, history size or branch answer.

Every successful source-packet run leaves the uniform writer-facing suffix:
input length, fuel, selected certificate length, expanded row width, remaining
length count, canonical cell position and within-cell offset. The remaining
count is the certificate limit minus selected length; for every selected length,
adding the two recovers the actual certificate limit. No replacement source
metadata, preselected row or supplied decoder answer is an execution premise.

The complete work/raw run still covers the three rejected non-cell prefix
coordinates, exhausted cell-family routing and all successful source-selected
rows. The exact final-tape and fresh-frontier results are preserved. The revised
packet and encoded-source polynomial theorems charge the seven-field copy, all
handoff routing and decoder work, retained history and the nine outer bridges.
The source-size theorem uses the existing genuine body, cursor-balance and
region invariants; it does not assume a polynomial bound for an unimplemented
reference construction.

All 52 prepared regressions in
[`PNPConcreteCookLevinBuilderInitialPairedCellSource`](../../lean-regression/PNPConcreteCookLevinBuilderInitialPairedCellSource.lean)
pass, including the updated complete output layout, wrong-field rejection,
actual metadata recovery, universal suffix, complete execution and source-size
bound. All 33 public theorem axiom audits pass: six are axiom-free, eight use
only `propext`, and nineteen use only `propext` and `Quot.sound`.
No `Classical.choice`, project-specific assumption or incomplete proof enters
those closures. The first targeted run reached terminal success with the
producer and revised regression expectations prepared together.

Only the changed source-machine target and its consumers were checked.
The unchanged standalone handoff, decoder and upstream row infrastructure were
reused; their independent targeted suites were not repeated. Earlier evidence
records describe the previous coordinate-only return layout, while this result
establishes the current metadata-preserving source integration.

### Next dependency: physical initial-cell request dispatch

Use the actual seven-register suffix to implement the complete paired initial
cell request classifier: blank cells, fixed bits, source-bit requests and
certificate-bit requests. Preserve the necessary source metadata and canonical
position/within-cell coordinate while deriving each request and its index by
physical comparisons and arithmetic. Then connect the indexed source reader,
literal-index kernels and canonical initial payload packers. The complete
initial/accepting writers and formula/reduction wiring remain open.

M230 is not earned. Formal artefact coverage remains 205/207; risk-weighted
proof estimate remains 35%, with uncertainty 20% to 40%; global gates closed
remain 0/5. The eligible root theorem is absent and the publication gate remains
false. No fixed checkpoint changed. PNPLabs publication remains deferred at its
coherent M229 source pin.

### Active complete paired-cell request-dispatch contract

Continue the same M230 manuscript-to-concrete-Cook-Levin dependency. Implement
one fixed physical dispatcher for the unchanged `pairedRequest` encoding, not
another finite position fixture or a semantic classifier standing in for a
machine. Its input is the verified seven-register metadata/cell frame.

The actual comparisons walk widths `[fuel, inputLength, 1, inputLength,
selectedLength, 1, selectedLength]`. On a miss, the existing compare/residual
primitive must derive the remaining offset and physically carry it to the next
segment. On a hit, emit blank, fixed true, fixed false, source index or
certificate index as appropriate. Empty input or certificate segments have
zero width and must be skipped correctly; both zero-length delimiter cells
remain present. The static table has seven entries for every source input.

The output suffix must contain all seven original metadata/cell fields followed
by a request kind and argument: blank `[0,0]`, fixed bit `[1,bit]`, source
request `[2,index]`, or certificate request `[3,index]`. A source request is
an index for the existing indexed reader, never a supplied source bit. Preserve
arbitrary older registers and inside/source/output data and leave a fresh outer
frontier. Prove exact work and compiled raw execution without supplied branch,
route or lookup premises, and prove the request equals the canonical paired
request for every position and selected certificate length.

Compile the fixed table through nested finite branch graphs. Prove execution
and bounds structurally over that static table, with physical copies and every
branch bridge charged. The complete incoming encoded-register-span bound must
also cover retained history and the final nine-field request suffix. Do not
present this bound as a source-packet binding before the source integration is
actually proved.

Prepare the source, all field-order and encoding-boundary expectations,
zero-length cases, universal canonical/execution statements, and public axiom
probe set together. Run only the new permanent target and its dedicated
regressions/axiom audit, then source-bound documentation checks. Reuse the
unchanged comparison, metadata handoff and source-row evidence; full root,
inventory, publication and exact-merge audits remain due at M230 integration.

Then connect the dispatcher to the actual source machine, indexed input reader,
literal kernels and canonical payload packers. Complete initial/accepting
writers and the full formula/reduction loop remain open. M230 is not earned;
no fixed checkpoint, progress value or PNPLabs publication changes.

### Verified complete physical paired-cell request dispatch

The permanent
[`CookLevinBuilderInitialPairedRequest`](../../lean/PNP/Concrete/CookLevinBuilderInitialPairedRequest.lean)
target now implements the complete paired-cell request dispatcher. One fixed
seven-entry table covers the leading blank region, input unary prefix,
delimiter, actual source indices, certificate-length unary prefix, delimiter
and certificate indices, followed by the trailing blank region. Zero-width
segments are skipped while the two delimiter cells remain present.

The program physically compares the current residual offset with the next
segment width. A miss copies the derived remainder and all seven original
metadata/cell fields into the next stage. A hit copies those original fields
followed by the request kind and argument. Every return has a uniform
nine-register suffix: blank `[0,0]`, fixed bit `[1,bit]`, source index
`[2,index]`, or certificate index `[3,index]`. A source index is not a
supplied input bit.

The exact work/raw execution proof is structural over the static segment table.
No runtime input, certificate length, coordinate, route answer or history size
constructs the program. All requests agree with the unchanged canonical
`pairedRequest` for every position and selected length; certificate request
indices satisfy the required finite width. Arbitrary older registers and
inside/source/output tape are preserved, and the outer frontier is fresh.

The complete polynomial bound charges every comparison, metadata/result copy,
retained register and nested graph bridge. It bounds the actual encoded incoming
register span and the final nine-field suffix. Binding that input span to the
full source packet belongs to the next integration; no complete source-to-reader
or initial-payload run is claimed by this standalone dispatcher.

All 66 prepared regressions in
[`PNPConcreteCookLevinBuilderInitialPairedRequest`](../../lean-regression/PNPConcreteCookLevinBuilderInitialPairedRequest.lean)
pass. They cover every segment boundary, empty input, zero certificate length,
both zero-length delimiters, residual rather than absolute indices, wrong-field
rejection, metadata retention, universal canonical/execution statements and
polynomial bounds. All 26 public theorem axiom audits pass: nine are axiom-free,
six use only `propext`, and eleven use only `propext` and `Quot.sound`.
No `Classical.choice`, project-specific assumption or incomplete proof enters
those closures.

The earlier targeted attempts exposed proof-script record layout, an explicit
suffix witness, Boolean/subtraction normalization and outer-graph inference.
The repairs changed no machine, bound polynomial, theorem obligation or prepared
regression result. The final permanent target, audit and regression run reached
terminal success. Existing comparison and handoff sources and their independent
successful suites were unchanged and reused.

### Next dependency: source-to-request and physical payload wiring

Connect the verified source machine's uniform seven-field cell result to this
complete dispatcher. Prove the full actual source-packet run leaves the canonical
nine-field request suffix and charge the new stage in its encoded-source
polynomial bound. Then bind source requests to the existing indexed reader and
connect literal kernels and canonical payload packers. Complete initial/accepting
writers and the full formula/reduction loop remain open.

M230 is not earned. Formal artefact coverage remains 205/207; risk-weighted
proof estimate remains 35%, with uncertainty 20% to 40%; global gates closed
remain 0/5. The eligible root theorem is absent and the publication gate remains
false. No fixed checkpoint changed. PNPLabs publication remains deferred at its
coherent M229 source pin.

### Active source-to-request integration contract

The next dependency edge under the same **Final SAT decision** /
**Accepted package implies P=NP** legacy anchor is the complete physical
source packet to canonical paired-cell request. Upgrade the existing
`BuilderInitialPairedCellSource` in place; do not introduce a parallel source
machine or substitute a supplied route answer.

Append the verified fixed request dispatcher to the actual metadata handoff.
The ten-node source program must derive every successful request from the
source-selected row and cell. The seven-field handoff frame remains an
intermediate interface, while the final nine-field frame adds the request kind
and argument. Rejected prefix constraints and exhausted cell-family positions
remain distinct from successful blank, fixed-bit, source-index and
certificate-index requests.

Required theorem boundary: for every paired problem, body index, remainder and
inside tape, `workRunExact` and `run_compile_exact` execute that complete
physical chain. No length, branch, request or correct output is supplied.
`final_uniform_suffix` must describe all nine fields; `found_canonical_suffix`
must identify the unchanged canonical `pairedRequest` for every selected
length and offset. Certificate request indices must remain below the original
source certificate limit.

The packet and encoded-source polynomial bounds must include the dispatcher,
its retained history and the tenth outer bridge. Obtain its input bound from
the actual handoff output rather than a new independent size premise. Preserve
the genuine source body, cursor-balance and selected-region invariants.

Consumer audit: the source module is consumed only by its dedicated regression
and this plan. Update graph size/transitions, complete output layout, final
suffix, request interpretation and polynomial execution expectations together.
Keep the intermediate seven-field metadata tests; add a negative test that
distinguishes that frame from the final request frame. The prepared contract has
64 regressions and 38 public theorem axiom probes. Rebuild only the changed
source-machine target and its consumers; reuse the exact verified dispatcher,
handoff, decoder and row primitives without repeating their independent suites.

After this boundary passes, connect actual indexed source reads and canonical
literal/payload writing, then finish the initial and accepting families and the
complete formula/reduction loop. M230 remains unearned. No new checkpoint,
publication row or progress credit is assigned. PNPLabs remains deferred.

### Verified source-bound canonical request execution

The existing
[`CookLevinBuilderInitialPairedCellSource`](../../lean/PNP/Concrete/CookLevinBuilderInitialPairedCellSource.lean)
target now runs the complete paired request dispatcher after its actual
metadata-preserving cell handoff. This is one ten-node source program, not a
second source-machine variant. Neither a branch answer nor a request kind,
index, source bit or history length is supplied to its execution theorem.

Every successful source-packet run has a uniform nine-field suffix: input
length, fuel, selected certificate length, row width, remaining lengths,
decoded cell position, within-cell offset, request kind and request argument.
The intermediate seven-field metadata frame is still present and separately
specified. The two additional fields are physically computed through the
verified seven-segment dispatcher, not appended as semantic advice.

The final request agrees with the unchanged canonical `pairedRequest` for
every selected certificate length and cell coordinate. Certificate request
indices are below the original source certificate limit. The source machine
still rejects the three non-cell prefix constraints and exhausted paired-cell
family coordinates; those are downstream writer branches rather than
successful requests manufactured by this component.

The exact work and compiled raw runs now include source extraction, row
selection, cell decoding, metadata handoff and request dispatch. The complete
source-size polynomial bounds charge the new dispatcher, all retained
workspace and every one of the ten outer graph bridges. The dispatcher input
bound is derived from the actual handoff output under the unchanged source
body, cursor-balance and region invariants.

All 64 prepared regressions in
[`PNPConcreteCookLevinBuilderInitialPairedCellSource`](../../lean-regression/PNPConcreteCookLevinBuilderInitialPairedCellSource.lean)
pass, including complete output layout, physical dispatch transitions,
canonical request meaning, certificate-index safety, the distinction between
intermediate and final frames, universal execution and source-size bounds.
All 38 public theorem axiom audits pass: eight are axiom-free, eight use only
`propext`, and twenty-two use only `propext` and `Quot.sound`. No
`Classical.choice`, project-specific assumption or incomplete proof enters
those closures. The first targeted run reached terminal success.

The source producer, graph/output expectations, new regression boundaries and
axiom-name probe were prepared together. Only the changed source target and its
consumers were rerun. The byte-identical request dispatcher, handoff, decoder
and upstream row evidence were reused; documentation did not trigger a second
Lean build.

### Next dependency: indexed request resolution and canonical payload writing

Resolve source-index requests with the existing physical indexed reader; do
not provide a bit as a premise. Feed the actual metadata/request fields into
the literal kernels and unchanged canonical payload packers. Complete
initial-prefix, initial input-only, paired-family and accepting writers, then
connect formula emission, recovery/successor wiring and the packaged all-input
polynomial reduction.

M230 is not earned. Formal artefact coverage remains 205/207; risk-weighted
proof estimate remains 35%, with uncertainty 20% to 40%; global gates closed
remain 0/5. The eligible root theorem is absent and the publication gate remains
false. No fixed checkpoint changed. PNPLabs publication remains deferred at its
coherent M229 source pin.

### Active actual-input request resolution and source binding

Under the same **Final SAT decision** / **Accepted package implies P=NP**
legacy anchor, close the source-request-to-symbol edge required by the
canonical initial-family writer. A source request must read the actual input
tape, not accept a bit or a supplied semantic answer.

Reuse the existing non-destructive `BuilderUnaryTagMatch` for fixed request
tags and the verified `BuilderIndexedInputRead` for the source branch only.
One fixed resolver must preserve the nine request fields and append the
canonical symbol code: blank 0, false 1, true 2. Certificate offset zero uses
the positive/one conclusion; offset one uses the negative/zero conclusion.
The generic component covers every typed request and natural offset, while
the source selection supplies the canonical within-cell bounds.

Derive exact work and compiled raw runs on the actual `inside input output`
tape, including arbitrary prior output. Restore all source marks and registers;
do not scan into the tally or prior output after the source terminator.
Charge all tag tests, copies, the actual indexed scan, retained history and
outer bridges in one encoded-register polynomial bound. Derive index and older
workspace bounds from the materialized input frame.

Then compose the unchanged verified `BuilderInitialPairedCellSource` with
this resolver in a source-bound resolution stage. This reuses the existing
source machine; it is not a duplicate source extractor or alternative route.
The complete source-bound theorem must construct the request from the selected
row and decoded cell, match its actual nine-field suffix, resolve the source
bit physically and return ten source-derived fields. No request, bit, branch
answer or independent size certificate belongs to that source-level theorem.
Keep source-prefix and exhausted-family rejection unchanged.

Prepare the resolver's 46 regressions and 32 public axiom probes with its
source. After that targeted boundary passes, reuse its exact evidence during
source composition; do not repeat the independent reader, tag matcher, request
dispatcher or source-selection suites. Add the source-composition execution,
layout, rejection, canonical symbol and encoded-source bounds tests before
building that target. Commit the integrated boundary only after both stages
and the current documentation/status/diff checks pass.

Literal kernels, canonical payload packing, the complete initial and accepting
families, formula-loop wiring and the packaged polynomial reduction remain
downstream. M230 is not earned; no checkpoint, publication row or progress
credit is awarded. PNPLabs publication remains deferred.

### Prepared source-to-resolution integration contract

The resolver now has successful exact-target, regression and compiled axiom
evidence. Preserve those verified bytes while adding the two-node composition:
the unchanged source machine physically creates the nine-field request, and
the resolver appends its canonical symbol using the actual source input.

Prepare 43 source-composition regressions and 26 exact public axiom probes before
building. Check the actual source tape, arbitrary prior output, nine-to-ten-field
boundary, computed source history, canonical request derivation, complete exact
work/raw runs, prefix and exhaustion rejection, fixed graph transitions, all
symbol branches, and both packet and encoded-source polynomial bounds.
Reuse the unchanged resolver and source-selection suites. The next required
construction is the canonical literal/payload writer; M230 remains unearned.

### Verified source-to-symbol request resolution

The fixed
[`CookLevinBuilderInitialRequestResolution`](../../lean/PNP/Concrete/CookLevinBuilderInitialRequestResolution.lean)
program now resolves every typed initial-cell request physically. Its thirteen
fixed graph nodes preserve all nine request fields and append the canonical
symbol code: blank 0, false 1 or true 2. The source branch uses the actual indexed
input reader, including out-of-range blank behavior; no source bit is supplied.
Certificate offset zero and offset one retain their distinct conclusions.
Both the source tape and arbitrary prior output are restored.

The new
[`CookLevinBuilderInitialPairedCellResolution`](../../lean/PNP/Concrete/CookLevinBuilderInitialPairedCellResolution.lean)
is a two-node composition of the unchanged verified source machine and that
resolver. Its execution theorem has no supplied request, bit, history, branch
answer or independent size certificate. The computable history cut is justified
by the source machine's actual canonical nine-field suffix. Every successful
cell selection now ends with the ten source-derived request-and-symbol fields.
The existing non-cell prefix and exhausted-family branches still reject; this
component does not pretend they are completed writer cases.

Exact work and compiled raw execution theorems cover the complete source-to-read
chain. Register-size bounds include all retained history, tag tests, field
copies, indexed input scanning and both composition bridges. The encoded-source
bound derives the initial packet size under the unchanged paired-mode, body,
cursor-balance and selected-region invariants.

All 46 resolver regressions in
[`PNPConcreteCookLevinBuilderInitialRequestResolution`](../../lean-regression/PNPConcreteCookLevinBuilderInitialRequestResolution.lean)
and all 43 composition regressions in
[`PNPConcreteCookLevinBuilderInitialPairedCellResolution`](../../lean-regression/PNPConcreteCookLevinBuilderInitialPairedCellResolution.lean)
pass. The resolver's 32 public axiom probes comprise four axiom-free theorems,
ten using only `propext`, and eighteen using only `propext` and `Quot.sound`.
The composition's 26 probes comprise one using only `propext` and twenty-five
using only `propext` and `Quot.sound`. None uses `Classical.choice`, a
project-specific axiom or an incomplete proof.

Earlier failed attempts exposed proof normalization, one reserved identifier
and unnecessary whole-machine unfolding in endpoint comparisons. The repairs
changed proof terms only, not the machine, theorem statements, polynomial
budgets or prepared regression expectations. Successful terminal target,
axiom and regression runs supply the evidence; failed attempts do not.

The complete expectation sets were prepared before their target builds.
Composition reused the byte-identical resolver and source-selection evidence;
the independent reader, tag matcher, dispatcher, handoff and row suites were
not rerun. Documentation/status verification reuses both successful source
hashes rather than rebuilding Lean.

### Next dependency: canonical initial-cell literal and payload writing

Use the ten actually materialized fields to construct the length, symbol and
certificate-bit literal indices with the existing arithmetic kernels. Pack the
unchanged canonical guarded and bit-guarded initial-cell payloads, retaining
the distinct certificate signs. Derive all dimensions and indices from the
source packet; do not supply semantic answers or correctness certificates.
Then finish initial-prefix, input-only, paired-family and accepting writers,
formula-loop emission/recovery and the packaged all-input polynomial reduction.

M230 is not earned. Formal artefact coverage remains 205/207; risk-weighted
proof estimate remains 35%, with uncertainty 20% to 40%; global gates closed
remain 0/5. The eligible root theorem is absent and the publication gate remains
false. No fixed checkpoint changed. PNPLabs publication remains deferred at its
coherent M229 source pin.

### Active canonical paired-cell literal and payload construction

Continue the **Final SAT decision** / **Accepted package implies P=NP**
dependency: construct the exact initial-cell constraint from the source-derived
request-and-symbol fields, then expose it to the complete formula emitter.

The input is the actual ten-register resolution suffix. Recover the original
certificate bound as selected length plus remaining lengths; derive time count
as fuel plus one and the paired global tape width from input length, certificate
bound and fuel. The selected row's slot count is not that global tape width.
The fixed verifier supplies only its source-independent raw-machine state bound.

Specialize the existing canonical literal-expression syntax by structural
expression substitution over those ten fields. Prove substitution preserves
evaluation; do not introduce alternative variable numbering. Compute length,
symbol and certificate-bit indices with the existing physical expression
compiler, charging scratch, field copies, arithmetic and every graph bridge.
A noncertificate branch may compute an unused natural bit index, but only the
certificate branch may claim a bounded certificate-bit literal.

Use physical kind and offset tests to write the existing guarded payload
`[lengthIndex, 1, symbolIndex, 1, 1, 3]` or bit-guarded payload
`[bitIndex, sign, lengthIndex, 1, symbolIndex, 1, 2, 3]`.
Preserve positive/negative certificate signs and their distinct symbols.

The generic exact execution theorem covers every written numeric frame;
the source-level theorem must compose the unchanged source-resolution machine
and derive its frame, request, symbol and size bounds itself. For each selected
cell, prove that the final suffix is the exact payload returned by the unchanged
`BuilderInitialConstraintPayload.pairedCellValues`. Obtain the one/two-slot
offset bound from the canonical selection theorem. No dimension environment,
input bit, literal index, constraint, history or correctness certificate may be
supplied to the source-level theorem. Preserve prefix/exhaustion rejection.

Prepare exact layout, canonical-index, source-binding, branch/sign, execution,
polynomial-size/runtime and negative regressions with the source before each
targeted build. Probe every added public theorem's compiled axiom closure.
Reuse unchanged resolution and upstream evidence. Commit the integrated
source-to-payload boundary after both stages and documentation/status checks,
not merely a standalone literal evaluator.

Complete initial-prefix, input-only and accepting families, formula-loop
emission/recovery, and the packaged all-input reduction remain downstream.
M230 is not earned and no fixed checkpoint or publication row is awarded.
PNPLabs publication remains deferred at the coherent M229 coordinate.

Prepared literal-stage expectations: 54 focused regressions and 31 public
compiled-axiom probes. These cover numeric layouts, both signs, source symbol
resolution, unchanged canonical indices, exact physical execution and complete
encoded-size bounds. The following source-composition stage has its own contract;
no literal-only result is an integrated source-to-payload milestone.

### Prepared source-to-payload integration

The added source stage composes the existing source resolver with the literal
writer in a fixed two-node graph. Its input is the original source packet,
actual source bits and prior output; its run accepts exactly a selected cell
and preserves prefix/exhaustion rejection. The ten-field frame and history cut
are derived from the actual resolver result.

The theorem `BuilderInitialPairedCellPayload.source_canonical_payload` must
connect exact physical execution directly to the unchanged canonical
`pairedCellValues`. Position and request-offset bounds come from the source
selection theorem, not an added correctness premise. Packet and actual
encoded-input polynomial theorems must charge both stages, retained scratch
and every outer join.

Prepared expectations: 39 composition regressions and 25 public compiled-axiom
probes, in addition to the literal writer's 54 regressions and 31 probes.
The next commit must include both stages after their exact contracts pass.
No standalone stage is a published milestone; the initial-prefix, input-only
and accepting families, complete emission/recovery loop and packaged
all-input reduction remain required for M230.

### Verified source-derived canonical paired-cell payloads

The fixed
[`CookLevinBuilderInitialPairedLiteralPayload`](../../lean/PNP/Concrete/CookLevinBuilderInitialPairedLiteralPayload.lean)
program now physically builds canonical literal indices and writes the complete
initial-cell payload from the ten resolution registers. The original certificate
bound is recovered as selected length plus remaining lengths, time count is fuel
plus one, and global tape width comes from the unchanged paired-layout formula.
The row's slot count is not substituted for global tape width. Structural
expression substitution preserves the existing literal kernel's numbering.

Three compiled expressions compute the length, symbol and certificate-bit
indices. Fixed tag/offset tests select the ordinary guarded or signed
bit-guarded payload. The two certificate branches preserve both their distinct
signs and symbols. The generic numeric frame theorem does not claim that every
numeric frame denotes a valid literal: canonical index and payload theorems
separately establish that meaning for source-derived requests.

The new
[`CookLevinBuilderInitialPairedCellPayload`](../../lean/PNP/Concrete/CookLevinBuilderInitialPairedCellPayload.lean)
composes actual source selection and symbol resolution with that writer.
Its `source_canonical_payload` theorem ties the exact physical run directly to
the unchanged `BuilderInitialConstraintPayload.pairedCellValues`.
The bounded position and one/two-slot offset come from actual source selection.
No source bit, dimension environment, literal index, payload, history or
correctness certificate is supplied to the execution theorem.

The source tape and arbitrary prior output are preserved. Non-cell prefix and
exhausted-family cases still reject at this component boundary. Exact work and
compiled raw execution theorems cover the whole source-to-payload chain.
Polynomial bounds charge source selection, actual reads, all arithmetic and
retained scratch, payload copies, tag scans and every composition bridge.
The actual encoded-input bound uses the unchanged body, cursor-balance,
paired-mode and selected-region invariants.

All 54 literal-writer regressions in
[`PNPConcreteCookLevinBuilderInitialPairedLiteralPayload`](../../lean-regression/PNPConcreteCookLevinBuilderInitialPairedLiteralPayload.lean)
and all 39 source-composition regressions in
[`PNPConcreteCookLevinBuilderInitialPairedCellPayload`](../../lean-regression/PNPConcreteCookLevinBuilderInitialPairedCellPayload.lean)
pass. The 31 literal-writer axiom probes comprise two axiom-free theorems,
five using only `propext`, and twenty-four using only `propext` and `Quot.sound`.
The composition's 25 probes comprise one using only `propext` and twenty-four
using only `propext` and `Quot.sound`. No new theorem depends on
`Classical.choice`, a project-specific axiom or an incomplete proof.

The prepared contracts caught syntax, explicit layout typing and register-list
normalization issues. An independent empty-input numeric fixture initially
omitted the head-variable block: the unchanged canonical formula gives
`1*3*3 + 1*3 + 1*0 = 12`, not 9. Its expected value was corrected from that
formula without changing proof code. The final fixture run reused the separately
completed exact-source build and axiom commands after checking their identities;
the failed wrapper was not treated as a successful run. The composed stage
then passed its complete target, axiom and regression run.

All source-to-symbol and upstream evidence remained byte-identical and was
reused. Documentation/status checks do not rebuild Lean. Full root, inventory,
publication, CI and exact-merge verification remain due at complete M230
integration.

### Next dependency: complete initial families and formula emission

Finish the variable-length certificate-length choice and required head/state
prefix, the input-only initial cells and accepting family. Connect those
canonical payloads to the full schedule emitter, erase/recover retained scratch,
prove exact complete encoded-formula output, and package the uniformly
polynomial all-input reduction. Do not replace these obligations with another
fixed instance or a supplied semantic answer.

M230 is not earned. Formal artefact coverage remains 205/207; risk-weighted
proof estimate remains 35%, with uncertainty 20% to 40%; global gates closed
remain 0/5. The eligible root theorem is absent and the publication gate remains
false. No fixed checkpoint changed. PNPLabs publication remains deferred at its
coherent M229 source pin.

### Active arbitrary-width certificate-length clause

Continue the **Final SAT decision** / **Accepted package implies P=NP**
dependency by physically constructing the complete initial exactly-one clause
over every possible certificate length. This is an arbitrary-width family,
including certificate bound zero, not another fixed list or schedule fixture.

Reuse the existing source-to-literal machine with its fixed zero-coordinate
certificate-length plan. It physically derives the canonical length-block base
from the actual initial-region source packet. Read the certificate width from
the written dimension fields, compute `count = C + 1` and the exclusive
`upper = base + count`, and feed those actual registers into the existing
complete exactly-one payload machine. Reuse its range loop, payload tag and
runtime theorem; do not rebuild control from a runtime count or supply an
index list.

The required source theorem must prove one exact physical run from the original
source/radix packet to a suffix equal to
`BuilderInitialConstraintPayload.lengthValues`. Prove the descending range is
exactly the reversed canonical `pairedLengthVariables` map. Source bits, prior
output and any tracked exterior are preserved according to the existing tape
contract. In particular, keep and charge the exactly-one writer's remaining
blank exterior rather than silently identifying it with an empty list.

No base, count, upper bound, list, branch answer or correctness certificate may
be supplied to the source-level run. The fixed verifier and source packet must
derive them. Bounds must include source field copies, canonical literal
arithmetic, count/upper arithmetic, retained history, variable-length payload,
blank exterior and every composition bridge, uniformly in encoded input size.

Prepare canonical-range, zero-width, order/tag, physical execution, source
binding, polynomial-size/runtime, control-safety and negative regressions before
the targeted build. Probe every new public theorem's compiled axiom closure.
Reuse exact unchanged source-to-literal, range, exactly-one and paired-cell
evidence; do not repeat their full suites. Commit only after the complete
source-bound clause and its documentation/status checks pass.

This does not yet select all initial branches or emit the whole formula.
Required head/state prefix, input-only initial cells, accepting-family payloads,
complete dispatch/emission/recovery and the packaged all-input reduction remain
open. M230 remains unearned; no fixed checkpoint, publication row, public source
pin or PNPLabs release changes at this component boundary.

### Verified source-derived arbitrary-width certificate-length clause

The [source-bound length writer](../../lean/PNP/Concrete/CookLevinBuilderInitialLengthPayload.lean)
now physically constructs the complete initial certificate-length exactly-one
payload. Its machine is fixed by the verifier: the source packet supplies the
actual dimension fields, the existing literal kernel computes the canonical
length-block base, fixed arithmetic derives the count and exclusive upper bound,
and the existing range/payload loop writes every required variable and tag.

The universal result covers every certificate width, including zero. The
descending list is proved equal to the reversed canonical
`pairedLengthVariables` map, and the resulting payload decodes to the existing
initial constraint at coordinate two. This coordinate identifies one complete
unbounded family, not a new fixed-slot milestone. No caller supplies the base,
count, upper bound, variable list, input bits, result or correctness certificate.

The exact work-machine run and raw compilation theorem start from the actual
source/radix packet and preserve the original input and prior output. The
encoded-input-size polynomial theorem charges the source-to-literal work,
field copies, arithmetic, retained scratch, entire variable-length payload,
all three graph bridges and the remaining blank exterior. The exterior is
explicit in the endpoint and size bound; it is not assumed empty.

All 42 [length-writer regressions](../../lean-regression/PNPConcreteCookLevinBuilderInitialLengthPayload.lean)
passed, including canonical numbering, zero-width, order/tag negatives,
physical source binding, decoder equality, control safety and polynomial
bounds. All 29 public theorem axiom probes passed: one is axiom-free, two use
only `propext`, and 26 use only `propext` and `Quot.sound`. None uses
classical choice or project-specific proof authority.

Verification reused the unchanged source-to-literal, descending-range and
exactly-one machines and the already verified paired-cell source composition.
Initial source attempts required explicit arithmetic/state normalization and a
narrow rewrite to avoid expanding the bound expression. The successful target
and axiom commands were retained after one regression proof exceeded recursive
list-reduction depth; rewriting the same list lengths fixed that fixture
without changing its expected values. The final regression wrapper bound those
exact unchanged successful commands and reached its own zero exit status.
Failed overall wrappers are not represented as successful verification.

#### Next dependency: complete initial and accepting families

Continue with source-derived initial state/head requirements, input-only cells
and accepting constraints. Then complete family dispatch, canonical clause
emission, recovery and the all-input polynomial reduction. The exact M230
dependency/root build, full axiom inventory, publication checks and release
verification remain due when those obligations are integrated.

**M230 is not earned.** Formal artefact coverage remains **205/207**.
The risk-weighted proof completion estimate remains **35%**, with uncertainty
**20% to 40%**; global gates remain **0/5**. The eligible root theorem is absent
and the publication gate is false. No fixed checkpoint changed. PNPLabs
publication remains deferred at its coherent M229 source pin.

### Active source-derived initial and accepting boundary payloads

Continue the **Final SAT decision** / **Accepted package implies P=NP**
dependency by constructing the canonical initial-state, initial-head and final
accepting-state requirements from the actual source/radix packet. These are the
three fixed semantic boundaries of every tableau, uniformly over all encoded
inputs and both verifier input modes; they are not additional finite schedule
fixtures or separately earned milestones.

Use one fixed branch syntax for the three roles. The verifier determines its
raw start/accept states, while the existing source fields determine dimensions
and the runtime fuel/head/final-time value. Physically copy the eight literal
arguments, run the existing canonical state/head kernel, and pack the actual
written index with the required-literal sign and payload tag. Do not provide
an index, fuel value, environment, literal or correctness answer from the caller.

Required theorems identify each argument environment with the canonical typed
request; prove the resulting payload is the unchanged canonical initial or
accepting constraint; and prove exact work/raw execution with preservation of
the actual source frame, original input, prior output and explicit exterior
allocation. The accepting-region theorem must identify its unique current slot
from authoritative region selection, not a supplied local-coordinate answer.
Provide encoded-input-size polynomial bounds for all literal work, retained
scratch, payload copies and every composition bridge.

Prepare independent literal numbering, polarity/tag, both-mode, source binding,
accepting-slot, exact execution, exterior, size/runtime and control-safety
regressions before compilation. Probe every new public theorem's compiled
axiom closure. Reuse unchanged source-literal and register-pack evidence; the
previous length and paired-cell proof suites do not need another run.

The complete accepting payload family closes at this component boundary.
Selection among all initial branches, input-only cells, full constraint
dispatch/emission/recovery and the packaged all-input reduction remain open.
M230 is not earned and no weighted checkpoint, publication row, status
coordinate or public source pin changes. PNPLabs remains deferred until the
major complete-builder publication boundary.

### Verified source-derived boundary payloads

The [boundary writer](../../lean/PNP/Concrete/CookLevinBuilderBoundaryPayload.lean)
now constructs all three canonical boundary requirements: the initial state,
initial head position and final accepting state. Each fixed branch reads the
actual source/radix packet, copies the eight canonical literal arguments,
computes the state/head index using the existing kernel, and packs that written
index with the required-literal polarity and tag. Verifier compilation fixes
the raw start/accept states; runtime fuel and dimensions remain source fields.

The universal proofs cover both verifier input modes. Argument environments
match the typed canonical requests, and every payload decodes to the unchanged
required constraint. The accepting-region theorem derives its unique local
coordinate from authoritative region selection and identifies the exact
whole-formula slot. It does not ask the caller for a final time, state index,
local coordinate, literal answer or correctness certificate.

Exact work-machine and raw compilation theorems preserve the actual source
frame, original input and prior output. Exterior allocation is explicit for
arbitrary exterior data, including the empty case. Encoded-input-size
polynomial bounds include source-to-literal work, scratch, payload copies and
all composition bridges; a separate exterior-bound theorem charges any
pre-existing outside space without repeating the source computation.

All 47 [boundary regressions](../../lean-regression/PNPConcreteCookLevinBuilderBoundaryPayload.lean)
passed. They cover independent block numbering, zero certificate width/fuel,
polarity/tag/order negatives, variable bounds, actual-source execution,
accepting-slot linkage, exterior behavior, control safety and complete branch
size/runtime bounds. All 28 public theorem axiom probes passed: one is
axiom-free, three use only `propext`, and 24 use only `propext` and
`Quot.sound`. None uses classical choice or project-specific proof authority.

Verification reused unchanged source-literal, register-pack, length-writer and
paired-cell evidence. The initial source attempt corrected the defining
coordinate namespace and an implicit list-lemma argument in source and tests
together. The successful target build and axiom commands were retained after
two decoder fixtures required direct equality proofs instead of a missing
decidable-equality instance. Their expected payloads did not change. The final
regression wrapper bound the exact unchanged successful commands, passed every
fixture and reached its own terminal zero status; failed wrappers are not
claimed as green verification.

#### Next dependency: input-only cells and complete family routing

The canonical accepting payload family and initial state/head branch writers
are complete at the source-packet boundary. The next missing initial family is
the input-only cell writer, using actual source bits and canonical position
bounds. Then connect all initial branches, full five-region payload dispatch,
clause emission and scratch recovery, and package the all-input polynomial
reduction. M230 root/inventory/publication/release verification remains due at
that complete integration boundary.

**M230 is not earned.** Formal artefact coverage remains **205/207**.
The risk-weighted proof completion estimate remains **35%**, uncertainty
**20% to 40%**, and global gates **0/5**. The eligible root theorem is absent;
the publication gate is false. No fixed checkpoint changed. PNPLabs
publication remains deferred at its coherent M229 source pin.

### Active source-derived input-only initial-cell payloads

Continue the **Final SAT decision** / **Accepted package implies P=NP**
dependency by constructing the remaining input-only initial-cell family.
The unbounded object is every source-selected initial cell of an arbitrary
encoded input, not a fixed position, bit fixture or supplied request.

Use one fixed runtime graph. Copy input length, fuel, tape width and the actual
initial-region coordinate from the source packet. Compare against the two
state/head prefix entries, then the actual width and center. Reject prefix
entries for the separate boundary dispatcher; write the canonical empty
opportunity for padding; otherwise derive a blank or source-bit request and
reuse the existing actual indexed-input resolver. Physically compute the
initial symbol index from the derived position and resolved symbol code, then
pack its required-literal sign and tag. Blank cells and padded opportunities
must remain different outputs.

The exact source theorem must run this fixed graph from the source packet and
original input, preserve prior output, and identify the unchanged canonical
initial constraint and whole-formula slot for every valid input-only cell.
No runtime coordinate, width answer, source bit, request, family or comparison
certificate may be supplied as proof authority. Charge every copy, comparison,
read, index operation, retained register and graph bridge to an encoded-size
polynomial. Runtime frame lemmas are implementation interfaces, not substitutes
for the source-bound theorem.

Prepare independent prefix/width/center, absent/false/true source-bit,
padding-versus-blank, literal numbering, polarity/tag, exact execution,
source binding, control safety and polynomial-bound regressions before the
targeted run. Probe every new public theorem's compiled axiom closure. Reuse
unchanged comparator, request-resolver, source-field and register evidence.

Initial-family dispatch, full region dispatch, clause emission, scratch
recovery and the packaged all-input polynomial reduction remain downstream.
M230 is not earned; no score, publication row, global gate or public source pin
changes. PNPLabs remains deferred at the coherent M229 publication.

### Verified source-derived input-only initial-cell payloads

The [input-only runtime](../../lean/PNP/Concrete/CookLevinBuilderInitialInputOnlyPayload.lean)
and [source composition](../../lean/PNP/Concrete/CookLevinBuilderInitialInputOnlySource.lean)
now construct the complete remaining input-only initial-cell family. A fixed
twelve-node graph handles arbitrary runtime coordinates: remove the two
state/head prefix entries, compare the position with the actual tape width,
compare valid positions with the source center, derive the blank/source request,
reuse the existing actual indexed-input resolver, compute the initial symbol
index and pack the required-literal payload.

Prefix coordinates are rejected for the separate boundary dispatcher. In-region
padding writes the canonical empty opportunity `[1]`; a blank tape cell writes
a real required symbol literal, not padding or an absent `[0]` slot. The machine
covers positions before, within and beyond the source input. Source bit values
are read from the actual preserved input and are never supplied as premises.
The twelve-node syntax is independent of input length, position, width and bit.

The source composition physically copies input length, fuel, tape width and
the initial-region coordinate from the existing source/radix packet. Its
uniform theorem relates the actual physical endpoint to the unchanged
whole-formula constraint slot in input-only mode, including padding. It derives
the capacity bound from authoritative region selection, proves canonical
literal identity and decoding, and computes its retained history rather than
accepting a supplied family, environment, source bit, literal or index answer.

Exact work-machine and raw execution preserve the original input, prior output
and source frame. The empty exterior frontier is explicit. Full
encoded-input-size polynomial bounds charge source-field copies, all physical
comparisons and reads, index arithmetic, retained scratch, payload writes and
every graph bridge. Runtime frame lemmas are backed by the source-level theorem;
they are not substitutes for that theorem.

All 80 prepared regressions passed:
51 [runtime regressions](../../lean-regression/PNPConcreteCookLevinBuilderInitialInputOnlyPayload.lean)
and 29 [source regressions](../../lean-regression/PNPConcreteCookLevinBuilderInitialInputOnlySource.lean).
They include independent prefix/width/center and false/true/absent-input cases,
padding-versus-blank, canonical numbering, polarity/tag/order negatives,
source binding, whole-formula slots, actual execution and full size/runtime
contracts. All 54 public theorem axiom probes passed: four are axiom-free,
20 use only `propext`, and 30 use only `propext` and `Quot.sound`.
No classical choice or project-specific proof authority entered the closures.

Targeted development corrected explicit tape/projection rewrites and terminal
state proofs without changing theorem statements or expected payloads. One
temporary runner stopped in checksum preflight; its transcription error was
fixed before source compilation. Each final verification wrapper reached its
own terminal zero status. The source integration reused the exact green
runtime target and did not rerun its 51 regressions or 35 axiom probes.
Unchanged reader, request, comparison, source-field and register evidence was
also reused.

#### Next dependency: complete initial-family dispatch

Both initial-cell modes and the three boundary requirements now have
source-derived payload writers; the paired length clause was verified earlier.
Connect them with source-preserving initial-family dispatch, including paired
padding and explicit scratch/exterior handling, then complete the five-region
dispatcher, clause emission and scratch recovery, and package the all-input
polynomial reduction. Full M230 root/inventory/publication/release checks remain
due at that integration boundary.

**M230 is not earned.** Formal artefact coverage remains **205/207**.
The risk-weighted proof completion estimate remains **35%**, uncertainty
**20% to 40%**, and global gates **0/5**. The eligible root theorem is absent;
the publication gate is false. No fixed checkpoint changed. PNPLabs
publication remains deferred at its coherent M229 source pin.

### Active complete initial-family dispatch

Continue the **Final SAT decision** / **Accepted package implies P=NP**
dependency by joining all verified initial payload writers into one fixed,
source-driven family program. The unbounded target is every initial-region
opportunity for every encoded input, in both verifier input modes, including
state, head, paired length, actual cells and padded opportunities.

The initial source/radix packet already ends in its local coordinate: the
initial family has no radix splits. Prove that physical suffix and run the
existing unary tag tests directly on it. Select state at zero, head at one,
paired length at two, and the appropriate complete cell writer thereafter.
Do not copy/erase a disposable coordinate or supply a branch answer. Only the
verifier's fixed input mode determines which cell program enters the graph.

For paired cells, connect the physically selected row/cell/payload to the
unchanged canonical initial slot. Convert exhausted in-region paired padding
to the empty opportunity `[1]`; do not silently equate padding, a blank-cell
requirement, an absent slot or a global failure. Derive row/cell selection and
all canonical bounds from the existing source selection theorems.

The exact source theorem must run the fixed graph from the actual source
packet and original input to the canonical initial/whole-formula payload,
with no caller-supplied role, bit, request, row, family, history or index.
Prove every direct tag test preserves the input frame. Preserve prior output
and describe the final exterior exactly: the paired length writer can leave
an explicit blank exterior, which must not be replaced by an empty list.
Provide encoded-input-size bounds for all branch work, retained scratch,
exterior space, padding writes, tag tests and composition bridges.

Prepare mode/prefix and canonical branch regressions before compilation,
including paired exhaustion and the length exterior. Check the complete
source theorem, decoding, exact work/raw runs, control safety and polynomial
bounds; audit every new public theorem. Reuse unchanged leaf evidence without
rerunning the input-only, paired-cell, boundary or length regression suites.

Five-region dispatch, clause emission, scratch recovery and the packaged
all-input polynomial reduction remain downstream. M230 is not earned; no
fixed checkpoint, progress score, publication row, gate, root or public source
pin changes. PNPLabs publication remains deferred at the coherent M229 pin.

### Verified complete initial-family dispatch

The [initial-family program](../../lean/PNP/Concrete/CookLevinBuilderInitialPayload.lean)
now constructs every initial-family payload from the actual source/radix packet
in both verifier input modes. Its fixed nine-node graph tests the existing
coordinate directly, preserving the physical packet, source input and prior
output. It selects state at zero, head at one, paired length at two, and the
complete appropriate cell writer thereafter. The fixed verifier mode selects
the cell program; no runtime role, row, bit, request or literal is supplied.

The paired route connects the actual selected length, cell and payload to the
canonical initial slot. Exhausted in-region paired rows produce the empty
opportunity `[1]`, not an absent `[0]` slot, a blank-cell requirement or a
global failure. Both input modes therefore include every in-region padding
opportunity as well as every substantive initial constraint. The constructor
computes its retained history; there is no supplied suffix witness in the
source execution interface.

The canonical source theorem reaches the unchanged whole-formula payload for
the actual source-derived constraint index. It proves initial-slot agreement,
decoding and exact work-machine and compiled raw execution. Direct tag tests
preserve arbitrary workspace and exterior tails. Complete-family execution
starts with an empty exterior, preserves the original input and prior output,
and retains the length writer's explicitly described blank exterior rather than
claiming that it has been erased. Other selected branches finish with an empty
exterior.

Uniform encoded-input-size polynomial bounds include all selected leaf work,
padding, retained registers, remaining exterior, tests and graph bridges.
The three bounded tag tests and their bridges cost at most 18 work steps;
the compiled bound accounts for their 108 raw steps. These are complete
source-size bounds, not finite termination or a caller-provided capacity claim.

All 43 prepared [regressions](../../lean-regression/PNPConcreteCookLevinBuilderInitialPayload.lean)
passed. They cover both-mode branch selection, unbounded cell coordinates,
physical tag preservation, paired exhaustion and padding distinctions, exact
runs, canonical slots, source binding, exterior contracts, control safety and
polynomial bounds. All 34 public theorem axiom probes passed: three are
axiom-free, three use only `propext`, and 28 use only `propext` and
`Quot.sound`. No classical choice or project-specific axiom entered the
new theorem closures.

Targeted development corrected the verifier/tableau input-mode projection,
proof normalization, explicit suffix witnesses and bridge arithmetic without
weakening the theorem statements. Regression-only syntax corrections left the
verified proof source unchanged; the final wrapper reused its exact compiled
target and axiom transcript and reached terminal zero status after all 43
regressions passed. The unchanged boundary, length, paired-cell and input-only
suites were not rerun.

#### Next dependency: whole-family dispatch and emission

The entire initial family is now source-derived, alongside the previously
verified payload components. Continue through the five-region dispatcher,
clause emission and scratch recovery, then package the all-input polynomial
Cook-Levin builder and reduction. The remaining composition must preserve each
family's real scratch/exterior contract. Full M230 root, inventory,
publication and release verification remain due at that integration boundary.

**M230 is not earned.** Formal artefact coverage remains **205/207**.
The risk-weighted proof completion estimate remains **35%**, uncertainty
**20% to 40%**, and global gates **0/5**. The eligible root theorem is absent;
the publication gate is false. No fixed checkpoint changed. PNPLabs
publication remains deferred at its coherent M229 source pin.

### Active source-driven whole-family payload dispatch

Continue the pinned **Final SAT decision** / **Accepted package implies P=NP**
dependency by joining all five payload families, their actual radix-entry
programs and the existing source-derived region selector into one finite
program. Preserve the canonical shape, initial, control, preservation and
accepting slot order. This is the next direct composition edge toward the
complete all-input polynomial builder, not another finite schedule prefix.

Use the region tag already written at the physical source-dispatch frontier.
Test it in place, route to the matching radix decoder and payload constructor,
and reject an invalid tag. Do not supply a region, conclusion, equality verdict,
row, source bit, canonical payload or correctness certificate to the unified
source execution interface. The machine syntax may depend on the verifier,
never on the input, cursor coordinate or a mathematical branch answer.

First give the five verified branch-entry programs one exact interface, including
their actual final values, computed payload history, canonical whole-formula
slot and exterior. Then wire those entries behind the source-derived tag tests.
For every actual body cursor, the intended theorem has the form
`workRunExact? (machine problem.verifier) (workSteps problem index remaining hBody)
  (initialConfiguration problem index remaining output) =
  some (finalConfiguration problem index remaining output hBody)`.
Its canonical final tape must end in the payload for
`problem.formulaConstraintSlotDirect
  (BuilderClauseDividerExecution.constraintIndex problem index)`.
The body-range proof is the existing cursor invariant, not a selection oracle.

Charge region assembly, tag tests, radix decoding, all selected payload work,
retained registers, exterior and every composition bridge to explicit
encoded-input-size polynomial bounds. Preserve actual length/shape/control/
preservation exterior contracts; do not identify a blank exterior with an
erased one. Preserve both option layers for padding versus an absent slot.

Prepare all five-family source, canonical, invalid-tag, exact work/raw,
control-safety and bound regression contracts with the new modules before
compilation. Probe every new public theorem's axiom closure. Reuse unchanged
family and source/radix evidence instead of rerunning their suites; validate
changed documentation links and exact scope after the new sources stabilize.

Clause occupancy, token emission, scratch recovery, the full cursor loop and
the packaged all-input polynomial reduction remain downstream. No component
alone earns M230 or its fixed checkpoint. Public status, source pins and
PNPLabs publication remain unchanged pending that complete integration.

### Verified source-driven whole-family payload construction

The complete five-region payload dispatch component is now kernel checked.
[BuilderFamilyPayload](../../lean/PNP/Concrete/CookLevinBuilderFamilyPayload.lean)
gives the shape, initial, control, preservation and accepting radix/payload
entries one exact interface.
[BuilderSourcePayload](../../lean/PNP/Concrete/CookLevinBuilderSourcePayload.lean)
runs the existing source selector from the actual body cursor, reads its
physically written region tag and executes the matching family entry.

The main execution theorem quantifies over every problem, body cursor and
existing output. It derives the selected region from that cursor; its machine
depends only on the verifier. No caller supplies a region, conclusion, row,
equality verdict, source bit, literal, payload or correctness certificate.
The canonical endpoint is the payload of the exact whole-formula constraint
slot selected by the clause-divider coordinate, preceded by the computed
history. Both option layers remain distinct for padding and an absent slot.

The finite source graph has eleven nodes: the source selector, five in-place
tag tests and five family entries. The tag tests preserve the selected source
frame and take at most forty work steps. An invalid tag at the tag-test entry
rejects without entering a payload family and preserves the older frame and
workspace; this is not a claim about arbitrary invalid source-entry tapes.
The accepted body run has exact work-machine and compiled raw-machine
execution theorems, canonical payload decoding and explicit final-tape and
control-safety contracts.

Polynomial bounds charge the source selector, tag tests, radix and payload
programs, all composition bridges, retained registers and actual exterior.
The common interface additionally proves the previously missing control
exterior estimate from the constructed head-move and scratch-drop operations.
It does not equate a blank exterior with erased scratch. The source-level
bounds apply to every valid body cursor with the existing cursor-balance
invariant, uniformly in encoded input length.

The prepared
[family regressions](../../lean-regression/PNPConcreteCookLevinBuilderFamilyPayload.lean)
and
[source regressions](../../lean-regression/PNPConcreteCookLevinBuilderSourcePayload.lean)
exercise all five entries, source-derived dispatch, canonical and option
contracts, exact work/raw execution, invalid-tag rejection, safety and
polynomial bounds. All 68 prepared regressions passed: 28 for the common
family interface and 40 for the unified source program.
All 34 public theorem axiom probes passed: one is axiom-free, one uses only
`propext`, and thirty-two use only `propext` and `Quot.sound`.
None uses `Classical.choice` or a project-specific axiom.

The first common-interface run exposed an accepting-branch alias elaboration
mismatch. Making the existing definitions explicit repaired it without
changing the theorem or its expected result; that failed attempt is not green
evidence. The final common-interface wrapper and subsequent source wrapper
both reached terminal zero status. The source wrapper reused the exact
verified common-interface evidence rather than repeating its regressions.
The final documentation and scope check likewise reuses both unchanged
source results; no full root build or publication suite is claimed here.

### Next dependency: source-driven clause emission and scratch recovery

Connect the canonical source-produced payload to clause occupancy and token
emission at the actual formula cursor, recover all computed history and
exterior, and prove the body transition returns the exact next cursor tape.
Then close the complete cursor loop and packaged all-input polynomial builder
and reduction. Preserve the manuscript's canonical clause and literal order;
a supplied occupancy answer, emission certificate or cleanup oracle cannot
replace executable derivation.

M230 is not earned. This component changes no fixed checkpoint, publication
row, global gate, root status or public source pin. Risk-weighted proof
completion remains 35%, uncertainty 20–40%; formal artefact coverage remains
205/207 and global gates remain 0/5 closed. PNPLabs publication remains deferred
until the complete major capability and its required audits are earned.

### Active general exactly-one clause-occupancy execution

Continue the pinned **Final SAT decision** / **Accepted package implies P=NP**
transport edge through physical clause occupancy. The canonical exactly-one
constraint emits one at-least-one clause and one exclusion clause per distinct
pair of list positions. Its existing `LocalConstraint.pairCount` recurrence
counts those positions, including repeated variable values.

For every runtime list length `count` and local clause coordinate `index`,
prove `2 * LocalConstraint.pairCount count + count = count * count` and hence
`index < 1 + LocalConstraint.pairCount count ↔
  2 * index + count < count * count + 2`.
Implement the latter test with the existing physical expression compiler,
argument packing and strict comparator. This avoids enumerating clauses,
materializing pairs, division and subtraction. Empty exactly-one lists still
have a populated empty clause at coordinate zero.

The finite program must not depend on either runtime number. Its exact theorem
runs from `endTape (older ++ [index, count]) inside outside` and returns the
correct accept/reject state, original registers, explicitly computed arithmetic
history and accounted exterior. Derive a uniform polynomial work/space bound
from the encoded register-span bound, including each preparation and graph
bridge and every cleared comparator cell. Preserve arbitrary surrounding data.

Prepare semantic boundaries, exact work/raw, preserved-frame, rejection,
control-safety and polynomial regression contracts before compilation; audit
all new public theorem axiom closures. Reuse the unchanged arithmetic and
comparator evidence. This is an internal general execution dependency, not a
new milestone or publication row.

The actual source payload supplies the list count, while the body divisions
supply the local clause coordinate. Their physical operand handoff and unified
payload-tag dispatch remain explicit next obligations: no source-entry theorem
is claimed merely from this two-register interface. Canonical token emission,
scratch recovery, the full cursor loop and packaged polynomial reduction also
remain open. M230, public status and PNPLabs publication remain unchanged.

### Verified general exactly-one clause-occupancy execution

[BuilderExactlyOneClauseOccupancy](../../lean/PNP/Concrete/CookLevinBuilderExactlyOneClauseOccupancy.lean)
now implements the canonical exactly-one occupancy test as one finite program
independent of both runtime operands. Its exact execution theorem reads the
actual local-clause index and list-count registers, computes both arithmetic
operands, packs them and runs the existing strict comparator.

The constructive identity `2 * pairCount count + count = count * count`
proves that occupancy is exactly `2 * index + count < count * count + 2`.
This does not enumerate pairs, materialize clauses, divide or subtract.
The canonical occupancy theorem applies to arbitrary variable lists, including
repeated variable values. At count zero, index zero is an occupied empty clause;
the next index is padding.

Both outcomes preserve the original registers and arbitrary surrounding
workspace. The arithmetic history remains explicit, and the theorem accounts
for every allocated and cleared exterior cell instead of silently erasing it.
The polynomial bounds cover the surviving registers and exterior as well as
both expressions, argument copies, comparison, restoration and all three
serial bridges. Source-bound operand extraction remains a separate obligation.

All 32 prepared regressions passed in the
[paired regression file](../../lean-regression/PNPConcreteCookLevinBuilderExactlyOneClauseOccupancy.lean).
All 14 public theorem axiom probes passed: one is axiom-free and thirteen use
only `propext` and `Quot.sound`. No `Classical.choice` or project-specific
axiom remains in those closures. The final target, audit and regression wrapper
reached terminal zero status. Existing expression, packing and comparator
regression suites were not repeated.

An earlier attempt stopped on composition and polynomial-alias elaboration.
The next build succeeded, but its axiom audit correctly rejected a convenience
iff proof that introduced classical choice. Explicit constructive implications
removed that dependency; the theorem statements and all prepared regression
expectations stayed unchanged. Neither failed wrapper is successful evidence.

### Next dependency: source-derived occupancy operands

Physically extract the local clause coordinate from the retained source
division frame and the list count from the canonical payload. Route the actual
payload tag to the requirement/implication, exactly-one and padded cases.
Do not supply either an occupancy answer or a clause-count certificate.
Keep the growing arithmetic/payload history distinct from the original cursor
frame and account for it during recovery.

After that handoff, connect canonical token emission, exact scratch recovery
and successor cursor, Finish, the complete loop and the packaged all-input
polynomial reduction. M230 is not earned. This component changes no checkpoint,
publication row, gate or source pin. Risk-weighted proof completion remains
35%, uncertainty 20–40%; formal artefact coverage remains 205/207 and global
gates remain 0/5 closed. PNPLabs publication remains deferred.

### Active source-root clause-coordinate handoff

Continue the pinned **Final SAT decision** / **Accepted package implies P=NP**
dependency through the actual source-to-occupancy operand handoff. The verified
source payload retains the original division frame below input-dependent
arithmetic and payload history. An end-relative copier whose control depends on
that history length is not a uniform source-derived construction.

Locate the selected register from the stable inner source boundary, using only
a compile-time root ordinal. Mark its real delimiter, then reuse the existing
marked-counter consumer and increment primitive to append a copy and restore
the original value. The number and values of newer registers may vary freely.
Do not enumerate source values or generate a control table from the input.

The generic exact interface must cover every list of older and newer registers,
every selected value, arbitrary interior data and arbitrary exterior:
`workRunExact? (machine beforeCount) (workSteps before value after)
  (initialConfiguration beforeCount before value after inside outside) =
  some (finalConfiguration beforeCount before value after inside outside)`,
with the structural layout equality `before.length = beforeCount`.
Its final register word is exactly
`before ++ [value] ++ after ++ [value]`; the exterior is
`outside.drop (value + 1)`. Restore the selected delimiter and all consumed
unary cells. Charge root seeking, fixed-ordinal traversal, marking, destination
allocation, every counter iteration, restoration and composition bridge.

Bind the root ordinal to the actual retained clause-divider coordinate.
Prove the canonical payload preserves that source prefix, then copy the actual
local clause coordinate through its variable-length history. In an exactly-one
branch, copy the count from the physically written payload header with the
existing constant-offset copier, producing the verified occupancy program's
two operand registers. Route the other payload tags without supplying an
occupancy verdict, source coordinate, count or correctness certificate.

Prepare the exact tape, restored-value, source-layout, work/raw, safety and
polynomial regression expectations with the source, before compilation. Reuse
unchanged counter, increment, constant, payload and occupancy evidence; validate
only the new dependency chain and its affected contracts during development.
Full root, inventory and publication integration remains due for complete M230.

Canonical token emission, recovery and successor, Finish and the complete
polynomial loop/reduction remain downstream. These are internal general
dependencies, not additional publication rows or fixed checkpoint credit.
M230 remains unearned, and PNPLabs publication stays deferred with its coherent
M229 source pin and progress values unchanged.

### Verified source-root clause-coordinate handoff

The fixed-ordinal [register copier](../../lean/PNP/Concrete/CookLevinBuilderRegisterRootCopy.lean)
locates the actual register from the stable inner source boundary, marks its
delimiter, copies it with the existing marked-counter/increment loop, and restores
the original value and delimiter. Arbitrarily many newer registers, arbitrary
values, interior data and pre-existing exterior cells are covered. Its control
depends on the root ordinal only, never on input-dependent history length.

The exact final word is `before ++ [value] ++ after ++ [value]`; the exterior is
`outside.drop (value + 1)`. The proved work bound for original register span at
most `S` is `S * (6 * S + 9) + 13 * S + 18`; compilation costs exactly six raw
steps per work step. Its register-plus-exterior bound explicitly includes every
allocated cell rather than assuming an empty exterior.
All 30 prepared copier regressions passed in the
[focused regression](../../lean-regression/PNPConcreteCookLevinBuilderRegisterRootCopy.lean).
All 11 public copier axiom probes passed: one is axiom-free and ten use only
`propext` and `Quot.sound`.

The [source-coordinate program](../../lean/PNP/Concrete/CookLevinBuilderSourceClauseCoordinate.lean)
proves that every canonical payload family preserves the actual clause-divider
frame. This includes the paired initial-input route's computed nine-field and
ten-field packet cuts: both cuts preserve the source prefix. The locator ordinal
is derived from the fixed verifier's two polynomial register layouts plus eleven
fields, with an exact proof of the preceding-register count.

The source program starts at the real cursor, computes the complete canonical
payload, then retrieves and appends the actual local clause coordinate through
the resulting variable-length history. Its execution theorem supplies no chosen
family, clause coordinate, payload, root ordinal, list count or correctness
certificate. The main source contract retains only the existing valid-body guard.
The final tape keeps the canonical payload unchanged and appends the actual
`clauseIndex`; source-span and raw-time polynomials account for the complete
payload construction, copy, exterior allocation and composition bridge.
All 32 prepared source-handoff regressions passed in the
[focused regression](../../lean-regression/PNPConcreteCookLevinBuilderSourceClauseCoordinate.lean).
All 16 public source-handoff axiom probes passed: one uses only `propext` and
fifteen use only `propext` and `Quot.sound`.

The targeted wrappers reached their own terminal zero status after source,
axiom and regression phases. Initial attempts diagnosed record-layout syntax,
private proof normalization and a request-packet alias; the final checks retain
the originally prepared theorem statements and regression expectations. No
`Classical.choice`, project-specific axiom, admitted theorem or new correctness
premise was introduced. Previously verified source-payload, register and
occupancy checks were reused unchanged; no complete Lean build or website audit
was repeated for these internal components.

**M230 is not earned.** These results close the physical source-coordinate
handoff, not the entire occupancy dispatcher or complete formula builder.
No fixed checkpoint, publication row, global gate, root theorem, axiom status,
publication gate or published source pin changed. Formal artefact coverage remains
**205 of 207 current scoped rows earned**; the risk-weighted proof estimate is
**35%**, uncertainty **20% to 40%**, with **0 of 5 global gates closed**.
PNPLabs publication remains deferred on its coherent M229 snapshot.

### Next dependency: complete payload-driven clause occupancy

Use the physically written payload tag to dispatch absent/padding,
requirement/implication and exactly-one cases. The general exactly-one program
must receive the copied source clause coordinate and the actual canonical
payload count, not caller-supplied operands. Reuse the fixed-offset register
copier and existing literal single-register eraser to inspect a copied tag and
restore the frame; account for the resulting cleared exterior cells.

Compose that dispatcher with the verified source-coordinate program and prove
that its endpoint equals the canonical formula-clause schedule's occupancy
projection. Preserve the distinction between an absent coordinate and an
in-range padded opportunity at the semantic interface. Do not claim occupancy
for a tag test alone. Prepare tag, boundary, empty-list, source-handoff, endpoint,
axiom and polynomial expectations before compilation.

Canonical token emission, exact recovery/successor, Finish and the complete
all-input polynomial builder/reduction remain downstream. Full root, inventory,
publication, workflow and exact release verification remain due at complete M230
integration; these internal components do not replace those release gates.

### Active all-family payload occupancy contract

Continue the pinned **Final SAT decision** / **Accepted package implies P=NP**
dependency from the verified physical source-coordinate handoff to complete
payload-driven clause occupancy. Do not replace the obligation with a tag test
or an assumed list count.

Build one finite graph independent of input, payload length, literal values and
local clause coordinate. Starting at `endTape (older ++ values slot ++ [j])`,
copy the actual payload tag from its fixed offset, test it, and erase only the
temporary copy. Absent coordinates reach a distinct dead endpoint; padded empty
opportunities reject occupancy. Requirements and implications are occupied
exactly at local coordinate zero. For exactly-one payloads, copy the physically
written list count past the tag and local coordinate, then execute the existing
general arithmetic occupancy program. Both occupied and unoccupied outcomes
must preserve the original payload and coordinate, with exact computed scratch
history and cleared/allocated exterior cells.

The generic theorem quantifies every canonical nested-option payload, every
local coordinate and arbitrary older/interior/exterior data. Compose it with
the source-coordinate program so that the source theorem supplies no payload,
tag, count, coordinate, occupancy verdict or correctness certificate. Prove
its endpoint matches the actual canonical formula-clause occupancy projection,
including the absent-versus-padding distinction.

Prepare exact graph/endpoint, canonical-layout, boundary, empty exactly-one list,
work/raw, axiom and source-encoded polynomial regression contracts with the
source. Charge copied tags, all rejected tests, erasure, copied counts, arithmetic,
comparison and every graph bridge. Reuse unchanged copy, erase, tag, arithmetic
occupancy and source-coordinate evidence; only the new dependency chain and
affected regressions are development checks.

Emission, exact recovery and successor, Finish and the full polynomial
all-input loop/reduction remain downstream. This internal dependency earns no
publication row or fixed checkpoint by itself. M230 remains unearned, and
PNPLabs publication remains deferred on its coherent M229 source pin.

### Verified source-derived clause occupancy

The pinned **Final SAT decision** / **Accepted package implies P=NP** dependency
now has a physical source-to-occupancy execution theorem. This is an internal
part of the complete builder, not an earned M230 or a finished reduction.

[Payload-driven occupancy](../../lean/PNP/Concrete/CookLevinBuilderPayloadClauseOccupancy.lean)
uses one fixed thirteen-node graph for every canonical payload and every local
clause coordinate. It copies the actual tag, tests all preceding alternatives,
and erases the temporary tag copy. Absent and padded coordinates remain distinct.
Requirements and implications accept occupancy exactly at zero. Exactly-one
payloads supply their physically written list count to the general arithmetic
test, including the empty-list case; no pairs or clauses are enumerated.
The original payload and coordinate survive, with an exact scratch history and
computed exterior. Work-machine and raw compiled execution, deterministic
control, terminal safety, and polynomial final-span/runtime bounds are proved.

All 49 prepared payload regressions passed, including absent-versus-padding,
empty lists, repeated variables, last occupied and first unoccupied indices,
all tag paths, preserved tape interiors and uniform polynomial contracts.
All 16 public payload axiom probes passed: four are axiom-free, five use only
`propext`, and seven use only `propext` and `Quot.sound`.
[The regression](../../lean-regression/PNPConcreteCookLevinBuilderPayloadClauseOccupancy.lean)
checks the general statements as well as small boundary fixtures.

[Source-derived occupancy](../../lean/PNP/Concrete/CookLevinBuilderSourceClauseOccupancy.lean)
composes the already verified source-coordinate execution with that fixed
dispatcher. The machine depends on the verifier, not a runtime family, payload,
tag, local coordinate, list count or supplied correctness certificate.
`workRun_observes_schedule` proves that execution from the actual source cursor
observes precisely the canonical formula-clause schedule at its decoded source
coordinate. The existing in-body hypothesis identifies that coordinate; it does
not supply an occupancy verdict. Exact tape preservation and compiled execution
are retained. Polynomial time and final register/exterior span follow from the
existing source bound, the new dispatch bound, and the composition bridge.

All 24 prepared source-occupancy regressions passed.
All 16 public source-occupancy axiom probes passed using only `propext` and
`Quot.sound`. Neither new dependency closure uses `Classical.choice` or a
project-specific axiom.
[The source regression](../../lean-regression/PNPConcreteCookLevinBuilderSourceClauseOccupancy.lean)
requires actual source-derived operands and complete-schedule observation, not
an externally chosen payload or a finite-case substitute.

Verification reused the exact green copy, erasure, tag, arithmetic-occupancy and
source-coordinate evidence. Only the new dependency targets and affected
regressions were checked. Payload source compilation and axiom evidence were
reused after a regression-only identifier correction; the final wrapper checked
the unchanged source identity and passed all prepared regressions. Earlier
non-green elaboration and launch attempts are not milestone evidence.
No root build, inventory regeneration, website proof rebuild or historical
replay was repeated for this internal addition. Final root/dependency/audit and
publication checks remain due at full M230 integration.

Formal artefact coverage remains **205 of 207 current scoped rows earned**.
The risk-weighted proof completion estimate remains **35%**, with uncertainty
**20% to 40%**. Global gates closed remain **0 of 5**, project-specific axioms
remaining **0**, the eligible root `PNP.Main.p_eq_np` absent and publication
false. No publication row, global gate or weighted checkpoint changed.
M230 is not earned; PNPLabs publication remains deferred on coherent M229.

### Next dependency: general payload-to-clause emission and recovery

Occupancy is now derived from the source, but it does not emit the selected
clause. Continue the same manuscript dependency with a finite program that
reads the preserved canonical payload and local coordinate and emits exactly
the selected clause tokens. Requirements, arbitrary implication lists and both
exactly-one clause forms must use uniform list/pair selection and polynomial
encoded-size execution, not another fixed list or selected clause fixture.
Account for the occupancy scratch history in the real handoff. Preserve source
and existing output, recover scratch exactly, then connect the complete
successor and Finish and prove the all-input polynomial loop and reduction.
Do not replace an unproved general step with supplied data, an added premise,
a project axiom or extra milestone credit.

### Active uniform literal-token selection contract

Continue **Final SAT decision** / **Accepted package implies P=NP** through the
unchanged canonical token schedule. The existing body loop emits one optional
token per coordinate; do not replace it with a different whole-clause schedule.
The verified physical token appender is reused after its request is derived.

The next shared physical selector must handle every sign, variable index and
token position of a literal, not a fixed unary prefix. Use one fixed finite
program starting at `endTape (older ++ [signValue positive, value, position])`.
Position zero reads a copied physical sign; a positive position copies and
decrements the actual position and compares it with the actual variable index.
The comparator's derived residual distinguishes the terminating false token from
out-of-range padding. Restore the temporary sign copy, preserve the original
three-register frame and arbitrary tape interior, and account for the exact
comparison scratch and exterior cells. Program control must not depend on the
runtime sign, variable value, position or a supplied token verdict.

The intended universal theorem observes actual work-machine execution as
`DirectToken.literalSlot {positive := positive, variableIndex := value} position`,
with exact raw compilation and encoded-input polynomial time/span bounds.
Prepare uniform execution/type/axiom/safety regressions and independent sign,
zero-index, last-unary, terminator and first-padding examples before compiling.
Tests must preserve their intended semantics through elaboration corrections.
Reuse the unchanged copy, tag, decrement, erasure and residual-comparator
evidence; no full core or website proof suite is needed for this development
boundary.

This selector is a necessary dependency of general clause-token selection, not
its replacement. Arbitrary implication-list traversal, exactly-one pair/list
selection, extraction of the actual token coordinate, source-bound request
construction, exact scratch recovery, successor, Finish and the complete
all-input polynomial builder/reduction remain required. Do not declare M230,
a publication row or a fixed checkpoint earned for this component. Keep the
coherent published M229 status and PNPLabs source pin unchanged.

### Active uniform scratch-recovery contract

The arbitrary-length source and comparison histories must be removed before
returning to the balanced cursor. Preserve the unchanged canonical schedule and
its input/output interior. Reuse the existing fixed inner-boundary locator:
expose its already-proved marking execution and control interface without
changing its machine or proof. A new fixed eraser then clears from the scratch
end back to that marked boundary, not for a caller-supplied history length.

For every retained register list `before` with verifier-fixed length, every
first discarded value and every arbitrary remaining register list, prove exact
work/raw execution from the ordinary end tape to `endTape before`, preserving
the original interior and replacing exactly the discarded word with exterior
blank cells. Charge the locator and every erasure transition. Derive a uniform
polynomial time bound from the original encoded span; recovery may not enlarge
that register/exterior span. Cover empty retained prefixes, zero discarded
values, empty tails, arbitrary long tails, exact symbols, control safety and
axiom closure in the prepared regressions.

This is the complete generic recovery dependency, not another fixed scratch
count. Its later source binding must derive the retained cursor boundary from
the existing source-prefix theorems and preserve the computed token result
through finite control. Keep the 36 verified literal-selector regressions and
its unchanged-source axiom evidence; check the newly exposed root interface and
new eraser/locator chain. Source-bound request construction, arbitrary clause
lists and pair selection, successor, Finish and the complete builder remain
required. M230 and all public progress/gate/source-pin fields remain unchanged.

### Verified uniform literal selection and scratch recovery

The manuscript's **Final SAT decision** / **Accepted package implies P=NP**
dependency now has two further general physical components. Neither is a
complete builder or an earned M230.

[Literal-token selection](../../lean/PNP/Concrete/CookLevinBuilderLiteralTokenSelector.lean)
uses one fixed ten-node graph for every sign, variable index and token position.
At position zero it reads the actual sign register. At every positive position
it copies and decrements the actual position, copies the actual variable index,
and compares the resulting unary coordinate. It distinguishes true tokens,
terminating false tokens and padding, not merely a finite literal prefix.
`workRun_observes_literal` identifies the executed result with
`DirectToken.literalSlot`. The original sign, index and position registers and
arbitrary tape interior survive. The exact comparison history, exterior,
compiled execution and polynomial time/final-span bounds are proved.

All 36 prepared literal-selector regressions passed.
All 16 public literal-selector axiom probes passed: four are axiom-free, three
use only `propext`, and nine use only `propext` and `Quot.sound`.
[The regression](../../lean-regression/PNPConcreteCookLevinBuilderLiteralTokenSelector.lean)
covers both signs, zero and positive indices, the first and final tokens,
padding, the original frame and the universal execution/polynomial interfaces.

[Root-bounded scratch recovery](../../lean/PNP/Concrete/CookLevinBuilderRegisterRootErase.lean)
reuses the existing root locator and a fixed four-rule eraser. The locator marks
the separator after a verifier-fixed retained register prefix. The eraser then
clears to that actual marker without receiving the discarded history's length.
The theorem covers every retained list of that fixed length, every first
discarded value and every arbitrary remaining register list. Zero values,
empty tails and empty retained prefixes are included. Exact work and raw
compiled execution restore `endTape before`, preserve the entire interior,
and replace exactly the discarded register word with exterior blank cells.
The complete locator/eraser chain takes at most `4 * bound + 7` work steps
when the original register word has length at most `bound`. The sum of
retained-register and exterior lengths is preserved exactly.

The [existing locator module](../../lean/PNP/Concrete/CookLevinBuilderRegisterRootCopy.lean)
only gained public wrappers for its already-proved marking execution and
control interface; its machine and original proofs were not changed.
All 32 affected locator regressions and all 28 new recovery regressions passed.
All 28 public locator/recovery axiom probes passed: five are axiom-free and
23 use only `propext` and `Quot.sound`. Neither component's dependency closure
uses `Classical.choice` or a project-specific axiom.
The [locator regression](../../lean-regression/PNPConcreteCookLevinBuilderRegisterRootCopy.lean)
and [recovery regression](../../lean-regression/PNPConcreteCookLevinBuilderRegisterRootErase.lean)
require exact tape results, unbounded histories, terminal safety, deterministic
control and polynomial execution rather than a caller-supplied erasure count.

The final targeted wrappers completed successfully. The literal selector's
unchanged source, regression and dependency evidence was reused during recovery
verification. The changed locator export and new recovery module were checked
in dependency order. Earlier non-green elaboration attempts are not evidence;
the list-rewrite correction changed no statement, machine or regression
expectation. No root rebuild, complete proof suite, inventory regeneration,
historical replay or website proof build was duplicated for these components.
Those final integration boundaries remain due for complete M230.

Formal artefact coverage remains **205 of 207 current scoped rows earned**.
The risk-weighted proof completion estimate remains **35%**, with uncertainty
**20% to 40%**. Global gates closed remain **0 of 5**, project-specific axioms
remaining **0**, the eligible root `PNP.Main.p_eq_np` absent and publication
false. No publication row, global gate or weighted checkpoint changed.
M230 is not earned; PNPLabs publication remains deferred on coherent M229.

### Next dependency: uniform list/pair selection and source-bound token requests

Connect the literal primitive to arbitrary implication lists and both
exactly-one clause forms, including ordered exclusion-pair selection. Derive
the actual token position and payload from the source cursor; a supplied
literal, list, pair, token or correctness premise is not the final interface.
Preserve the selected token/padding result in finite control while recovering
the variable-length history to the real retained cursor prefix. Do not erase
the payload prematurely and recompute it. Then connect physical request
dispatch, successor and Finish and prove the complete all-input polynomial
loop and reduction. Keep the canonical clause/token schedule unchanged and
stop at an unproved general boundary rather than substituting a finite fixture.

### Active arbitrary-register indexing contract

Continue the pinned **Final SAT decision** / **Accepted package implies P=NP**
dependency through the runtime list-access obligation required by arbitrary
literal lists and ordered exclusion pairs. One fixed machine must read an
ordinal physically written after a reader-ordered register list, locate the
selected entry, copy its value, and restore the original list and ordinal.
Neither the ordinal nor the input-dependent list length may determine the
control table.

For every `before`, selected `value`, `after`, older registers, and arbitrary
interior/exterior, require exact work and raw compiled execution from
`endTape (older ++ (before ++ [value] ++ after).reverse ++ [before.length])`
to the same register sequence with `value` appended. Give the corresponding
ordinary-list/valid-index interface, not just a chosen split fixture. The
valid-index condition is the data-domain boundary; this primitive does not
claim to classify invalid ordinals. The final source selector must derive its
bounds from the actual payload and branch, not receive a correctness verdict.

Reuse the existing marked-counter consumer and marked-register copier. Add a
fixed moving candidate marker and charge initialization, each ordinal-consumer
iteration, each physical pointer advance, exhaustion, marker restoration and
copying. Prove polynomial work/raw time and final register/exterior span in the
original encoded span, including zero values, an empty skipped prefix and
arbitrary newer/older data. Preserve the literal selector and root recovery.

Prepare general execution, source-bound polynomial, marker/control safety and
boundary regression contracts with the source. Expose only the existing
copier's necessary checked interface; do not change its machine or original
proofs. Run new and affected targets/axiom probes/regressions in dependency
order. Reuse unchanged prior component evidence, keep all public M229 fields
and the complete-builder checkpoint unchanged, and defer PNPLabs publication.
This is an internal M230 dependency, not an earned publication row or a
substitute for full literal/pair selection, token request construction,
source recovery, successor, Finish or the complete builder/reduction.

### Verified runtime-indexed register-list access

The pinned **Final SAT decision** / **Accepted package implies P=NP** dependency
now has the runtime list-access primitive needed by arbitrary literal lists and
ordered exclusion pairs. This remains an internal M230 dependency, not an earned
complete builder or publication row.

[Runtime-indexed copying](../../lean/PNP/Concrete/CookLevinBuilderRegisterIndexedCopy.lean)
uses one fixed five-node graph. It reads the ordinal written on the tape,
marks the current candidate, consumes ordinal units while advancing through the
actual variable-width register data, restores the original ordinal and
delimiters, and invokes the existing marked copier. Neither the selected index,
the input list length nor a growing history determines the control table.

`workRun_select_getElem` and `run_compile_select_getElem` state the ordinary
list interface for every valid index. The original list, ordinal, older
registers and arbitrary tape interior survive; the selected entry is appended
and exactly its allocation is charged to the exterior. The split-list execution
theorem supports the induction, but is not the only public selection contract.
The valid-index data domain remains explicit: the primitive does not classify
invalid ordinals. The complete source selector must derive that bound from its
actual payload and branch, not receive a correctness verdict.

The complete initialization, ordinal loop, pointer movement, exhaustion,
restoration, copy and composition transitions are charged. `workSteps_le`
provides a quadratic work bound in the original encoded register span; compiled
execution uses six raw steps per work step. The final register/exterior span is
at most `2 * bound + 1`. `selected_source_polynomial_bounds` carries both bounds
through the ordinary-list/valid-index interface for any supplied polynomial
bound on the original encoded source span.

All 36 prepared indexed-copy regressions passed, covering general list access,
both work and raw execution, zero values, empty skipped prefixes, arbitrary
long skipped lists, exact exterior allocation, marker rejection cases,
deterministic control and source polynomial bounds.
[The regression](../../lean-regression/PNPConcreteCookLevinBuilderRegisterIndexedCopy.lean)
retains concrete boundary fixtures only as tests of the general machine.

The [existing marked copier](../../lean/PNP/Concrete/CookLevinBuilderRegisterRootCopy.lean)
only gained execution, control and step-bound exports for its already-proved
copy phase. Its machine and original proofs were unchanged.
All 35 affected copier regressions passed.
[The copier regression](../../lean-regression/PNPConcreteCookLevinBuilderRegisterRootCopy.lean)
checks the newly exposed phase alongside the existing root-locator interface.
All 44 public copier/indexed-copy axiom probes passed: seven are axiom-free,
three use only `propext`, and 34 use only `propext` and `Quot.sound`. No closure
uses `Classical.choice` or a project-specific axiom.

The final targeted wrapper completed with zero exit status. After source
compilation and axiom auditing succeeded, only regression declaration formatting
needed correction. The final run byte-checked and reused that exact source and
axiom evidence, then passed every prepared regression. Earlier non-green
elaboration attempts are not evidence. No root rebuild, complete proof suite,
inventory regeneration, historical replay or website proof build was repeated.

Formal artefact coverage remains **205 of 207 current scoped rows earned**.
The risk-weighted proof completion estimate remains **35%**, with uncertainty
**20% to 40%**. Global gates closed remain **0 of 5**, project-specific axioms
remaining **0**, the eligible root `PNP.Main.p_eq_np` absent and publication
false. No publication row, global gate or weighted checkpoint changed.
M230 is not earned; PNPLabs publication remains deferred on coherent M229.

### Next dependency: physical literal-list and ordered-pair selection

Use the fixed runtime indexer to read signs and variable indices from arbitrary
canonical payload lists, deriving their physical offsets including accumulated
scratch registers. Prove the complete variable-width literal-token search and
the selected ordered exclusion pair; do not replace these with a fixed literal
or pair coordinate. Bind the actual token position and selection to the source
cursor, preserve the selected token/padding result through recovery, and connect
request dispatch, successor and Finish. Complete the all-input polynomial
builder/reduction and its remaining root, audit and publication boundaries
before claiming M230 or the fixed builder checkpoint.

### Next internal component: canonical payload field selection

Legacy anchor remains **Final SAT decision** / **Accepted package implies P=NP**:
the complete formula builder must physically read each runtime literal and
ordered-pair variable from the canonical constraint payload. The verified indexer
alone does not compute the physical field address.

Implement one fixed-schema affine field reader. Its stride, field offset and
number of newer registers are structural constants; the selected ordinal, list
length and payload values remain runtime data. Compile the address expression
from the actual ordinal, including every register the expression itself creates,
then invoke the existing general runtime indexer. Preserve the original payload,
ordinal, arbitrary newer values and tape interior. Charge expression evaluation,
the chain join, selection, copying and exterior allocation.

The intended general execution theorem has only the layout equality and valid
field-index bound as entry-domain premises; it appends exactly the selected
payload entry. Specialize it to every valid literal-list index (sign and variable
fields) and every valid variable-list index, deriving field bounds from the
canonical encodings. These are physical data-access theorems, not assumptions
that a selected literal, pair, token or verdict is correct.

Affected producer/consumer matrix: new field-reader definitions and execution,
control and encoded-size polynomial theorems; a matching focused regression with
general types, independent offset fixtures, frame/allocation checks and source
bounds; a complete public theorem axiom-probe list; and this plan. Existing
indexer, expression compiler and payload encoding stay byte-identical. No
inventory, status, workflow, publication source or website value changes.

Verify source/expectation name sets and whitespace first, then the new permanent
Lake target, its public axiom closures and focused regression. Reuse unchanged
component evidence rather than repeating old suites. Complete M230 integration
still owes the root, full audits and release boundaries.

Remaining downstream obligations are variable-width literal-token search,
canonical ordered-pair coordinates, source-bound token position and request
selection, result-preserving recovery, successor/Finish, and the complete
all-input polynomial builder and reduction. M230 is not earned and publication
remains deferred; no row, checkpoint, gate or score is awarded here.

### Verified canonical payload field access

The [field reader](../../lean/PNP/Concrete/CookLevinBuilderPayloadFieldCopy.lean)
closes the runtime-ordinal-to-physical-field edge required by the pinned
**Final SAT decision** / **Accepted package implies P=NP** reconstruction.
One fixed-schema machine evaluates the affine address from the actual ordinal
register, includes its own five expression registers and every newer register
in the physical offset, and invokes the existing general runtime indexer.

For every valid field coordinate, `workRunExact` and `run_compile_exact`
append exactly that entry. The payload, original ordinal, older and newer
registers, and arbitrary tape interior are preserved. The exact exterior
allocation includes all five expression registers and the selected value.
Runtime data does not determine the machine's control table.

`workRun_literal_field` and `run_compile_literal_field` read the sign or
variable index of every literal in an arbitrary canonical literal list.
Their field bounds and values follow from the actual canonical encoding.
`workRun_variable_field` and `run_compile_variable_field` likewise read
every valid entry in the canonical variable list, providing the data-access
operation required by ordered-pair selection. These interfaces do not accept
a supplied selected literal, variable value, token or correctness verdict.

The general, literal-list and variable-list `source_polynomial_bounds`
interfaces charge expression evaluation, the chain join and indexed copying.
Their span includes both the surviving register frame and remaining exterior.
All three bounds are polynomials in an original encoded-span polynomial; the
five-register calculation is a proved compiler output, not an assumed offset.

All 34 prepared [regressions](../../lean-regression/PNPConcreteCookLevinBuilderPayloadFieldCopy.lean)
passed. They cover general work/raw execution, arbitrary newer data, zero
fields, independent address/allocation fixtures, literal polarity and indices,
variable-list access, deterministic control, terminal separation and source
polynomial bounds. All 24 public theorem axiom probes passed: seven are
axiom-free, one uses only `propext`, and 16 use only `propext` and
`Quot.sound`. No closure uses `Classical.choice` or a project-specific axiom.

The whole targeted wrapper reached its final green marker and terminal zero
status. The first source attempt exposed three proof-composition mismatches;
the repair only made the chain handoff and literal lookup instantiations
explicit. The intended theorem types and all regression expectations stayed
unchanged. That non-green attempt is not verification evidence.

The expression compiler, runtime indexer, canonical payload encoding and their
existing regression evidence were unchanged and reused. No complete root
build, inventory regeneration, historical replay or website proof suite was
repeated for this internal component.

Formal artefact coverage remains **205 of 207 current scoped rows earned**.
The risk-weighted proof completion estimate remains **35%**, uncertainty
**20% to 40%**. Global gates closed remain **0 of 5**, project-specific axioms
remaining **0**, the eligible root `PNP.Main.p_eq_np` absent and publication
false. No row, weighted checkpoint or global gate changed. M230 is not earned;
PNPLabs publication remains deferred on the coherent M229 snapshot.

### Next dependency: general literal-token search and ordered-pair coordinates

Compose the field reader with the verified literal-token selector to search
the actual variable-width list, and derive the canonical ordered exclusion
pair coordinates before reading their variables. Account for accumulated
scratch and preserve canonical clause order and polarity. The entry-domain
index bound of a field reader is not a supplied global coverage certificate:
derive it from the actual source-bound branch and list count.

Then bind the original token position, payload and selected result to the source
cursor, preserve the request through recovery, and close dispatch, successor
and Finish. The complete all-input polynomial builder/reduction, root and
publication audits remain required before earning M230 or its fixed checkpoint.

### Physical indexed-literal selection within the general list search

The next implementation phase connects the verified field reader to the
three-outcome literal-token selector. This is the runtime data-access-to-token
edge of the same pinned **Final SAT decision** / **Accepted package implies
P=NP** reconstruction, not a replacement for the complete variable-width search.

Use one finite machine with input registers consisting of the actual canonical
literal-list payload followed by the runtime literal ordinal and token position.
Read the variable field with one newer register, then the sign field with seven
newer registers, deriving those offsets from the first stage's six-register
output. Pack the actual sign, variable index and original position from their
fixed structural locations. No selected literal, sign, variable or token verdict
may be passed as a machine parameter or correctness premise.

Prove exact work and compiled runs for every valid literal ordinal and every
token position, including padding. Preserve all three selected outcomes through
composition: a padding endpoint must not be treated as a false-bit endpoint.
Prove the canonical observed literal token, preserved original registers,
exact exterior effects and complete encoded-source polynomial bounds.

Affected contracts are the new preparation/selection module, its complete public
axiom list and focused regression, and this plan. Prepare general theorem-type,
three-outcome, independent layout/allocation and polynomial expectations before
the targeted build. Reuse unchanged field-reader, packer and selector evidence;
do not rerun their suites or regenerate publication data.

After this physical per-entry selector, derive the runtime ordinal and residual
position for the complete variable-width list and the canonical ordered
exclusion-pair coordinates. Bind these to the source cursor, preserve the request
through recovery and close the complete loop. The valid ordinal is an entry
domain, not a supplied global routing certificate. M230 remains unearned,
publication deferred, and no row, checkpoint, gate or score changes here.

### Verified physical indexed-literal token selection

The [composed selector](../../lean/PNP/Concrete/CookLevinBuilderIndexedLiteralTokenSelector.lean)
now reads both literal fields and the original token position from its actual
register input. This advances the pinned **Final SAT decision** / **Accepted
package implies P=NP** construction from field access to token observation.
Neither a selected literal nor a sign, variable index or token verdict is
supplied as proof authority.

The first field read leaves six registers, so the second reads past seven
newer registers including the preserved token position. A fixed pack copies
fields 13, 7 and 1 of the resulting 14-register environment into the exact
sign/value/position interface. These structural counts are proved from the
actual producer outputs. They do not depend on the runtime list or ordinal.

`prepare_workRunExact`, `workRunExact` and `run_compile_exact` apply to
every valid ordinal in an arbitrary canonical literal list and every token
position. The selected state observes precisely
`DirectToken.literalSlot literals[index.val].emit position`.
State-renaming injectivity preserves true, false and padding separately.
The padding endpoint is proved rule-free rather than interpreted as a false bit.

The input list, ordinal, original token position, older registers and arbitrary
tape interior survive. Exact exterior effects include both field reads, argument
packing and selector scratch. Preparation and complete-selection polynomial
contracts charge every component and chain join, including the surviving frame
and exterior in the encoded-source span bound.

All 32 prepared [regressions](../../lean-regression/PNPConcreteCookLevinBuilderIndexedLiteralTokenSelector.lean)
passed. They cover general preparation and selection, compiled execution,
independent scratch/address fixtures, both signs, unary bits, zero-valued
indices, terminators, padding, frame preservation, all terminal controls and
complete polynomial bounds. All 20 public theorem axiom probes passed: six are
axiom-free, two use only `propext`, and 12 use only `propext` and
`Quot.sound`. There is no project-specific axiom or `Classical.choice`.

The whole targeted wrapper finished with its green marker and terminal zero.
Source verification required explicit applications of state-renaming injectivity.
After source and axiom checks passed, the regression needed a complete record
assertion and a namespace import; no expected result or theorem type was
weakened. The final run byte-checked and reused that unchanged source/axiom
evidence, then passed all regressions. Earlier non-green attempts are not
component evidence. Existing field-reader, packer and selector suites, the full
root/inventory boundary and website proof tests were not redundantly rerun.

Formal artefact coverage remains **205 of 207 current scoped rows earned**.
The risk-weighted proof completion estimate remains **35%**, uncertainty
**20% to 40%**. Global gates closed remain **0 of 5**, project-specific axioms
remaining **0**, the eligible root `PNP.Main.p_eq_np` absent and publication
false. No row, checkpoint or gate changed. M230 is not earned and PNPLabs
publication remains deferred on the coherent M229 snapshot.

### Remaining list and source integration

The new theorem reads an arbitrary indexed literal; it does not yet locate that
literal from the overall variable-width token coordinate. Complete that runtime
locator, including the empty/exhausted-list branch and residual token position,
and derive the canonical ordered exclusion-pair coordinates. The ordinal bound
must follow from the actual branch and list count, not a supplied coverage
certificate. Preserve canonical order and polarity.

Then derive source-bound coordinates, preserve the selected request through
recovery and close dispatch, successor and Finish. Complete the all-input
polynomial builder and packaged reduction, root/audit integration and release
boundaries before earning M230 or the fixed complete-builder checkpoint.

### Complete runtime variable-width literal-list lookup

Continue the same pinned **Final SAT decision** / **Accepted package implies
P=NP** construction. The required next general interface is a fixed machine
whose observed result is `DirectToken.boundedLiteralListSlot literals position`
for every canonical list and every overall token position, including empty and
exhausted lists. The runtime may not receive a selected literal ordinal,
residual position, coverage certificate or token verdict as proof authority.

Use loop registers for ordinal, remaining literal count and residual position,
starting at zero, the actual list length and the original token position.
A physical count guard handles exhaustion before any field access. Read the
actual variable index, construct its full literal width (index plus two), and
compare the residual position with that width. The hit branch reads the actual
sign and invokes the verified three-outcome selector. Its width premise is
derived by the comparison and excludes the selector's padding case.

On a miss, physically copy/increment the ordinal, copy/decrement the positive
remaining count and copy the actual comparator residual. Prove that the complete
discarded logical register chunk has exactly 17 fields, so an affine field reader
with stride 19 accounts for both the accumulated history and the two-field
canonical literal encoding. Derive these counts from all producer definitions;
do not choose them independently of the completed iteration.

Prepare the physical comparison and advancement interfaces, the hit selector,
the fixed cyclic graph, the exact execution induction over the remaining list,
and the original-source polynomial contracts. The original source/payload data
and arbitrary tape interior remain intact; all scratch and exterior effects
must be charged. Keep true, false and exhausted-list padding distinct.

Prove one global workspace bound from the original encoded input span, the
bounded scalar values and the number of list entries. Do not repeatedly compose
a loose per-iteration span polynomial: its degree could grow with runtime list
length even when the actual construction is polynomial. Apply fixed per-step
time polynomials to the proved global span and sum them over at most the actual
list length plus the final guard/selection phase.

Affected contracts are the new search data/step and complete-loop modules,
their general execution, bounds, terminal and canonical-result regressions,
complete public axiom lists, and this plan. Reconcile definitions and all
expectations before targeted compilation. Reuse unchanged component evidence;
full M230 root, inventory and publication checks remain due at integration.

The complete list lookup is still one dependency of M230, not the complete
builder/reduction. Canonical ordered-pair coordinates, source-bound request
selection, request-preserving recovery, dispatch/successor/Finish and the final
builder and audit boundaries remain required. No publication row, weighted
checkpoint or gate changes during this implementation. M230 is not earned;
PNPLabs remains deferred on coherent M229.

### Verified literal-search frame and physical width comparison

Two general components of the same complete-list locator are now checked.
Neither accepts a supplied literal-width verdict or a preselected result.

**History and address frame.** The physical comparison chunk has exactly
17 registers, derived from its actual producers: three loop scalars, six
field-read registers, three width-expression registers and five restored
comparison registers. A stride-19 reader accounts for both the retained
history and the two-field literal encoding. For every valid literal ordinal,
either field can be read through the derived history with exact physical and
compiled execution, frame preservation and source-polynomial bounds.

The exact chunk word length is
`40 * ordinal + count + 2 * position + 5 * value + residual + 60`.
The residual never exceeds the input position. Scalar bounds from the original
input therefore give a linear per-chunk bound; the proved history envelope is
quadratic in the original bound, not a polynomial whose degree grows with the
iteration count. Applying that envelope to the complete cyclic execution still
requires the loop to establish its history, scalar and exterior invariants.

**Physical comparison.** One fixed machine reads the actual variable index,
constructs index plus two as the full literal width, copies the actual residual
position and width into disposable comparison operands, and runs the existing
restoring comparator. Acceptance is exactly position less than width; rejection
is exactly width at most position. The output retains the complete expected
17-register chunk and a usable residual for the next iteration.

The exact execution theorem covers every canonical list, valid current ordinal,
derived-length prior history, count and position, and arbitrary older and
interior/exterior tape data. Raw compilation, both terminal contracts,
query-distinctness, no-rule terminal states and complete preparation/comparison
polynomial bounds are checked. The comparison does not increase exterior length,
and its actual additional history is charged separately for the later loop
bound.

**Verification.** All 28 prepared frame regressions and all 19 public frame
axiom probes passed. All 30 comparison regressions and all 18 public comparison
axiom probes passed. The 37 probes use only the existing logical/kernel
authorities `propext` and `Quot.sound` where needed; none introduces
`Classical.choice` or a project-specific axiom. Both targeted wrappers reached
their own terminal zero exit and final success marker.

The final comparison verification reused the byte-identical successful source
build and axiom transcript after correcting four regression declarations that
had accidentally included private proof bodies. General regression contracts
must copy only complete theorem signatures, including record-valued targets;
a one-line proof assignment must terminate the signature too. No theorem type
or independent boundary expectation was weakened. Unchanged dependency and
earlier selector tests were reused rather than repeated.

**Remaining complete-list integration.** Physically advance the ordinal,
decrement the actual positive remaining count and retain the produced residual.
Compose the count guard, hit-only sign/token selection, miss advancement and
empty/exhausted padding branch into one fixed cyclic graph. Prove exact
execution over the whole remaining list and derive the required global bounds
from the original input, rather than accepting a supplied search result.

M230 is not earned. The complete literal locator, canonical ordered-pair
coordinates, source-bound dispatch and request-preserving recovery, successor
and Finish, complete builder/reduction and final root/inventory/publication
audits remain open. Public status is unchanged: formal artefact coverage
205/207; risk-weighted proof estimate 35%, uncertainty 20–40%; global gates
0/5. No publication row or checkpoint changes; publication remains deferred
on coherent M229.

### Physical advancement for the complete literal-list locator

Continue the pinned **Final SAT decision** / **Accepted package implies P=NP**
construction's complete all-input builder, using the general comparison just
verified. This next interface advances the actual runtime search frame:
`older ++ chunk ordinal (remaining + 1) position value` becomes that same
retained frame followed by `[ordinal + 1, remaining, residual position value]`.
The ordinary-register copier, incrementer, decrementer and final residual copy
form one fixed machine. Only fixed structural offsets determine its control.

Prove exact physical and compiled execution for all older data and all natural
counter/position values, with the positive count represented by
`remaining + 1`. The cyclic driver must obtain that positivity from the actual
count guard, not request it as a correctness certificate. On the comparison's
miss branch, derive the next position as `position - (value + 2)`.

Charge all three physical copy scans, both arithmetic steps and all four chain
joins. Prove preservation of older and comparison registers, the next history
length, terminal/query contracts, exterior effects and source-polynomial time
and workspace bounds. Derive copy-tail and scalar bounds from the encoded entry
span; do not assume separately bounded intermediate data. Keep the original
comparison and history definitions unchanged.

Prepare independent equality/greater-boundary, final-item and exact-register
fixtures and every general theorem/type and axiom contract in the same patch.
The affected consumers are the new advancement regression and the later cyclic
lookup module. Reuse unchanged frame/comparison and earlier component evidence.
The hit selector, physical exhaustion guard, complete graph execution and global
original-input bounds remain required before the list lookup is complete.

No publication or scoring change: M230 is not earned, and publication remains
deferred on coherent M229. The full formula builder, source-bound dispatch,
canonical ordered-pair coordinates, recovery, successor/Finish and the final
root/inventory/publication audits remain required.

### Physical hit selection for the complete literal-list locator

After the actual width comparison accepts, read the sign of that same literal
through the 17-register comparison chunk and accumulated prior history. The
fixed stride-19 field reader uses an after-count of 16; its six output registers
extend the chunk to a 23-register environment. Fixed addresses 22, 8 and 2
then pack sign, variable index and residual position for the existing selector.

The exact interface must work for every actual canonical literal, valid ordinal,
derived prior history and arbitrary count/position, older registers and tape
data. Prove physical execution, raw compilation, the canonical token result
and complete preparation/selection polynomial bounds. In addition, derive from
`position < value + 2` that the final state is true or false rather than padding.
The cyclic driver must establish that premise with its comparison; the selector
must continue representing padding distinctly outside that domain.

Reconcile the complete 23-field environment from its producers before testing.
Prepare sign, equality-boundary, zero-variable, padding and actual-run contracts
with the source, together with every public theorem's axiom probe. Reuse the
byte-identical frame, advancement and previous selector verification.
The count guard, cyclic graph, whole-list induction and global source-bound
lookup remain separate obligations. This is internal M230 work; no publication
row, weighted checkpoint, progress score or website release is earned here.

### Verified miss advancement and hit selection

The two physical search branches are now checked for arbitrary runtime data.

**Miss advancement.** One fixed five-stage machine copies/increments the actual
ordinal, copies/decrements the actual positive count, and copies the comparator's
residual. Its exact output preserves the complete 17-register comparison chunk
and appends the three next-loop scalars. The proof covers all older registers
and arbitrary interior and exterior tape data. On a miss the new position is
exactly the old position minus the current literal's full token width.

All three copy scans, both arithmetic operations and all four composition joins
are charged in the polynomial time bound. Scalar and copy-tail bounds come from
the encoded entry span, not separately supplied intermediate bounds. The final
residual copy consumes the blank cell released by decrementing, so advancement
does not increase exterior length. The next history length is exactly
17 times the next ordinal.

**Hit selection.** The fixed stride-19 reader physically reads the same literal's
sign through the retained comparison frame. The producer-derived 23-register
environment has a checked exact correspondence to its packed sign, variable
index and token-position arguments. Physical and compiled execution return the
canonical literal token. The complete preparation and selection costs have
source-polynomial bounds, with original data and all scratch accounted for.

The terminal contract is explicit: when the actual width comparison establishes
`position < value + 2`, the selector reaches its true or false state, never
padding. Outside that domain, padding remains a distinct, rule-free third
outcome. No caller-supplied token, sign, ordinal or completeness verdict generates
the control, and the later cyclic graph must derive the hit premise itself.

**Verification.** All 33 advancement regressions and all 21 public advancement
axiom probes passed. All 31 hit-selection regressions and all 19 public
hit-selection axiom probes passed. Every one of the 40 probes uses only the
existing logical/kernel authorities `propext` and `Quot.sound` where needed.
Both final targeted wrappers reached their own success marker and terminal zero
exit. Unchanged comparison, history, field-reader and earlier selector evidence
was reused; no full-root or website proof suite was repeated.

The fail-closed axiom check initially detected `Classical.choice` in a scalar
bound helper, through an auxiliary `Classical.propDecidable` proof. Splitting the
conjoined arithmetic goal explicitly before `omega` removed that dependency;
the complete public axiom list was then checked again. A record-environment
rewrite was also normalized consistently before the final selector build.
Neither fix changed a theorem statement, boundary expectation or claim.

**Next: complete guarded lookup.** Join the count-copy/zero guard and its
single-register cleanup to comparison, advancement and hit selection in one
fixed cyclic graph. Induct over the actual remaining list, with the processed
prefix, ordinal and accumulated history derived from execution. Handle empty
and exhausted lists as padding. Prove equality with
`DirectToken.boundedLiteralListSlot` for every original list and position.

Use one original-input polynomial envelope for all iterations. The ordinal plus
remaining count stays equal to the original list length; residual position never
increases. Derive actual history and exterior growth and sum fixed node costs
over the bounded number of iterations. Do not iterate a loose span polynomial.

M230 is not earned. The complete lookup, canonical ordered-pair coordinates,
source-bound dispatch and recovery, successor/Finish, full formula builder and
reduction, and final root/inventory/publication audits remain required.
Formal artefact coverage remains 205/207; the risk-weighted proof estimate
remains 35%, uncertainty 20–40%; global gates remain 0/5. No checkpoint or
publication row is added, and publication remains deferred on coherent M229.

### M230 complete literal-list lookup: restoring guard and fixed loop plan

The legacy anchor remains the complete Cook–Levin formula construction and its
canonical literal-list encoding. The next dependency is the all-list token
locator, not another fixed literal index. Its external theorem must observe
`DirectToken.boundedLiteralListSlot literals position` for every actual canonical
list and overall token position, including empty lists and exhausted searches.

Factor the search control into a four-node restoring count guard and a fixed
four-node outer graph: guard, width comparison, hit selection, and advancement.
The guard copies the actual remaining count, tests zero, and erases only the
temporary copy on either branch. The outer graph sends zero to padding,
positive counts to comparison, misses through advancement back to the guard,
and hits through the actual sign/token selector. This refines the earlier
six-node sketch without changing its interface or introducing input-dependent
control. Charge every internal guard step and every outer graph transition.

Prove the execution by induction on the remaining list, preserving the actual
canonical payload, processed ordinal, remaining length, residual token position,
and exactly 17 retained scratch registers per processed literal. Derive each
indexed field-read premise from that invariant. Do not accept a selected literal,
coverage certificate, or next-state data from a caller. Use one polynomial
envelope in the original encoded input for the retained history and exterior;
do not iterate per-step polynomial bounds and thereby grow their degree.

Before compiling, prepare general guard execution, restoration, raw compilation,
terminal separation and polynomial contracts, with independent zero/positive,
scratch and boundary regressions and an exhaustive public axiom probe. Then
prepare the corresponding complete-loop contracts before compiling that source.
Reuse unchanged verified comparison, advancement and selection evidence.
Neither the restoring guard nor a proof over supplied loop paths completes M230.
Ordered-pair routing, source request recovery, dispatch, Finish, the all-input
builder/reduction, and final root/inventory/publication audits remain downstream.
Publication remains deferred; no row, checkpoint, score, or gate changes.

### M230 all-list lookup execution contracts prepared

The fixed outer graph now has a single back edge from physical advancement to
the restoring guard. Its intended general execution proof inducts on the suffix
of the actual canonical list, derives each field index from the processed prefix,
and carries the exact retained history, tape exterior and charged work steps.
The public entry has no caller-supplied ordinal, remaining count, selected literal
or execution path: it starts at ordinal zero with the actual list length.

Prepared contracts require exact work-machine execution, exact six-step raw
compilation, canonical direct lookup and agreement with the actual encoded list
for every overall position. Independent tests cover mixed literal widths, both
signs, unary terminators, empty input and exhaustion after several misses.
The complete original-input polynomial envelope is the next obligation after
this execution layer; termination or finite fixtures alone earn no runtime credit.
Keep public status unchanged and reuse the verified restoring guard and branches.

### M230 original-input bounds for the complete literal-list lookup

Before cost verification, prepare a single-envelope contract for the actual
cyclic machine: the guard-entry span after k misses is at most
B + k * (100B + 100), where B bounds the original encoded entry. The guard adds
at most count + 1 exterior cells. Each comparison chunk has encoded length at
most 50B + 60; comparison and advancement never increase the exterior. The new
ordinal plus remaining count equals the old sum and the residual never grows,
so the next three-register frame is no larger than the previous frame.

Derive the actual literal-index bound from the canonical payload's encoded
sum, not from the ambient type width or a caller-supplied per-literal bound.
Every node input then fits the same quadratic envelope
Q(B) = B + (B + 1) * (100B + 100). Sum the four already verified component
raw-time polynomials at Q(B), add 18 for the three outer transitions, and
multiply once by the at-most B + 1 loop passes. Bound the final span by
Q(B) plus the hit selector's span polynomial at Q(B).

The complete contract must combine this bound with the actual raw-machine
execution and canonical token result for all lists and positions. Prepare
general cost/execution regressions, independent envelope and empty-list cases,
and all public axiom probes before compilation. No local prefix, finite
termination theorem or repeated composition of loose span polynomials satisfies
this contract. This remains one dependency of the open M230 builder milestone.

### Verified complete literal-list lookup with original-input polynomial bounds

The actual fixed cyclic lookup is now kernel checked. Its public
`BuilderLiteralListSearch.workRunExact` and `run_compile_exact` theorems cover
every canonical bounded-literal list and every overall token position, not a
caller-selected literal index. The invariant derives each field-read index from
the processed prefix, preserves the original payload and retained comparison
history, and advances the actual ordinal, remaining count and residual position.
Empty lists and exhausted searches reach the separate padding endpoint; hits
observe the exact canonical literal token. The public
`workRun_observes_encoding` theorem identifies the result with the corresponding
lookup in the actual encoded literal list.

`BuilderLiteralListSearchBounds.uniform_polynomial_lookup` combines the
actual raw-machine run, the canonical result and one original-input polynomial
runtime bound. Its companion `source_polynomial_bounds` also bounds the final
encoded span. Every node input uses the same quadratic envelope
Q(B) = B + (B + 1) * (100B + 100); the complete loop has at most B + 1 passes.
The literal-value bound comes from the actual canonical payload's encoded sum.
The proof charges each retained comparison chunk once, proves that the next
counter frame does not grow, and includes every internal and outer transition.
It does not iterate per-pass span polynomials, enumerate subsets, or accept a
supplied route/selection certificate.

The restoring guard passed all 28 regressions and all 16 public axiom probes.
The complete lookup passed all 31 regressions and all 15 public axiom probes.
The uniform-bound layer passed all 12 regressions and all 6 public axiom probes.
All 71 regressions and 37 public axiom probes passed in terminal successful
wrappers. The audited closures use only the allowed logical foundations:
no project-specific axiom, `Classical.choice`, `sorry`, or `admit` was added.
The complete execution and cost contracts were prepared before their builds,
including independent mixed-width, sign, terminator, empty-list and exhaustion
fixtures.

Diagnostics were resolved at their actual boundary: the launch manifest needed
the complete reviewed file set; the loop needed its explicit comparison import;
a private node-program equality avoids expanding the composed advancement machine;
the regression needs an explicit empty-list type and endpoint-configuration import;
and arithmetic needs the processed ordinal normalized before treating function
applications as atoms. The bound, theorem statements and premise boundary were
not weakened. Unchanged guard, comparison, advancement, selection and complete
execution evidence were reused for the later layers. No duplicate complete root
build, inventory generation or PNPLabs Lean suite was run for these internal
components; the final M230 integration audits remain mandatory.

Next: reconcile the remaining ordered-pair coordinates, source-derived request
routing and recovery, then compose dispatch, successor and Finish into the
complete all-input formula builder and packaged reduction. The final root,
inventory, source-bound status and publication audits remain required.
M230 is not earned by this lookup dependency alone. Formal artefact coverage
remains 205/207; the risk-weighted proof estimate remains 35%, uncertainty
20–40%; global gates remain 0/5. No checkpoint or publication row is added,
and publication remains deferred on coherent M229.

### Ordered exclusion-pair selection: canonical order before physical binding

Continue M230 at the exclusion clauses of each exactly-one constraint. The
legacy anchor remains the pinned report's SAT NP-completeness dependency and
its Final SAT decision / Accepted package implies P=NP boundary. This closes
the coordinate-to-canonical-pair edge needed by the complete all-input
Cook–Levin formula builder, not a new independent roadmap milestone.

Use the existing increasing-width row selector through the reverse ordinal
T(n) - 1 - q for valid exclusion slots, where T(n) is the canonical pair count.
Invalid slots must map to its exhausted boundary T(n); truncated subtraction
alone would incorrectly turn an invalid request into a hit. Decode a selected
row k and offset t as the ordered pair (n - 2 - k, n - 1 - t). Prove the exact
canonical descending-row clause order for every variable list, including empty
and singleton lists, duplicate variables, all valid slots and every invalid
ordinal. Do not replace clause equality by a permutation or satisfiability
equivalence.

The required source-level contract is
`selectedPair_observes_canonical variables coordinate`: observing the derived
indices in the actual variable list equals its canonical pair-exclusion clause
lookup. Its exactly-one corollary uses the successor clause slot, preserving
the preceding at-least-one clause. Reuse the existing fixed physical row loop
and its complete execution/cost results; expose its actual terminal suffix so
both pair fields can subsequently be read at fixed offsets. No selected pair,
rank map, route certificate, pair list or runtime-sized control is supplied.

Prepare the complete public axiom probe set and general/edge regression
contracts before compilation. Test only the changed coordinate/binding layers;
reuse unchanged row-loop and literal-list evidence. The physical preparation
of the reverse ordinal from actual source registers, extraction of the two
canonical variable fields, source request/recovery and final builder composition
remain explicit downstream obligations. A prepared-frame execution theorem is
not an end-to-end source execution or complete-runtime claim.

No score, coverage row or global gate changes here: formal artefact coverage
205/207; risk-weighted proof estimate 35%, uncertainty 20–40%; global gates
0/5. Publication stays on coherent M229 until the complete capability is earned.

### Verified canonical exclusion-pair mapping and physical row phase

The general reverse-ordinal construction is now kernel checked for every list
size and every pair-exclusion clause slot. `BuilderExclusionPairSelection`
proves equality with the exact canonical ordered clause list, not merely
permutation or satisfiability equivalence. Empty and singleton variable lists,
duplicate variables and all out-of-range slots are covered. Invalid slots are
sent to the exhausted coordinate rather than silently becoming the first hit
through truncated subtraction. The exactly-one corollary retains the preceding
at-least-one clause and selects exclusion clauses at successor slots.

`BuilderExclusionPairRow` reuses the unchanged five-node row machine. Its
`found_attempt` theorem identifies the complete actual terminal nine-register
suffix after any number of row attempts. Fixed suffix offsets recover the
physically decremented remaining count, selected width and residual offset;
`observedPair_eq_selectedPair` proves that the resulting pair is the canonical
one. The observation is gated by the actual terminal state, so an exhausted
history is never decoded as a hit. Complete work/raw execution, tape preservation,
control separation and canonical clause observation are proved.

The `row_polynomial_bounds` and `uniform_polynomial_row_phase` theorems
charge the complete row search and retained history using a quadratic
prepared-frame envelope derived from the original count/ordinal frame's encoded
size. These bounds cover the row phase only. They do not claim executable
construction of the reverse-coordinate frame, variable-field reads or final
source-token dispatch. No selected pair, pair list or execution certificate is
supplied to the fixed row machine.

All 63 regressions and 29 public axiom probes passed in terminal successful
wrappers: 32/12 for the canonical coordinate layer and 31/17 for the physical
row layer. Their closures use only the allowed logical foundations; no project
axiom or classical choice was introduced. The fail-closed axiom probe caught
an arithmetic tactic introducing classical choice over an equivalence; making
the two implications explicit eliminated it without changing the statement.
Other fixes reconciled recursive rewrite targets, existing declaration
namespaces, regression imports and a let-valued theorem type, and explicit
machine-state projection equalities. Source and regression contracts were
kept synchronized. The unchanged successful source build and axiom probes were
reused when only regression imports/type transcription changed.

Next derive the reverse-coordinate frame physically from the actual registers.
A concrete reuse path is to evaluate n*(n+1), use the existing fixed halving
machine at its proved fresh frontier, and compare its quotient against n+q+1.
A smaller quotient means an invalid pair slot; otherwise the actual residual
is T(n)-1-q, including zero for the final pair. That valid branch derives n≥2,
so packing the row frame and decrementing n is safe. This is an implementation
direction, not a theorem already earned here. Its execution, frontier handoff,
branch control and polynomial composition still need proof, followed by actual
variable-field reads, source request/recovery and complete builder composition.

M230 is not earned by this internal dependency. Final root, compiled inventory,
status, clean reproduction and publication audits remain due at full integration.
Formal artefact coverage remains 205/207; risk-weighted proof estimate remains
35%, uncertainty 20–40%; global gates remain 0/5. No checkpoint or publication
row changed, and publication remains deferred on coherent M229.

### Physical exclusion-pair lookup from written count and clause ordinal

Continue the same M230 canonical formula-builder dependency, anchored in the
pinned report's SAT NP-completeness linkage and Final SAT decision / Accepted
package implies P=NP boundary. The next implementation must close reverse-frame
preparation and the complete count/ordinal-to-pair lookup, not add another
caller-supplied coordinate contract.

The actual initial registers are [n, q]. Evaluate n*(n+1), physically halve it,
and compare the written quotient against n+q+1. Prove that the quotient is
T(n)+n and that the comparison's not-less outcome is equivalent to q<T(n).
On that branch, the physically written residual equals T(n)-1-q and n≥2 is
derived. Copy the actual count and residual into [0, 1, residual, n], decrement
the top count and run the existing fixed row loop. The other comparison branch
must reject the invalid ordinal, including every zero/singleton case, without
an unsafe predecessor or a fabricated successful row.

The complete work/raw execution and canonical-observation contract starts from
`endTape (older ++ [variables.length, coordinate]) inside []` and selects
exactly `(atMostOneBoundedClauses variables)[coordinate]?`. This is an explicit
fresh-frontier input contract required by the existing halver; prove each
intermediate frontier handoff. Do not claim an arbitrary exterior or manufacture
a freshness premise later. All count, quotient, comparison, residual, row and
history registers must come from the actual program execution.

Prepare source/type, full public axiom-probe and regression contracts together
for the arithmetic preparation and complete lookup layers. Include first/last
valid slots, strict-versus-equal comparison, all invalid ordinals, empty and
singleton counts, preserved older registers and the final canonical clause
order. Bound the entire preparation-plus-row runtime and retained encoded size
by composition of the existing fixed-phase polynomials, charging every bridge.
Reuse the unchanged row selector, halver and register-expression machinery;
do not add a generic divider, subtractor or second row-search implementation.

The consumers are the new preparation/lookup regression and axiom contracts and
the later source-payload/request composition; no current publication inventory,
status generator, package script or site expectation changes in this internal
step. Actual source-payload operand extraction, variable-field reads, token
routing/recovery and final builder composition remain downstream. Complete root,
inventory, reproduction and publication checks remain due at M230 integration.

Publication stays deferred on coherent M229. Formal artefact coverage remains
205/207; risk-weighted proof estimate remains 35%, uncertainty 20–40%; global
gates remain 0/5. This internal work does not itself earn a checkpoint or row.

### Verified complete polynomial pair lookup from count and clause ordinal

`BuilderExclusionPairPreparation` now physically computes n*(n+1), halves
that written result, constructs n+q+1 and compares the actual operands. Its
kernel-checked quotient identity is T(n)+n. The actual comparator distinguishes
all valid pair slots from invalid ones, including empty/singleton counts and
arbitrarily out-of-range ordinals. On the valid branch its actual residual is
the canonical reverse ordinal, and n≥2 is derived rather than supplied. Every
fixed arithmetic phase has exact work/raw execution, frontier, control and
original-encoded-input polynomial bounds.

`BuilderExclusionPairLookup` composes arithmetic preparation, row-frame
packing and safe decrement, and the existing row selector in one fixed
three-node graph. Its actual input contains only the written count and clause
ordinal after the preserved older registers, at the explicit fresh frontier.
No selected pair, reverse coordinate, successful execution or validity
certificate is supplied. Invalid requests terminate at the comparison branch;
valid requests derive the canonical ordered pair from the actual final
register suffix. `workRun_observes_canonical` proves exact equality with the
pair selected from the canonical exclusion-clause list, for every variable
list and clause ordinal.

The precise decrement handoff was checked rather than assumed: decrement
releases one blank cell outside the register frame. The pack execution contract
now records that cell explicitly. `positive_row_frontier` proves that the
first width-one row attempt consumes it, so the original end-to-end fresh
input/output frontier is preserved without a new premise or cleanup routine.
The complete endpoint contract rejects every invalid ordinal and does not
interpret an exhausted history as a hit.

`source_polynomial_bounds` and `uniform_polynomial_lookup` now include
the full count/ordinal preparation, frame packing/decrement and row search,
all internal and graph bridges, and retained history. These are fixed-phase
polynomial compositions in the original encoded count/ordinal frame, not
iteration of a bound through an unbounded number of phases. The result closes
the previously explicit reverse-frame-preparation gap for this lookup.

All 83 regressions and 44 public axiom probes passed in terminal successful
wrappers: 46/24 for arithmetic preparation and 37/20 for the complete lookup.
The allowed closures contain no project axiom or classical choice. Contracts
were prepared with the source; the released-blank expectation and its general
regression were corrected together before the next run. Other adapter fixes
used the actual namespace, explicit divisor, record layout, named polynomial
aliases and a typed chain-result handoff. The existing arithmetic, halver and
row-machine evidence was reused; no duplicate complete root build or website
proof suite was run.

Next read the two actual variable fields from the materialized source payload.
Keep that payload and history until token selection is complete. Derive reader
offsets from the proved 25-register preparation history and nine-register row
attempts, together with the actual payload schema and any new fixed scratch.
The current lookup produces pair indices; it is not yet an executable
variable-value read, literal-token emission, source-request binding or complete
formula builder. Those steps, recovery and final composition remain open.

M230 is not earned. Final root, inventory, status, clean reproduction and
publication audits remain due at full integration. Formal artefact coverage
remains 205/207; risk-weighted proof estimate remains 35%, uncertainty 20–40%;
global gates remain 0/5. No checkpoint or publication row changed, and
publication remains deferred on coherent M229.

### Actual variable reads from the retained exclusion-pair result

Continue the same M230 canonical formula-builder dependency and pinned-report
SAT NP-completeness / Final SAT decision linkage. The complete count/ordinal
lookup is now proved. The next obligation is physical variable-value access from
the materialized exactly-one payload, without substituting a supplied pair or
discarding and reconstructing the payload.

The source payload puts its count and tag after the reversed variable values.
After a valid lookup, the last attempt has nine registers; its field 3 is the
first index, field 7 is the selected width and field 8 is the row offset.
Derive the retained history length from the actual row execution: the preparation
has 25 registers and each attempted row has nine. Include the two payload-header
registers and every new scratch register in the reader address.

First compute 9*width + firstIndex + 33 with one fixed seven-node expression.
Its six non-root scratch registers, the last nine row registers and the derived
prior history place that address at the actual first variable. Use the existing
runtime indexer to copy its value while preserving the complete payload/history.
The public source-bound theorem must start at the actual lookup result for every
valid clause ordinal, derive its own row witness and field bounds, and identify
the selected canonical pair; an arbitrary supplied history theorem alone is not
the integration result.

Then derive the second field address physically, including the first read's
eight retained registers. Its index is firstIndex + width - offset. Reuse the
actual comparator residual for subtraction and the same runtime indexer. Prove
that the comparator branch is determined by source-derived row bounds, charge
all scratch and bridges, and retain both values for negative-literal token
selection. Final source request/recovery and complete builder composition remain
downstream; no finite-instance substitute or correctness certificate is allowed.

Prepare each source/type, complete public axiom-probe list, independent boundary
fixture and source-layout regression before its targeted build. Consumers are
these new field-read modules and the subsequent token/request composition.
No current inventory, publication row, status generator, package script or site
expectation changes at this internal dependency. Reuse unchanged lookup,
expression, indexed-copy and row evidence. Final root, inventory, reproduction
and publication checks remain due when M230 is complete.

Publication remains deferred on coherent M229. Formal artefact coverage remains
205/207; risk-weighted proof estimate remains 35%, uncertainty 20–40%; global
gates remain 0/5. No checkpoint credit is awarded for an incomplete builder.

### Verified first variable read from the canonical pair-lookup result

`BuilderExclusionPairFirstVariable` now uses one fixed seven-node expression
and the existing runtime indexer to copy the first selected variable from the
actual exactly-one payload. Its address is 9*selectedWidth + firstIndex + 33.
The constant accounts for the two source headers, the preparation history and
the expression's non-root scratch. The variable-length row history is derived
from the actual lookup, not supplied as an independent correctness certificate.
All original payload and history registers are preserved; the phase appends
seven expression registers and the actual copied value.

`source_layout` derives both canonical indices, the strict row-offset bound,
the exact history length and the complete physical layout for every valid source
clause ordinal. These facts are available to the second reader without another
reconstruction of the row witness. `source_read` starts at the actual complete
lookup result and identifies the copied source value. `uniform_source_lookup`
composes the count/ordinal lookup and first read into a fixed machine, proves
the exact raw execution, and charges the complete runtime and final encoded
size in the original source-frame polynomial bound, including the chain bridge.

All 33 regressions and 18 public axiom probes passed in the final terminal
successful wrapper. The closures use only the allowed logical foundations.
The axiom audit caught the arithmetic tactic invoking classical contradiction
on an impossible existential goal; an explicit elimination to False removed
that dependency without changing the statement or machine. Record-layout syntax
and the temporary runner's regression-count assertion were reconciled before the
successful run. Existing lookup, row, expression and indexed-copy evidence was
reused; no complete root build or website proof suite was repeated.

Next physically read the second selected variable and retain both source values
for exclusion-clause token selection. Its address must account for the first
read's eight retained registers and derive subtraction through the actual
comparator residual. Source-request binding, token-preserving recovery,
dispatch/successor/Finish and complete builder/reduction integration remain open.
The estimate of roughly ten substantial remaining integration/release steps is
provisional and does not redefine mathematical completion or award progress.

M230 is not earned. Final root, inventory, status, clean reproduction and
publication audits remain due at full integration. Formal artefact coverage
remains 205/207; risk-weighted proof estimate remains 35%, uncertainty 20–40%;
global gates remain 0/5. No checkpoint or publication row changed, and
publication remains deferred on coherent M229.

### Physical second-variable read and complete pair-value lookup

Continue the same M230 canonical formula-builder dependency and pinned-report
SAT NP-completeness / Final SAT decision linkage. Reuse the verified first
reader and its source-derived layout, both indices and strict row-offset bound.
The next complete interface must physically retain both selected source values,
not substitute a decoded natural-number pair for actual variable-field reads.

After the first read, evaluate 10*selectedWidth + firstIndex + 45 with a fixed
seven-node expression, retaining its six non-root scratch registers. Copy the
actual row offset with a fixed argument expression at the resulting offset.
The comparison's not-less branch is forced by the source-derived row bound;
use its actual residual as the address passed to the runtime indexer. Account
for the two source headers, 25 preparation registers, all nine-register row
attempts, eight first-read registers and ten new registers before the address.
The second phase appends eleven scratch registers and the actual second value.

Prove exact preparation, second-read and composed pair-read work/raw executions,
preserved payload/history and fresh-frontier handoffs. Compose their polynomial
runtime and encoded-size bounds with the already verified count/ordinal lookup.
The source-bound theorem must derive both field bounds and values from
`BuilderExclusionPairFirstVariable.source_layout`. Its runtime machine must not
take a selected index, history-length witness, payload value or correctness
certificate as an extra input. Keep an explicit invalid-ordinal branch at the
complete lookup boundary rather than interpreting a dead or exhausted frame as
a selected pair.

Prepare all public theorem/type and axiom-probe contracts and independent
boundary regressions with the source. Include first/last pair ordinals, unequal
variable values, duplicate source values, offset zero and the final offset in
a row, exact scratch/address accounting and invalid empty/singleton/out-of-range
requests. The consumers are the new second-reader/pair-value interface and
later exclusion-token/request composition. No current status, inventory,
publication-row, package-script or site consumer changes at this internal step.
Reuse unchanged first-reader, lookup, expression, comparison and indexer evidence.

Exact token emission, source request/recovery and final builder integration
remain downstream. M230 is not earned. Final root, inventory, status, clean
reproduction and publication checks remain due at full integration. Publication
stays deferred on coherent M229: formal artefact coverage 205/207; risk-weighted
proof estimate 35%, uncertainty 20–40%; global gates 0/5.

### Verified second-variable reader and complete source-pair value lookup

The second physical reader now derives its address from the retained row
environment, reads the actual second variable field, and preserves the first
value and complete source/history frame. The source-derived strict offset bound
forces the comparison's not-less branch. Its actual residual is
9*selectedWidth + secondIndex + 45; no pair, value or address is supplied as
runtime advice. The second phase retains eleven scratch registers and the
second value, making twenty additional registers for both reads together.

`BuilderExclusionPairSecondVariable.uniform_source_lookup` composes the actual
count/ordinal lookup and both readers for every valid source ordinal, deriving
the canonical pair and final values from the exactly-one payload. It includes
complete original-source polynomial runtime and encoded-size bounds.
`invalid_source_lookup` and `uniform_invalid_source_lookup` reject every
out-of-range ordinal, including empty and singleton source lists, before either
reader runs. The separate two-node lookup graph preserves that rejection at
the global boundary instead of dropping it inside a valid-only chain.

All 56 regressions and 36 public axiom probes passed on the final targeted run.
Eight probes are axiom-free, five use only `propext`, and twenty-three use
`propext` and `Quot.sound`; none uses project axioms or classical choice.
The tests cover exact generic theorem types, source-derived layouts and values,
polynomial bounds, both terminal outcomes and independent arithmetic/boundary
fixtures. Earlier adapter failures were resolved with private configuration
projection equalities and explicit local aliases; no public theorem statement,
runtime program or regression expectation was weakened.

The checked source and regression bytes are retained as verification evidence.
Unchanged first-reader, count/ordinal lookup, expression, comparison and indexer
checks are reused. Final root, complete inventory, clean-reproduction and release
checks remain due when the complete M230 builder is ready; this targeted result
does not replace them.

Next bind exact negative-literal token lookup to the two actual values, preserving
the requested token position and canonical clause markers. Then connect source
requests, cleanup/recovery, token dispatch, cursor advancement and Finish, and
prove the full all-input canonical formula output and packaged polynomial
reduction. M230 is not earned; publication remains deferred. The coherent M229
snapshot stays at formal artefact coverage 205/207, risk-weighted proof estimate
35% with uncertainty 20–40%, and global gates 0/5 closed.

### Exact exclusion literal-body tokens from the retained source values

Continue the same pinned-report SAT NP-completeness / Final SAT decision edge
toward the complete all-input formula builder. Reuse the complete literal-list
token locator rather than construct a second variable-width search procedure.
This substep belongs to exact exclusion-clause emission; it does not close the
whole token-emission integration step or earn M230.

The physical reader result ends in the first value, eleven second-reader scratch
registers and the second value. Once the token-position register is physically
appended, a fixed fourteen-register pack can copy the actual values into the
canonical two-negative-literal payload, followed by ordinal zero, literal count
two and the requested body position. Derive this layout from the existing reader
result; do not insert a position register into the source payload or change the
already verified runtime reader addresses.

Prove one fixed machine reads every literal-body position, including boundaries,
zero-valued and duplicate variables, and padding after the body. Its observed
result must equal the indexed canonical encoded literal list, not merely a
semantically equivalent clause. Preserve true/false/padding as distinct states
through composition and prove complete original-frame polynomial runtime and
encoded-size bounds. The source-layout adapter must derive its scratch width
from the compiled second reader; no token verdict or selected literal is
provided to the runtime machine.

Prepare generic theorem/type probes, axiom probes and independent encoding,
negative-sign, boundary and layout regressions together with the source. Reuse
unchanged pair readers, register pack and complete literal-list lookup evidence.
Only the new proof module, its regression and this existing plan change; no
status, inventory, package-script or website expectation changes are warranted.

Separator and finish selection, physical source-position binding, cleanup/root
recovery, dispatch, cursor advancement, Finish and the complete polynomial
reduction remain downstream. Do not call the literal body the complete clause.
M230 is not earned; publication remains deferred on coherent M229. Formal
artefact coverage remains 205/207; proof estimate 35%, uncertainty 20–40%;
global gates remain 0/5 closed.

### Verified canonical exclusion literal-body tokens

The fixed seven-field pack now copies both actual retained source values into
the canonical two-negative-literal payload and feeds the complete literal-list
locator. Every body position is covered, including the two negative signs,
both variable-width unary encodings, zero-valued and duplicate variables, and
padding beyond the body. True, false and padding remain distinct through the
sequential machine composition.

`BuilderExclusionPairLiteralTokens.workRun_observes_encoding` proves equality
with the indexed canonical encoded literal list.
`uniform_polynomial_lookup` gives the exact compiled run within a single
original-frame polynomial bound. The accompanying size theorem includes the
retained source frame, pack output, locator scratch and exterior tape.
`reader_output_frame` and `reader_body_lookup` connect the existing second
reader's exact output to this body lookup after a physical position register is
appended. The eleven-register width is derived from the second reader, and no
source-reader address or payload layout was changed.

All 49 regressions and 25 public axiom probes passed. Four probes are axiom-free,
five use only `propext`, and sixteen use `propext` and `Quot.sound`; none uses
project axioms or classical choice. Source and regression contracts were
prepared before compilation. The adapter corrections preserved every public
theorem type and independent expectation. For composition, proving the small
generic interface under abstract machine parameters avoided expanding the deep
finite-state encoding; no recursion or resource limit was raised.

Reuse unchanged pair-reader, pack and complete literal-list evidence. This
result is literal-body lookup, not the complete clause: separator, finish and
whole-source position binding remain open. Next classify the actual clause
position against zero and the two-value-derived finish boundary, retain the
five distinct token outcomes, and connect exact scratch cleanup to the body
selector. Final root, inventory, clean-reproduction and release checks remain
due at complete M230 integration.

M230 is not earned; publication remains deferred on the coherent M229 snapshot.
Formal artefact coverage remains 205/207; risk-weighted proof estimate remains
35%, uncertainty 20–40%; global gates remain 0/5 closed.

### Complete exclusion-clause token selection at every physical position

Continue the pinned-report SAT NP-completeness / Final SAT decision dependency
toward the complete all-input Cook–Levin formula builder. Reuse the verified
source-value readers, canonical literal-body selector, expression compiler,
comparison residual and bounded register eraser. The required result is one
fixed machine whose observed result equals the exact indexed canonical clause,
including separator, both negative literals, finish and padding, for all source
values and positions. No branch or token verdict is supplied as runtime advice.

The input frame is the actual first value, eleven retained reader registers,
second value and an actual clause-position register. Test zero for separator.
Otherwise derive the finish position as firstValue + secondValue + 5 with a
fixed expression, copy the physical position and compare these two operands.
A position beyond that boundary is padding; the actual zero residual identifies
finish. The remaining positive positions enter the literal body only after
erasing all nine boundary scratch registers and decrementing the disposable
position register. Preserve the original source payload and older root frame.

Use a small boundary module for exact preparation/comparison and its source
bounds, then compose the full token selector. Keep true, false, separator, finish
and padding in five distinct finite-control outcomes. Separator and finish must
be stable no-rule endpoints, not caller-selected token tags. Account for exact
work/raw execution, all graph bridges, scratch erasure, the freed decrement cell,
and total encoded-size polynomial bounds in one original input envelope.

Prepare the theorem/type and axiom contracts with both modules and regressions.
Include independent canonical encoding, sign, zero-variable, duplicate-variable,
first/last body-token, exact finish, first padding and large-position cases, plus
endpoint distinctness and no-rule checks. The affected consumers are only these
new interfaces and their regressions; current status, inventory, package scripts
and PNPLabs remain unchanged. Reuse verified dependency evidence and run only
the changed chain and focused checks before any complete milestone release gates.

Whole-source position binding, root recovery, output dispatch, cursor advancement,
Finish and the final canonical formula/reduction theorem remain downstream.
This selector alone does not earn M230 or the complete-builder checkpoint.
Publication stays deferred on coherent M229: formal artefact coverage 205/207;
risk-weighted proof estimate 35%, uncertainty 20–40%; global gates 0/5 closed.

### Verified all-position exclusion-clause token selection

The fixed eight-node clause selector is now kernel checked. It reads the actual
retained first and second source values and physical clause position, derives
the exact finish boundary, and returns the canonical token for every position:
separator, true, false, finish, or padding. Separator and finish occupy distinct
stable no-rule endpoints; no token or branch verdict is supplied to the program.

The literal-body path erases the nine boundary scratch registers and decrements
the disposable positive position before invoking the already verified actual-pair
literal selector. The exact tape-span identity includes the erased cells and
the freed decrement cell. The complete selector has checked raw execution and
polynomial runtime/output-span bounds in one original-input envelope, including
all graph bridges and all positions beyond the clause.

New compiled interfaces:

- `BuilderExclusionClauseBoundary.workRunExact`,
  `residual_suffix`, and `source_polynomial_bounds`.
- `BuilderExclusionClauseTokenSelector.workRunExact`,
  `run_compile_exact`, `canonical_result`, and
  `workRun_observes_encoding`.
- `body_input_span`, `source_polynomial_bounds`, and
  `uniform_polynomial_lookup` for the complete clause selector.
- Explicit no-rule and distinct-state contracts for all five outcomes.

All 86 regressions and 43 public axiom probes passed across the two new modules.
Seven probes are axiom-free, four use only `propext`, and thirty-two use only
`propext` and `Quot.sound`; none use project axioms or classical choice.
Independent fixtures cover canonical full encoding, zero and duplicate source
values, both literal boundaries, separator, finish, first padding and an oversized
position. The generalized contracts cover every valid source value and position.

Verification reused unchanged source-reader and literal-body evidence, then reused
the checked boundary module while validating the full selector. No duplicate
complete Lean suite, inventory extraction or publication cycle was run. Normal
root, axiom/inventory, PR, merge and clean-reproduction gates remain due when the
complete M230 theorem is ready.

Next physically bind the preserved complete-source token request to this selector,
then preserve its five outcomes through scratch cleanup and root recovery.
Dispatch, cursor advancement, Finish, canonical all-input formula output and the
complete polynomial reduction still remain. M230 is not earned; the complete
builder checkpoint stays open and publication remains deferred. The coherent
public baseline remains M229: formal artefact coverage 205/207; risk-weighted
proof estimate 35%, uncertainty 20–40%; global gates 0/5 closed.

### Active source-bound token-request contract

Continue the pinned-report SAT NP-completeness / Final SAT decision dependency.
The complete clause selector is now verified, but its physical position must be
bound to the original source cursor. Implement one verifier-fixed request machine
from the real cursor, reusing the complete five-family payload and clause-coordinate
pipeline. No payload, clause ordinal, token position or branch verdict is supplied.

The preserved coordinate frame contains the original index, token width and first
division quotient at fixed root ordinals. Copy those actual fields through the
variable-length payload history. Reuse the quotient: multiply it by the width,
compare that product with the original index, and prove that the actual comparison
residual is the original index modulo the token width. Do not rerun the divider or
erase and reconstruct the canonical payload.

Append the physical request suffix `[clauseIndex, tokenPosition]`, retaining the
existing payload and explicitly accounting for the fixed intervening scratch.
The target source theorem starts at `BuilderCursorSource.cursorTape`, preserves
the source/output interior, and ends with the canonical source payload plus a
derived request whose position is `index % BuilderDividerOperands.width problem`.
Only the existing body guard and balanced-cursor invariant may be premises.
Prove exact work and raw execution, deterministic terminal control, the exact
retained-frame/scratch layout, and polynomial runtime and full allocated-register
plus exterior workspace bounds in the encoded original input length for every
input and all five payload families. The arbitrary already-written output is
preserved; bounding that accumulated output belongs to the complete builder.

Prepare source/type, axiom-closure and independent arithmetic/layout regressions
before compilation. The affected consumers are the new request interface and its
regressions; do not change current status, theorem inventories or public claims
for an incomplete builder. Reuse unchanged payload, coordinate and selector checks.
Source-bound token dispatch, outcome-preserving root recovery, successor, Finish,
canonical whole-formula output and the complete polynomial reduction remain
downstream. This is part of source-request binding, not a reduction in the rough
remaining-step count until that integration is complete.

M230 remains unearned and publication is deferred on coherent M229: formal artefact
coverage 205/207; risk-weighted proof estimate 35%, uncertainty 20–40%; global gates
0/5 closed. No local component earns a publication row, gate or weighted checkpoint.

### Verified canonical source-token request

Implemented [the source-token request machine](../../lean/PNP/Concrete/CookLevinBuilderSourceTokenRequest.lean)
and its [independent regression contracts](../../lean-regression/PNPConcreteCookLevinBuilderSourceTokenRequest.lean).
The verifier-fixed machine starts at the actual source cursor, runs the complete
five-family payload pipeline, and retains its canonical payload. It reads the
preserved index, token width and original division quotient using fixed root
locators. It does not repeat the division or accept supplied request data.

The eight fixed continuation phases copy the width and quotient, multiply them,
copy the original index, copy the product into the correct operand position,
compare, copy the actual clause index, and copy the derived token remainder.
The restored-coordinate comparator keeps the coordinate on its less-than branch;
it is not an absolute-difference operator. The machine therefore physically
orders the final comparison as `index` against `width * quotient`. The proved
division reconstruction puts it on the subtracting branch and makes its actual
result exactly `index % width`, including the zero-remainder case.

The terminal register frame is the retained source history, the canonical local
constraint payload, nine explicitly accounted scratch registers, and the physical
request `[(index / width) % clauseWidth, index % width]`. The original source/output
interior is preserved. Exact work execution, raw compiled execution, deterministic
terminal control and source-input polynomial runtime/allocated-workspace bounds
are kernel checked for every input and all five payload families. These workspace
bounds cover the complete materialized register word and exterior; they do not
pretend to bound arbitrary already-written output without the later builder-loop
invariant.

All 50 regressions and 24 public axiom probes passed in a terminal zero-status
targeted run. Four public declarations are axiom-free, two use only `propext`,
and eighteen use `propext` plus `Quot.sound`. No project axiom or
`Classical.choice` enters these theorem closures. The regression contract covers
the source cursor, all fixed source fields, request and scratch layout, all eight
continuation phases, exact execution, original-input polynomial bounds, and the
comparator's strict/equal/zero arithmetic boundaries. Earlier unsuccessful
adapter drafts are not verification evidence. Existing selector and payload
evidence is reused; this is not another full core proof build or website cycle.

Next consume this physically derived request through the token selectors and
preserve the selected outcome through scratch cleanup and root recovery. The
controller loop, accumulated-output bound, canonical all-input formula theorem,
complete polynomial reduction, final release checks and major publication remain.
The rough seven-work-package estimate is unchanged: this advances the first
package but does not complete source-to-token binding. M230 is not earned and
publication remains deferred. The coherent public baseline remains M229: formal
artefact coverage 205/207; risk-weighted proof estimate 35%, uncertainty 20–40%;
global gates 0/5 closed.

### Active complete literal-clause selector and source binding

Continue the pinned-report SAT NP-completeness / Final SAT decision dependency.
The next missing edge is complete literal-list lookup to complete canonical
clause lookup for requirement, implication and the positive exactly-one clause.
The existing complete exclusion-pair selector remains reusable for negative
exactly-one clauses. The full M230 builder and reduction targets are unchanged.

Implement `BuilderLiteralClauseTokenSelector` for every bounded literal list and
every physical clause-token position, including empty clauses and positions past
the end. A fixed wrapper tests the initial separator position, physically
decrements a positive position, and enters the already verified complete list
search. When that search exhausts the list, read its actual remaining position:
zero means the clause's finishing marker, and a positive residual means padding.
Do not supply or recompute a total body-width verdict to the executable machine.

The target theorem observes exactly
`(encodeClauseTokens (BoundedClause.emit literals))[position]?` after a proved
raw execution from the actual encoded-list/count/position frame. Prove five
distinct stable token outcomes, full work and compiled execution, and polynomial
runtime plus complete register/exterior workspace bounds in the encoded entry
span. Preserve the arbitrary source/output interior explicitly. Derive the
exhausted frame and residual from the existing loop's induction, not from a
caller-supplied selected literal, final position or completeness certificate.

Prepare exact theorem/type, axiom-closure and independent grammar-boundary
regressions alongside the implementation. Cover empty clauses, both signs,
zero-valued variables, every body position, the exact finishing position and
padding. The new source, its regression file and this plan are the immediate
consumers. Reuse unchanged literal-list search, source-request and exclusion
selector evidence; do not regenerate current inventories or public status for
this unfinished integration.

After the generic clause selector, connect each canonical payload kind and its
physically derived clause/token request to the appropriate selector. That
source-level connection, outcome-preserving scratch/root recovery, the full
controller/loop, accumulated-output bound, exact canonical formula theorem and
complete polynomial reduction remain required. A standalone clause selector does
not finish source-to-token binding or reduce the rough seven-work-package count.

M230 remains unearned and publication remains deferred on coherent M229: formal
artefact coverage 205/207; risk-weighted proof estimate 35%, uncertainty 20–40%;
global gates 0/5 closed. No local component earns a weighted checkpoint or row.

### Verified complete arbitrary-list clause selector

Implemented [the complete literal-clause selector](../../lean/PNP/Concrete/CookLevinBuilderLiteralClauseTokenSelector.lean)
and its [independent regression contracts](../../lean-regression/PNPConcreteCookLevinBuilderLiteralClauseTokenSelector.lean).
One six-node finite wrapper handles every bounded literal list and every physical
clause-token position. It reads the initial position for the separator branch,
physically decrements a positive position, and enters the already verified
complete literal-list search. The search's actual exhausted suffix contains the
remaining position after all literal widths have been consumed. A physical zero
test on that suffix distinguishes the exact finish position from padding.

The machine is not supplied a total clause width, selected literal, branch
verdict, completion certificate or token. Width-based cases appear only in the
proof-level specification. Requirements, implications and positive exactly-one
clauses can use this general interface once their actual source payloads are
adapted to its physical literal-list entry frame. The existing exclusion-pair
selector remains available for negative exactly-one clauses.

The wrapper has five pairwise distinct stable control outcomes: true bit, false
bit, separator, finish and padding. Exposing exhaustion as a continuation changes
only the search machine's declared endpoint. A generic successful-step transport
explicitly accounts for the machine's halt check and proves that the relabelled
endpoints cannot cut off an existing transition because those states have no
rules. The final true-bit endpoint is likewise shown to be rule-free.

Exact work and compiled raw execution, equality with every token of the unchanged
canonical clause encoding, and polynomial runtime plus complete register/exterior
workspace bounds are kernel checked. The decrement transfers one cell from the
position register to blank exterior space, preserving the total entry span.
The arbitrary source/output interior is preserved; bounding accumulated formula
output still belongs to the complete builder-loop invariant.

All 56 regressions and 24 public-theorem axiom probes passed in a terminal
zero-status targeted run. Three public declarations are axiom-free, three use
only `propext`, and eighteen use `propext` plus `Quot.sound`. No project axiom
or `Classical.choice` enters these closures. The regressions cover the universal
execution and bound contracts, independent literal grammar, both signs,
zero-valued variables, empty clauses, every body position, exact finish and
padding. Proof-adapter corrections and an explicit empty-clause type annotation
did not weaken a theorem or test expectation. Unchanged predecessor evidence
was reused; no complete core or website rebuild was performed.

Next bind every canonical source payload kind and the already derived physical
clause/token request to the appropriate complete selector. Outcome-preserving
scratch cleanup and root recovery, the controller/loop, exact whole-formula output,
whole-builder polynomial bounds and the packaged reduction remain downstream.
This completes the generic clause-selector dependency, not the first complete
source-to-token work package. The rough seven-work-package estimate is unchanged.
M230 is not earned and publication remains deferred on coherent M229: formal
artefact coverage 205/207; risk-weighted proof estimate 35%, uncertainty 20–40%;
global gates 0/5 closed.

### Source-payload literal-token integration plan

The dependency anchor remains the pinned manuscript's SAT NP-completeness and
Final SAT decision construction, through the complete Cook-Levin builder
checkpoint. The generic clause selector is now verified, but its canonical
literal-list frame is not the actual source payload. This change closes the
literal-reading edge of the source-to-token work package; it does not close that
whole package or earn M230.

Implement one fixed-schema literal-token adapter for every valid literal ordinal
of a requirement, implication premise, implication conclusion and positive
exactly-one clause. Read the original encoded payload with the existing indexed
field reader. The machine depends only on the finite payload kind, never on the
source list length, ordinal, selected literal, token or supplied correctness
certificate. Its theorem domain describes the physical loop frame; the enclosing
source dispatcher and loop must subsequently derive that frame and index validity.

Preserve the original payload, its nine-register request gap, clause index and
original token position. Preserve earlier loop history, whose length is seventeen
registers per visited literal. Address the runtime ordinal with a fixed affine
field offset. Read every implication premise in original order, negate its
actual sign, and read the separately stored conclusion last. Positive exactly-one
literals use the positive sign specified by the clause grammar. Do not construct
another copy of the complete canonical clause list merely to reuse an interface.

The main execution contract is universal over the source literal/list, every
valid ordinal, the physical request and loop registers, arbitrary retained
interior data and exterior workspace:

```text
workRunExact? (machine source.kind) (workSteps source ...)
  (initialConfiguration source ...) = some (finalConfiguration source ...)
observe (finalConfiguration source ...) =
  DirectToken.literalSlot source.selectedLiteral.emit literalPosition
```

Prove exact work and compiled raw execution, deterministic and stable bit/padding
outcomes, preservation of the source/request frame, and polynomial runtime plus
register/exterior bounds in the encoded entry span. The arbitrary preserved
interior is not falsely bounded by a local scratch theorem. End-to-end accumulated
output size still belongs to the full builder invariant.

Producer and expectation changes are one changeset: add the adapter and its
universal theorem-type, canonical sign/order, boundary and axiom-closure regression
contracts together. Build the exact new Lake target before the imported regression
and focused axiom probes. Reuse the unchanged reader, list-selector and source
request evidence; run only these targeted checks and documentation-link/diff
checks for this internal integration. No status, public theorem-pin set, progress
ledger, generated report, workflow fixture or website value changes at this
intermediate step.

Remaining downstream work is actual source-level dispatch and guarded clause
search, outcome-preserving scratch cleanup/root recovery, the full controller
loop, exact whole-formula output, whole-builder polynomial bounds and the packaged
reduction, then final core verification/merge and a major publication batch.
The rough seven-work-package estimate is unchanged. Publication is deferred on
the coherent M229 baseline: formal artefact coverage 205/207; risk-weighted proof
estimate 35%, uncertainty 20–40%; global gates 0/5 closed.

### Verified source-payload literal-token adapter

Implemented [the source-payload literal-token adapter](../../lean/PNP/Concrete/CookLevinBuilderPayloadLiteralTokenSelector.lean)
and its [independent regression contracts](../../lean-regression/PNPConcreteCookLevinBuilderPayloadLiteralTokenSelector.lean).
The finite machine for each of four fixed schemas reads the actual runtime
ordinal and source payload fields. It covers every valid requirement literal,
implication premise, implication conclusion and positive exactly-one literal,
not a fixed list length or finite set of token positions.

The canonical payload and original request remain on tape. Fixed affine field
addresses account for the preserved request gap and seventeen registers per
previously visited literal. Implication premises retain their original order and
their actual signs are physically complemented. The separately stored conclusion
is read from its original header only after the premises. Explicit canonical-order
theorems tie those selections to the unchanged negated-premises-then-conclusion
clause. Positive exactly-one signs come from the canonical clause grammar.

A four-step finite machine complements the final Boolean unary register in place.
The prepared sign, actual variable index and actual literal-relative position feed
the existing scalar token selector. Exact work and compiled raw execution,
canonical bit/padding results, deterministic stable endpoints, source/request-frame
preservation and polynomial register/exterior plus runtime bounds are kernel
checked. Arbitrary retained interior data is preserved; its accumulated output
bound still belongs to the complete formula-builder invariant.

All 59 regressions and 29 public-theorem axiom probes passed in a terminal
zero-status targeted run. Two declarations are axiom-free, five use only
`propext`, and twenty-two use `propext` plus `Quot.sound`. No project axiom or
`Classical.choice` enters these closures. The regressions include universal
execution and bound contracts, independent field offsets, both signs, zero
variables, implication order, empty-premise conclusions, literal-token boundaries
and exact retained physical frames. Compiler and regression-adapter corrections
did not weaken the theorem statements or their intended expectations.

This is the valid-ordinal literal-reading primitive, not a complete source-bound
clause selector. Next compose it with the physical kind dispatch and guarded
source-clause search so those components derive its frame and valid ordinal.
Outcome-preserving scratch cleanup/root recovery, the full controller loop,
exact whole-formula output, whole-builder polynomial bounds and the packaged
reduction remain downstream. The rough seven-work-package estimate is unchanged.

M230 is not earned and publication remains deferred on coherent M229: formal
artefact coverage 205/207; risk-weighted proof estimate 35%, uncertainty 20–40%;
global gates 0/5 closed. Unchanged predecessor evidence was reused; no complete
core or website rebuild was performed.

### Guarded source-clause search integration plan

Continue the pinned manuscript SAT NP-completeness and Final SAT decision
dependency through the complete Cook-Levin builder checkpoint. The verified
source-payload adapter reads every valid literal ordinal, but the enclosing
machine must still derive that ordinal and its physical context from the actual
source payload and clause-token request.

Build the source-bound width comparison and guarded cyclic search, retaining the
original payload and request. Each comparison reads the current actual variable
index, constructs its index-plus-two literal width and compares the actual
remaining token position. Its seventeen-register chunk has the same control
layout as the existing list search, but its address-scratch values depend on one
of the four fixed payload schemas. Generalize the execution contract of the
existing fixed advance machine over arbitrary intermediate scratch contents of
that length; do not replace its control table or assume the old literal-list
address constants. A miss must physically copy/increment the ordinal,
copy/decrement the positive remaining count and copy the actual residual.

On a hit, the existing fixed fourteen-register eraser restores the pre-comparison
loop frame, then the verified payload-literal adapter produces the canonical bit.
This keeps source reading bound to physical registers and avoids copying a second
complete canonical clause list. The source and request survive both branches.
The implication loop counts its conclusion as the last literal: a physical
remaining-count test selects that header field only at the final iteration,
while earlier iterations read and negate the actual premises. Empty and exhausted
loops retain the actual residual for finish versus padding; the clause wrapper
also handles the leading separator.

The complete source-search theorem must quantify over arbitrary source lists and
every token position. Its execution proof must derive positive-count/index
validity and the selected schema from the physical guard; it may not take a
selected literal, selected ordinal, token, width verdict, branch certificate or
caller-supplied completeness premise as executable input. The source-level
dispatcher must ultimately derive its initial count and kind from the actual
payload and source-bound request, including the separate existing negative-pair
route for nonzero exactly-one clause indices.

Prove exact work/raw execution, canonical result, deterministic stable outcomes,
history/frame preservation and whole-search polynomial bounds. Charge the
retained comparison chunks against one original-input envelope and the bounded
number of literal visits; do not obtain a false polynomial claim by iterating a
loose polynomial once per runtime loop iteration.

Prepare the new comparison/advance/search source and its matching universal,
independent arithmetic, boundary, sign/order and axiom contracts together.
Verify targeted modules before the complete composed search and preserve
unchanged predecessor evidence. No complete root, inventory, report or website
cycle is warranted until the actual full-builder integration boundary is reached.
Existing public status and immutable historical artifacts are unchanged.

The larger source-to-token work package is still open until physical kind/count
dispatch, clause search and all source-request bindings compose. Cleanup/root
recovery, the complete controller loop, exact whole-formula output, total encoded
polynomial bounds, the packaged reduction and final verification/publication remain
downstream. M230 remains unearned; the rough seven-work-package estimate is
unchanged. Publication is deferred on M229: formal artefact coverage 205/207;
risk-weighted proof estimate 35%, uncertainty 20–40%; global gates 0/5 closed.

### Verified source-bound comparison and hit continuation

The guarded source-search integration now has three verified physical components.
`BuilderPayloadSearchAdvance` reuses the existing fixed cursor machine over any
fourteen-register intermediate scratch frame. It preserves the original registers,
increments the actual ordinal, decrements the positive remaining count and copies
the actual residual. Its 27 regressions and 17 public-theorem axiom probes passed.

`BuilderPayloadSearchComparison` reads the actual variable index using each fixed
source-payload layout, computes its index-plus-two width and compares the physical
residual position. Its seventeen-register result fits the cursor without assuming
the old canonical-list address constants. The retained chunk is bounded by the old
chunk plus thirty cells, supporting one original-input envelope for the future
loop. Its 40 regressions and 26 public-theorem axiom probes passed.

`BuilderPayloadSearchHit` erases exactly the fourteen comparison scratch registers
and restores the actual source/request/cursor frame before invoking the verified
literal selector. Erasure conserves physical span: cleared registers become blank
exterior rather than disappearing from the space accounting. Exact work/raw
execution, canonical token equality, stable true/false/padding outcomes, retained
frame preservation and polynomial bounds are verified. The
`comparison_hit_workRunExact` theorem links the physical accepting comparison
directly to the hit continuation. Its branch inequality is not an executable
supplied verdict. All 24 regressions and 18 public-theorem axiom probes passed.

Together these components have 91 passing regressions and 61 axiom probes:
nine axiom-free, nine using only `propext`, and forty-three using `propext` and
`Quot.sound`. No project axiom or `Classical.choice` occurs in these closures.
Unchanged predecessor evidence was reused; no complete root, inventory, report
or website rebuild was run for this internal integration.

Next derive the loop's positive-count and final-conclusion branches from physical
count guards, and compose the cyclic search over arbitrary source lists and token
positions. For implications the remaining count includes the conclusion: one
selects the conclusion header, and larger counts select negated premises. The
entry dispatcher must still derive source kind and count from the actual payload.
No caller-supplied ordinal, hit verdict or completeness certificate may replace
these guards. Bound all retained iterations against one original-input envelope.

The first larger source-to-token work package remains open. Cleanup/root recovery,
the full controller loop, exact whole-formula output, total polynomial construction
and packaged reduction, final core verification, and major publication/deployment
remain downstream. The rough seven uneven work packages are not a time estimate.

M230 and the complete-builder checkpoint remain unearned. Publication is deferred
on coherent M229: formal artefact coverage 205/207; risk-weighted proof estimate
35%, uncertainty 20–40%; global gates 0/5 closed.

### Guarded arbitrary-source loop construction

Continue the pinned manuscript SAT NP-completeness dependency through the actual
source-to-token entry. The newly checked comparison, cursor and hit continuation
must now be connected under physical guards over arbitrary source lists.

First implement `BuilderPayloadConclusionGuard`, a fixed restoring count-one
test. Its exact execution quantifies over every ordinal, remaining count, token
position, retained register frame and tape exterior. Its accepting-state theorem
must be equivalent to `count = 1`, and rejection to `count ≠ 1`. Together with
the existing physical positive-count guard and `ordinal + count = length + 1`,
this derives the final implication-conclusion ordinal or a valid premise index.
The count is read, tested and restored; no branch bit is executable input.

Then compose one cyclic search for each fixed source family: a requirement, an
implication's negated premises followed by its conclusion, and an exactly-one
positive clause. The loop must quantify over arbitrary source lists and every
token position, derive its valid ordinal from the guarded count invariant, and
retain the actual original source and request. For implications, only the physical
last-count branch may use the conclusion header. All other nonempty iterations
read the next actual premise and complement its sign. Runtime list lengths,
variable indices, literal data and verdicts must never select the finite program.

On each miss, append the checked comparison chunk, advance the physical frame,
and prove the remaining count decreases. On a hit, use the checked restoring
selection path. Exhaustion must preserve the actual residual for finish versus
padding. Prove the full loop result equals the corresponding canonical literal
body token, together with exact work/raw execution and one original-input
polynomial space/time envelope. Do not iterate a loose polynomial per loop visit.

The clause wrapper and payload/request-bound outer source dispatcher remain part
of this same open source-to-token package. A count-one guard alone is not an earned
roadmap milestone or publication trigger. M230 remains open; formal artefact
coverage is 205/207, risk-weighted proof estimate 35% with uncertainty 20–40%,
and global gates 0/5 closed. The rough seven uneven major work packages remain.

### Verified complete source-body execution

The arbitrary-source search now composes the physical count guards, actual
source mapping, fixed seven-node control graph and complete body-loop induction.
`BuilderPayloadConclusionGuard` passed 24 regressions and 16 axiom probes;
`BuilderPayloadSearchSource` passed 17 and 10; and
`BuilderPayloadSourceSearchControl` passed 39 and 29.

`BuilderPayloadSourceSearch.workRun_observes_body` constructs a terminating
execution from every actual constraint body, request and token position. It
derives each adapter from the consumed prefix of that body, returns the exact
canonical token outcome, and retains the original source/request prefix.
Exhaustion leaves the final ordinal equal to the actual body length, the count
zero, and the residual equal to the initial position minus the complete body
width. `run_compile_observes_body` gives the same result in the raw finite
machine with the exact sixfold simulation factor. Seven regressions and all
three public-theorem axiom probes passed for this complete-body module.

Together these four components passed 87 regressions and 58 axiom probes:
24 axiom-free, five using only `propext`, and 29 using `propext` and
`Quot.sound`. None of these theorem closures uses project axioms or
`Classical.choice`. Unchanged predecessor checks were reused.

Next prove a single original-input polynomial envelope for the full loop,
not merely finite termination. Bound actual source indices from the encoded
payload, retained history once per miss, and every leaf operation against the
same envelope. Any bounded execution witness must be constructed internally;
do not select one using a new assumption or a supplied runtime certificate.
The clause wrapper and actual payload/request dispatcher still belong to this
same open source-to-token work package. Cleanup/root recovery, full builder
control, exact whole-formula output, complete polynomial reduction, final core
verification and major publication/deployment remain downstream.

M230 and the fixed complete-builder checkpoint remain unearned. Defer PNPLabs
publication: this integration has not yet completed the source-to-token package
or changed the published bottom line. Formal artefact coverage remains 205/207;
risk-weighted proof completion remains 35%, uncertainty 20–40%; global gates
remain 0/5 closed. The estimate is still seven uneven major work packages,
including publication/deployment, and is not a time estimate.

### Uniform source-search polynomial bound

Continue the pinned manuscript SAT NP-completeness construction through the
complete source-body lookup. The execution theorem already covers every actual
constraint body and token position; the next obligation is its total encoded-input
polynomial time and retained-space bound.

Extend the existing constructive loop proof with internal cost evidence for its
empty, hit and miss cases. Preserve the existing execution, canonical-output,
retention and exhaustion theorem interfaces. The cost evidence is produced by
that proof, not supplied to the runtime machine or used as mathematical authority.
Bound all visits against one original-input envelope: actual source indices from
the encoded payload, constant-size history per miss, two restoring guards per
nonempty visit, nonincreasing residuals, and a strictly decreasing remaining count.
Sum fixed-kind leaf cost polynomials at the same envelope; do not iterate them.

The changed producer is the loop proof's internally constructed witness. Its
consumers are the existing exact work/raw theorem contracts and the new cost-trace
and polynomial-bound regressions and axiom probes. Update these type/name
expectations before each targeted check. The machine, source mapping, guards,
comparison, cursor and hit implementations stay unchanged and reuse their exact
successful evidence. No website, inventory or milestone-credit update is warranted
until the complete source-to-token and full-builder boundaries are closed.

### Verified single-envelope source-search bound

The full source-body search now has a single original-input polynomial bound,
in addition to the exact execution theorem. The trace extension in
[`BuilderPayloadSourceSearch`](../../lean/PNP/Concrete/CookLevinBuilderPayloadSourceSearch.lean)
constructs empty, hit and miss cost evidence inside the original execution
proof. Its public canonical-token, retained-request and exhausted-frame
contracts remain unchanged.

[`BuilderPayloadSourceSearchEnvelope`](../../lean/PNP/Concrete/CookLevinBuilderPayloadSourceSearchEnvelope.lean)
bounds actual source indices by their encoded payload, not by semantic width.
It charges each newly retained history chunk once and evaluates every leaf
cost polynomial at the same original-input envelope. The number of remaining
entries strictly decreases; leaf polynomials are summed, never iterated.

[`BuilderPayloadSourceSearchBounds`](../../lean/PNP/Concrete/CookLevinBuilderPayloadSourceSearchBounds.lean)
proves the complete visit and trace bounds. Its `source_polynomial_bounds`
and `run_compile_polynomial_bound` construct the full execution and give
the exact canonical token, retained original request, exact exhausted residual,
final-space bound and total raw-time bound together. No cost trace, selected
literal, supplied execution or correctness certificate is a public premise.

The trace, envelope and complete-bound components passed 8, 16 and 6 regression
contracts respectively, and 4, 13 and 4 public-theorem axiom probes. The combined
30 regressions and 21 axiom probes include two axiom-free results, one using
only `propext`, and 18 using `propext` and `Quot.sound`. None uses project
axioms or `Classical.choice`. The axiom audit caught a generated classical
decision procedure in a scalar conjunction; explicit constructive conjunction
proofs removed it without weakening the theorem. Exact unchanged predecessor
evidence was reused rather than rebuilding the complete proof or website suite.

Next connect the clause wrapper (leading separator, finish and padding) and
actual source/request dispatcher, including absent-source branches and the
already verified negative-pair route. These remain in the same open
source-to-token package. Cleanup/root recovery, complete builder control,
exact whole-formula output, the packaged polynomial reduction, final core
verification and major publication/deployment remain downstream.

M230 and the fixed complete-builder checkpoint remain unearned. Defer PNPLabs
publication until the major capability changes the public bottom line. Formal
artefact coverage remains 205/207; risk-weighted proof completion remains 35%,
uncertainty 20–40%; global gates remain 0/5 closed. The working estimate remains
seven uneven major work packages, including publication/deployment, not an ETA.

### Complete actual-source body-clause lookup

Continue the pinned manuscript SAT NP-completeness construction through the
complete clause layer, not another fixed token position. Compose the verified
actual-source body search with the canonical separator, finish and padding
semantics already established by `BuilderLiteralClauseTokenSelector`.

For every actual local constraint, request and clause-token position, construct
the six-node source-family wrapper, derive its body execution internally and
prove that its observed result is exactly
`(encodeClauseTokens (BoundedClause.emit (BuilderPayloadSearchSource.body constraint)))[position]?`.
Retain the original source/request prefix. Derive finish versus padding from the
search's actual exhausted residual; never accept a supplied width verdict, token,
literal, execution or correctness certificate as a public theorem premise.
Carry the original encoded-input polynomial bound through the wrapper, charging
at most 72 additional raw steps and preserving the source-search space bound.

Prepare the graph well-formedness, stable terminal states, canonical observation,
exact work/raw execution, retained-request and polynomial-bound contracts before
the targeted build. Include independent empty-body separator/finish/padding
regressions and fixed polynomial-shape checks. Audit every public theorem closure.
Reuse unchanged actual-source search and canonical clause semantics; do not run
the whole proof or website suite for this isolated composition.

This completes only the source-body/first-clause route when verified. The outer
actual source and clause-index dispatcher must still combine it with absent-source
branches and the previously verified negative-pair route. Cleanup/root recovery,
complete formula construction, exact output, the full polynomial reduction and
final core/publication checks remain downstream. M230 and the fixed complete-builder
checkpoint remain open; defer PNPLabs publication. Formal artefact coverage remains
205/207; risk-weighted proof completion remains 35%, uncertainty 20–40%; global
gates remain 0/5 closed. No milestone or weighted progress credit is claimed here.

### Verified actual-source body-clause wrapper

[`BuilderPayloadClauseTokenSelector`](../../lean/PNP/Concrete/CookLevinBuilderPayloadClauseTokenSelector.lean)
now wraps the complete actual-source search with the canonical clause boundary
semantics. Its fixed source-family graph handles separator, true/false literal
bits, finish and padding. Finish versus padding is derived from the actual
exhausted residual, including the empty positive-body clause.

`workRun_polynomial_lookup` constructs the complete execution from the actual
source, request and position. `uniform_polynomial_lookup` gives the compiled
raw-machine execution, exact canonical encoded clause token, retained original
source/request prefix, final-space bound and total polynomial runtime together.
Neither public theorem accepts a supplied execution, literal, width verdict or
correctness certificate. The wrapper adds at most 72 raw control steps to the
verified body search and evaluates one source-search space polynomial.

All 20 regression contracts and 15 public-theorem axiom probes passed. Three
closures are axiom-free, one uses only `propext`, and eleven use `propext`
and `Quot.sound`; none uses project axioms or `Classical.choice`. The tests
include empty-body separator/finish/padding and fixed polynomial-shape checks.
Unchanged search and canonical-clause evidence was reused.

Next close the outer actual-source and clause-index dispatcher, combining this
body-clause route with absent-source branches and the already verified
negative-pair route. This is still part of the open source-to-token package.
The full builder, exact complete formula output, packaged reduction and final
core/publication verification remain downstream. M230 and its fixed weighted
checkpoint remain open; defer PNPLabs publication. Formal artefact coverage
remains 205/207; risk-weighted proof completion remains 35%, uncertainty 20–40%;
global gates remain 0/5 closed. The seven-major-package estimate is unchanged
and is not a time estimate.
