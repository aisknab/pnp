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
