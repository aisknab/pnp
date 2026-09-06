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

### Source-bound register restoration (in progress)

Bind the normalizer to the tape actually produced by the source classifier.
Prove that every comparator outcome retains both original magnitudes, extract
the existing tape view from that result, and reconstruct the original index by
the proved quotient/remainder identity. No caller supplies a prepared tape,
correctness certificate or chosen route.

The intended source endpoint is the unchanged live source workspace with
retainedValues ++ [clauseCount, 0, index, tokenWidth, quotient, clauseCount].
Prepare both the exact standalone restoration trace on that produced tape and
the actual serial body machine. Its precise continuation guard is
index / tokenWidth < clauseCount; the non-body classifier endpoint stays
separate. A serial WorkMachineChain launches on accept, not reject, so do not
claim this body composition also executes Finish.

Prepare comparator-magnitude, exact body/equal/greater/zero tape handoff,
source-workspace, compiled-run, branch-separation and source-size regressions
with the implementation. Derive the restoration bound 11S + 13 from the
existing source-span theorem, and charge the new serial bridge separately in
the body bound. Audit every public theorem. Reuse the unchanged generic
normalizer and classifier evidence; run only the new permanent target and its
paired regression/axiom boundary.

The source-derived second divisor, occupancy execution, body emission, later
cleanup/loop and complete reduction remain open. Neither component earns a
publication row, weighted checkpoint or site update. Proof estimate 35%,
uncertainty 20% to 40%, formal artefact coverage 205/207 and global gates 0/5
remain unchanged.

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
