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

## Next implementation: executable region-local decoding

Starting from this actual selected tape, consume the physically written tag
and local coordinate and derive the canonical region-local constraint data.
Keep the existing direct decoder solely as the specification. The finite
control must implement the coordinate arithmetic and input-dependent reads,
preserve the source/output workspace, and distinguish a valid padded slot
from an absent one. Prove the all-coordinate work/raw execution and total
encoded-source polynomial bound, including the retained scratch and every
handoff. Do not substitute a supplied constraint, branch verdict or correctness
certificate, and do not promote a fixed slot to a complete decoder.

Local decoding, clause occupancy, emission, scratch recovery, Finish,
explicitly cleared padding and the complete loop/packaged reduction remain
necessary downstream obligations. Register only the complete M230 capability
in the publication inventory once its full obligation is discharged.

M230 and its fixed complete-builder checkpoint remain unearned. Publication
is deferred because the full end-to-end construction is not yet complete.
Risk-weighted proof completion estimate: 35%; uncertainty: 20% to 40%;
formal artefact coverage: 205/207; global gates closed: 0/5.

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
