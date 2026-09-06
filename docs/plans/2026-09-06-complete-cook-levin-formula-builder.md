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
