# Lean executable all-input framer

`lean/PNP/Concrete/PipelineInputFramer.lean` defines one literal finite
`WorkMachine` that frames every raw bitstring. The original canonical
`BitString.pair left right` route remains available with its exact polynomial.
The same rule table now also handles the empty word and an odd final raw bit by
explicit finite states and transitions.

The machine consumes the packed raw cells one at a time, copies their logical
bits into fresh `PipelineTape.dataSymbol` cells, installs the left and right
boundary markers, returns the head to the first logical cell, and halts in its
designated accepting state. For empty input it constructs the empty represented
tape directly. For odd input it copies the first component of the final partial
work cell and never promotes its materialized blank component to a logical bit.

For every `input : BitString`, the endpoint satisfies

```lean
PNP.Concrete.PipelineInputFramer.totalInputFramerFinal_represents input :
  PipelineTape.Represents (Tape.ofInput input)
    (PipelineInputFramer.totalInputFramerFinalTape input)
```

The consumed source region is deliberately retained as permitted
`outsideLeft` garbage. This is a represented boundary frame, not a no-garbage
normal form.

## Exact costs and uniform raw bound

Let `m = input.length` and let `k` be the number of packed work cells. The exact
work trace selected by the input shape is:

```text
empty input:                    4
k complete two-bit cells:      4 * k * k + 9 * k + 7
k cells, final cell partial:    4 * k * k + 9 * k + 5
```

Compilation uses six raw transitions for each proved work transition. A single
`NatPolynomial` in external raw input length bounds every branch:

```text
6 * m * m + 39 * m + 75.
```

`totalInputFramer_workRunExact` proves the exact structural work trace.
`totalInputFramerRawTimeBound_le` proves that six times that branch cost is at
most the displayed polynomial. From the ordinary raw configuration

```lean
startConfig (compileWorkMachine pairedInputFramer) input
```

`run_compileTotalInputFramer_rawTimeBound_blankEquivalent` reaches a raw
configuration blank-equivalent to the encoded represented endpoint. The
equivalence is necessary because ordinary raw input and the macro packed work
view can differ only by materialized exterior blanks. The compiled framer
therefore accepts every raw input and cannot time out at the polynomial budget.

The earlier canonical-pair theorem remains sharper. For

```text
k = left.length + right.length + 1
m = (BitString.pair left right).length = 2 * k
```

its exact compiled budget is still

```text
24 * k * k + 54 * k + 42
  = 6 * m * m + 27 * m + 42.
```

## Negative and adversarial coverage

The formal regression declarations prove that one step less than the exact
work cost times out for empty input and for each one-bit input. The static audit
mutates the empty/partial rules, both cost formulas, the polynomial, endpoint,
assumption boundary, and nonclaim text and requires every hostile variant to be
rejected.

The dedicated transcript prints the axiom closure of all 70 explicit public
declarations:

```bash
lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineInputFramerAxiomAudit.lean
node --test audits/lean-concrete-pipeline-input-framer0.test.mjs
```

Every printed closure is empty. The JavaScript audit also closes the public
declaration surface, checks literal finite control and exact formulas, rejects
Lean assumption declarations and proof shortcuts, and verifies that each
public head appears exactly once in the transcript.

## Exact boundary of the result

This module's local theorem ends at the accepting input frame. The successor
[`PipelineCompiler`](./lean_pipeline_compiler.md) now transports every raw word
from that endpoint through the renamed simulator, represented-output handoff,
and terminal packer. Thus complete-pipeline empty, odd, trailing, malformed,
and other non-pair behavior is now covered for an already-raw proof-bearing
target.

`PipelineRefinement` now supplies general
`FunctionProgram.RawRefinement.compose` and
`DecisionProgram.RawRefinement.precompose`, so the concrete complexity machine
link is discharged. These results do not establish `CNFSAT ∈ P`, CNF-SAT
NP-completeness, `PNP.Main.p_eq_np`, or `P = NP`; the publication gate remains
false.
