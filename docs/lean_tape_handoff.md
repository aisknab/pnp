# Lean blank-delimited output and pure handoff target

`lean/PNP/Concrete/TapeHandoff.lean` fixes the observable output boundary used by finite charged
function pipelines. Raw tape transitions can observe symbols but cannot observe where Lean's
finite `Tape.right` list ends and implicit blank tape begins. Output therefore decodes the focused
cell followed by right-hand cells only until the first blank delimiter.

## Why the previous convention was unusable for a compiler

Under the superseded list-boundary-sensitive decoder, these tapes produced different outputs:

```text
{ left := [], head := zero, right := [] }       -> [false]
{ left := [], head := zero, right := [blank] }  -> [false, false]
```

Yet moving right from either tape yields exactly the same represented tape. The transition system
cannot recover whether the blank was explicit or implicit, so no universal raw handoff machine
could reconstruct both old outputs. This is a semantic obstruction, not a missing implementation
trick.

The corrected decoder is structural and stops at the first blank:

```lean
def Tape.decodeOutputCells : List TapeSymbol → BitString
  | [] => []
  | .blank :: _ => []
  | .zero :: rest => false :: decodeOutputCells rest
  | .one :: rest => true :: decodeOutputCells rest

def Tape.outputBits (tape : Tape) : BitString :=
  decodeOutputCells (tape.head :: tape.right)
```

Lean proves that canonical `Tape.ofInput` values decode exactly, suffixes after the first blank are
ignored, explicit and implicit blank boundaries agree, cells left of the focus are irrelevant, and
right/left or left/right round trips cannot change output.

## Pure target, not an executable handoff

`Tape.handoffTarget tape := Tape.ofInput tape.outputBits` specifies the exact canonical tape a
later raw stage would need. Its output is preserved and the operation is idempotent. It is an
ordinary Lean data function used as a specification; it is not stored in a `Machine`, does not
provide transition rules, and has no runtime theorem.

`lean/PNP/Concrete/PipelineTapeGeometry.lean` now supplies the next pure layer: a finite two-track
boundary frame that tolerates exterior garbage and handles empty and odd logical lengths.
`PipelineMachineSimulation.lean` supplies ordered finite rules for every supplied exact `n`-step
successful raw execution inside an already represented frame, with exactly `3 * n` successful work
steps. It extracts an exact prefix `k ≤ F` from an ordinary `F`-fuel run and, only if its endpoint is
designated halting, pads to work fuel `3 * F` and compiled fuel `18 * F`. Those are at-most fuel
budgets, not successful-step counts or input-size bounds. This proves no termination result and
does not treat a stuck nonhalting stop as a verdict. `PipelineStageBridges.lean` now supplies the
framer/simulator/handoff launches and bounded verdict classification for supplied exact target
runs. `TerminalOutputPacker.lean` separately proves terminal raw output normalization. A future
compiler still needs the explicit handoff-to-packer launch, one four-stage rule table and trace,
composition/precomposition `RawRefinement`, target termination, and the full external-input-size
polynomial copy/simulation/output bound.

## Audit

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPConcreteTapeHandoffAxiomAudit.lean
node --test audits/lean-concrete-tape-handoff0.test.mjs
```

The axiom transcript covers all fourteen public declarations. The static audit rejects the old
whole-right-list decoder, treating blank as false data, skipping a blank, swapping zero and one,
dismissing the focused cell, including left garbage, weakening the exact target, adding a machine
constructor, duplicating `Tape.outputBits`, removing the general compiler blocker, or opening the
publication gate.

## Exact nonclaim

This semantic module itself does not construct a machine. The separate pipeline-output module now
constructs one internal represented handoff machine, but does not provide terminal raw output
de-tagging, composition or precomposition refinement, verifier adapters, charged/raw class
equivalence, `CNFSAT ∈ P`, NP-completeness, a root theorem, or `P = NP`.
