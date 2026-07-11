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

A future compiler still needs a finite boundary-marked simulation that ignores left garbage,
isolates stale suffix cells, resets control state without collisions, preserves first-match rule
semantics, and pays a polynomial copy/simulation cost. Empty and odd output lengths also require an
explicit work-tape layout rather than assuming the existing positive-even paired-input bridge.

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

This semantic migration does not construct a normalization or handoff machine, a boundary frame,
state namespaces, composition or precomposition refinement, verifier adapters, charged/raw class
equivalence, `CNFSAT ∈ P`, NP-completeness, a root theorem, or `P = NP`.
