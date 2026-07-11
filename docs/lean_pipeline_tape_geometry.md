# Lean boundary-marked pipeline tape geometry

`lean/PNP/Concrete/PipelineTapeGeometry.lean` defines the two-track tape representation needed by
a future raw-pipeline compiler. It reuses the existing nine-symbol `WorkSymbol` alphabet and the
already audited `WorkTape` semantics.

## Exact representation

Each simulated raw cell is stored on the first track:

```lean
def PipelineTape.dataSymbol (symbol : TapeSymbol) : WorkSymbol :=
  ⟨symbol, .blank⟩
```

The second track is a tag. Blank denotes data, zero denotes the left marker, and one denotes the
right marker:

```lean
def PipelineTape.leftMarker  : WorkSymbol := ⟨.blank, .zero⟩
def PipelineTape.rightMarker : WorkSymbol := ⟨.blank, .one⟩
```

Lean proves that data symbols are injective, every data symbol is distinct from both markers, and
the two markers are distinct.

For a raw tape focused at `head`, the work tape contains mapped logical cells through the first
marker on each side:

```text
nearest left ... logical left | LEFT | exterior garbage
                           [data head]
logical right ...             | RIGHT | exterior garbage
```

Both raw and work-tape left lists are nearest-first; right lists are ordinary left-to-right. The
formal relation is existential in the two exterior lists. Those lists may contain any stale work
symbols, including marker-like values, because only the first marker after the mapped logical cells
belongs to the frame.

## Proved local geometry

The module proves that:

- canonical and arbitrary-garbage frames represent their raw tape exactly;
- writing a data head preserves the frame;
- an interior left or right raw move is one ordinary work-tape move;
- when the logical side is empty, a pure three-move boundary expansion inserts a blank data cell,
  shifts the relevant marker outward, and preserves the relation; and
- every pure `Tape.handoffTarget` has a valid frame with arbitrary exterior garbage.

Boundary expansion deliberately consumes the nearest exterior garbage cell when one is materialized
and preserves the remaining tail. If no exterior cell is materialized, the work-tape move exposes an
implicit blank. This is why exact whole-tape equality would be the wrong invariant.

Empty outputs need no special case: the represented raw tape has a blank data head between the two
markers. Odd logical lengths also need no padding because each raw cell is tagged one-for-one.

## Audit

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineTapeGeometryAxiomAudit.lean
node --test audits/lean-concrete-pipeline-tape-geometry0.test.mjs
```

The transcript covers all twenty declarations. The static audit rejects tag or marker collisions,
reversed or misplaced markers, loss of arbitrary exterior garbage, weakened boundary expansions,
the wrong handoff target, extra declarations, executable machine fields, hidden assumptions, or any
attempt to remove the compiler blocker or open the publication gate.

## Exact nonclaim

The expansion functions are pure tape identities, not transition-rule lists or a `WorkMachine`.
The separate `PipelineMachineSimulation` layer now supplies an ordered finite rule lift for every
supplied exact `n`-step successful raw execution over this relation, with exactly `3 * n` successful
work steps. It also extracts an exact prefix `k ≤ F` from an ordinary `F`-fuel raw run. Conditional
on that endpoint being designated halting, `workRun` with fuel `3 * F` and compiled `run` with
fuel `18 * F` reach its representation and encoding. This does not prove termination; the full
fuels are at-most budgets, not successful-step counts or input-size bounds, and a stuck nonhalting
stop is not a verdict. A separate paired-input framer now constructs a represented initial frame
from literal canonical paired input with an exact quadratic bound, but it is not composed with the
simulator. A separate output-handoff machine now reaches a represented `Tape.handoffTarget` from an
already represented tape at an exact linear logical-output-length cost, but it is not connected to
the simulator and its compiled trace is not a terminal raw-output layout. These layers do not prove
`boundedDecide`, verdict or output preservation, terminal output de-tagging, construct
composition/precomposition `RawRefinement`,
prove an input-size polynomial end-to-end bound or charged/raw class equivalence, establish
`CNFSAT ∈ P` or NP-completeness, activate a root theorem, or prove `P = NP`.
