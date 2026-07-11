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
This module does not construct a frame recognizer or creator, state namespace, rule simulation,
first-match preservation theorem, transition-count bound, normalization run, executable handoff,
composition or precomposition refinement, verifier adapter, charged/raw class equivalence,
`CNFSAT ∈ P`, NP-completeness, a root theorem, or `P = NP`.
