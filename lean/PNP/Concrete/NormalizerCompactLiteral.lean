/-
Copyright (c) 2026 PNP Labs.

One complete literal compaction call: read its encoded index and polarity,
run the source-order lookup, and conditionally emit the dense literal.
Bounds include both scans and the entire emitted index, on every raw input.
-/
import PNP.Concrete.NormalizerCompactEmission

namespace PNP.Concrete.NormalizerBlocks.CompactClause
open BitRegister Occurrence

def body : Block 13 := .seq readLiteral (.seq lookup choose)
def compacted (r : State) : State := chosen (looked (literalRead r))
def bodyFuel (r : State) : Nat :=
  readFuel r + (lookupFuel (literalRead r) + chooseFuel (looked (literalRead r)))
theorem body_exec (r : State) : Exec body r.store (bodyFuel r) (compacted r).store :=
  Exec.seq (readLiteral_exec r) (Exec.seq (lookup_exec (literalRead r)) (choose_exec _))

theorem compacted_fields (r : State) :
    (compacted r).pending = next r.pending ∧
    (compacted r).variables = r.variables ∧
    (compacted r).positive = r.pending := by
  have read := read_fields r
  have look := lookup_fields (literalRead r)
  have chosen := chosen_fields (looked (literalRead r))
  exact ⟨chosen.1.trans (look.1.trans read.2.1),
    chosen.2.1.trans (look.2.1.trans read.2.2.2.1),
    chosen.2.2.trans (look.2.2.2.trans read.2.2.1)⟩

theorem bodyFuel_bound (r : State) :
    bodyFuel r ≤ 7 * r.pending.length + 64 * r.variables.length + 114 := by
  have read := readFuel_bound r
  have look := lookupFuel_bound (literalRead r)
  have emit := chooseFuel_bound (looked (literalRead r))
  have output := lookup_output_bound (literalRead r)
  have indexSize := index_bound r.pending
  rw [(read_fields r).2.2.2.1] at look output
  rw [(read_fields r).1] at output
  unfold bodyFuel
  omega

theorem compacted_buffer (r : State) (literal : CNFLiteral) (vertices : List CNFLiteral)
    (suffix : BitString)
    (pending : r.pending = NANDFrontend.literalBits literal.positive literal.variableIndex ++ suffix)
    (variables : r.variables = SearchVertices.encodeVertices vertices) :
    (compacted r).buffer = (literalOutput (compactLiteral vertices literal)).reverse ++ r.buffer := by
  have read := read_canonical r literal suffix pending
  have looked := lookup_fields (literalRead r)
  have answer := lookup_canonical (literalRead r) literal.variableIndex vertices read.1
    ((read_fields r).2.2.2.1.trans variables)
  have sign : ForwardEdge.present (CompactClause.looked (literalRead r)).positive = literal.positive := by
    rw [looked.2.2.2]
    exact read.2.2
  have emitted := chosen_buffer (CompactClause.looked (literalRead r)) literal.positive
    (TableOwner.vertexOwner vertices literal.variableIndex) sign answer
  change (compacted r).buffer = _ at emitted
  rw [looked.2.2.1, (read_fields r).2.2.2.2] at emitted
  exact emitted

theorem compacted_suffix (r : State) (literal : CNFLiteral) (suffix : BitString)
    (pending : r.pending = NANDFrontend.literalBits literal.positive literal.variableIndex ++ suffix) :
    (compacted r).pending = suffix := by
  rw [(compacted_fields r).1, pending]
  exact (parsed_canonical literal suffix).2.1

end PNP.Concrete.NormalizerBlocks.CompactClause
