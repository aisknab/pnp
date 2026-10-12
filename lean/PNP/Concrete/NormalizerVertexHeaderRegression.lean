import PNP.Concrete.NormalizerVertexHeader

namespace PNP.Concrete.NormalizerBlocks

example (r : Occurrence.Registers) :
    Exec SearchVertices.reset r.store 7 (SearchVertices.buffered r.input r.excess).store :=
  SearchVertices.reset_exec r
example (input buffer : BitString) :
    Exec TableInit.header (SearchVertices.buffered input buffer).store (TableInit.headerFuel input)
      (SearchVertices.readBuffered input buffer).store := SearchVertices.buffered_header_exec input buffer
example (count : Nat) (suffix buffer : BitString) :
    SearchVertices.readBuffered (TableInit.encodeCount count suffix) buffer =
      {TableInit.canonicalHeader count suffix with excess := buffer} :=
  SearchVertices.readBuffered_canonical count suffix buffer

#print axioms SearchVertices.resetLeft_exec
#print axioms SearchVertices.resetRight_exec
#print axioms SearchVertices.reset_exec
#print axioms SearchVertices.header_buffer
#print axioms SearchVertices.buffered_header_exec
#print axioms SearchVertices.prepare_exec
#print axioms SearchVertices.readBuffered_canonical

end PNP.Concrete.NormalizerBlocks
