import PNP.Concrete.NormalizerVertexEmission

namespace PNP.Concrete.NormalizerBlocks

example (tag : Bool) (r : Occurrence.Registers) :
    Exec (SearchVertices.emitEntry tag) r.store (4 * r.target.length + 10)
      (SearchVertices.emitted tag r).store := SearchVertices.emitEntry_exec tag r
example (tag : Bool) (r : Occurrence.Registers) :
    Exec (SearchVertices.step tag) r.store (4 * r.target.length + 12)
      (SearchVertices.advanced tag r).store := SearchVertices.step_exec tag r
example (tag : Bool) (count index : Nat) :
    SearchVertices.rangeBits tag count index =
      encodeTokenPairs (encodeClauseListTokens ((SearchVertices.rangeData tag count index).map (fun v => [v]))) :=
  SearchVertices.rangeBits_exact tag count index
example : SearchVertices.rangeData true 3 4 = [⟨true,4⟩,⟨true,5⟩,⟨true,6⟩] := rfl

#print axioms SearchVertices.entryBits_exact
#print axioms SearchVertices.entryBits_reverse
#print axioms SearchVertices.emitEntry_exec
#print axioms SearchVertices.step_exec
#print axioms SearchVertices.rangeBits_exact

end PNP.Concrete.NormalizerBlocks
