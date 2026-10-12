import PNP.Concrete.NormalizerVertexPhase

namespace PNP.Concrete.NormalizerBlocks

example (tag : Bool) (r : Occurrence.Registers) :
    Exec (SearchVertices.phase tag) r.store (SearchVertices.phaseSteps tag r)
      (SearchVertices.phaseResult tag r).store := SearchVertices.phase_exec tag r
example (tag : Bool) (r : Occurrence.Registers) :
    SearchVertices.phaseSteps tag r ≤ SearchVertices.phaseBudget.eval r.input.length :=
  SearchVertices.phaseSteps_bound tag r
example (tag : Bool) (count : Nat) (suffix buffer : BitString) :
    (SearchVertices.phaseResult tag (SearchVertices.buffered (TableInit.encodeCount count suffix) buffer)).input = suffix :=
  SearchVertices.phase_canonical_input tag count suffix _ rfl
example (tag : Bool) (count : Nat) (suffix buffer : BitString) :
    (SearchVertices.phaseResult tag (SearchVertices.buffered (TableInit.encodeCount count suffix) buffer)).excess =
      (SearchVertices.rangeBits tag count 0).reverse ++ buffer :=
  SearchVertices.phase_canonical_excess tag count suffix _ rfl

#print axioms SearchVertices.phase_exec
#print axioms SearchVertices.phase_input
#print axioms SearchVertices.phase_input_bound
#print axioms SearchVertices.phase_excess
#print axioms SearchVertices.phaseBudget_eval
#print axioms SearchVertices.phaseSteps_bound
#print axioms SearchVertices.phaseBudget_mono
#print axioms SearchVertices.phase_canonical_input
#print axioms SearchVertices.phase_canonical_excess

end PNP.Concrete.NormalizerBlocks
