import PNP.Concrete.NormalizerExplorationAccept

namespace PNP.Concrete.NormalizerBlocks
open Exploration
def explorationAcceptFixture : State :=
  begun ⟨Extraction.loaded (Extraction.encode [] [none] [] [⟨false, 2⟩, ⟨true, 0⟩]), [true, true]⟩
example : (accepted explorationAcceptFixture).remaining = [true] := by decide
example : (accepted explorationAcceptFixture).core.pending = SearchVertices.encodeVertices [⟨false, 2⟩] := by decide
example : (accepted explorationAcceptFixture).core.trace = TraceData.encode [(⟨true, 0⟩, none)] := by decide
example : (accepted (begun ⟨Extraction.loaded
    (Extraction.encode [[⟨true, 2⟩]] [none] [(⟨true, 0⟩, none)] [⟨false, 2⟩]), [true]⟩)).core.trace =
    TraceData.encode [(⟨false, 2⟩, some ⟨true, 0⟩), (⟨true, 0⟩, none)] := by decide

#print axioms Extraction.parentPacked_frame
#print axioms Extraction.vertexPacked_input
#print axioms Frame.set_frame
#print axioms Exploration.consume_exec
#print axioms Exploration.accept_exec
#print axioms Exploration.accepted_fields
#print axioms Exploration.accepted_trace_bytes
#print axioms Exploration.acceptFuel_bound
#print axioms Exploration.accepted_selected

end PNP.Concrete.NormalizerBlocks
