import PNP.Concrete.NormalizerSearchTrace
namespace PNP.Concrete.NormalizerBlocks
def searchTraceFixture : Search.State := Search.explored (Exploration.encode 1 [[⟨true, 0⟩]] [none])
example : searchTraceFixture.original = Exploration.encode 1 [[⟨true, 0⟩]] [none] := by decide
example : searchTraceFixture.core.core.trace = TraceData.encode [(⟨false, 0⟩, some ⟨true, 0⟩), (⟨true, 0⟩, none)] := by decide
example : (Search.seenDerived searchTraceFixture).registers.output = MatchingTable.encode [some 0, none] := by decide
#print axioms Search.saveOriginal_exec
#print axioms Search.explore_exec
#print axioms Search.exploreFuel_bound
#print axioms Search.explored_trace
#print axioms Search.explored_matching_raw
#print axioms Search.explored_matching
#print axioms Search.deriveSeen_exec
#print axioms Search.seenDerived_frame
#print axioms Search.seenDerived_canonical
end PNP.Concrete.NormalizerBlocks
