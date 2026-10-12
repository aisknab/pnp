import PNP.Concrete.NormalizerSeenPhase
namespace PNP.Concrete.NormalizerBlocks
def seenPhaseFixture (trace : List TraceData.Row) : SeenTrace.State :=
  ⟨{ParentQuery.initial [] with pending := TraceData.encode trace}, [true, false], []⟩
example : (SeenTrace.phaseResult (seenPhaseFixture [])).registers.output = MatchingTable.encode [] := by decide
example : (SeenTrace.phaseResult (seenPhaseFixture [(⟨true, 0⟩, some ⟨false, 7⟩)])).registers.output = MatchingTable.encode [none] := by decide
example : (SeenTrace.phaseResult (seenPhaseFixture [(⟨false, 2⟩, none), (⟨true, 0⟩, none), (⟨false, 1⟩, none)])).registers.output = MatchingTable.encode [some 2, none, some 1] := by decide
#print axioms SeenTrace.scan_buffer
#print axioms SeenTrace.whole_buffer
#print axioms SeenTrace.finish_exec
#print axioms SeenTrace.front_exec
#print axioms SeenTrace.phase_exec
#print axioms SeenTrace.frontFuel_bound
#print axioms SeenTrace.phaseFuel_bound
#print axioms SeenTrace.phase_preserves
#print axioms SeenTrace.phase_canonical
end PNP.Concrete.NormalizerBlocks
