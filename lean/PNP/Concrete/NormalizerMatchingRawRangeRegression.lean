import PNP.Concrete.NormalizerMatchingRawRange
namespace PNP.Concrete.NormalizerBlocks
example (width malformed : BitString) (entries : MatchingTable.Entries) :
    ∃ answer, (Search.result (MatchingDriver.searchPacket width malformed (MatchingTable.encode entries))).registers.output =
      Search.answer answer ∧ Search.OutputBound (ClauseCount.count malformed + width.length) answer :=
  MatchingDriver.search_raw_shape width malformed entries
example (input : BitString) :
    ∃ trace, (Search.explored input).core.core.trace = TraceData.encode trace ∧
      ExplorationData.TraceBound (Exploration.sourceLimit input) trace ∧
      trace.length ≤ Exploration.sourceLimit input := Search.explored_raw_range input
#print axioms Exploration.scan_trace_range
#print axioms Exploration.initialized_exact_within
#print axioms Exploration.finished_trace
#print axioms Search.explored_raw_range
#print axioms MatchingDriver.searchPacket_fields
#print axioms MatchingDriver.search_raw_shape
end PNP.Concrete.NormalizerBlocks
