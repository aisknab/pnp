import PNP.Concrete.NormalizerMatchingLoop
namespace PNP.Concrete.NormalizerBlocks
example (r : MatchingDriver.State) (stopped : r.remaining = []) :
    (MatchingDriver.whole r).state.table = r.table := by
  rw [MatchingDriver.whole, MatchingDriver.scan_empty _ r stopped]
example (v : Nat) (cs : List (List CNFLiteral)) (entries : MatchingTable.Entries)
    (r : MatchingDriver.State) (data : MatchingDriver.Canonical v cs entries r) :
    (MatchingDriver.whole r).state.table = MatchingTable.encode (MatchingLoop.finish v cs r.remaining.length entries) :=
  MatchingDriver.whole_value v cs entries r data
#print axioms MatchingDriver.State.get_remaining
#print axioms MatchingDriver.scan_empty
#print axioms MatchingDriver.scan_step
#print axioms MatchingDriver.scan_exec
#print axioms MatchingDriver.scan_stopped
#print axioms MatchingDriver.scan_frame
#print axioms MatchingDriver.whole_exec
#print axioms MatchingDriver.whole_stopped
#print axioms MatchingDriver.scan_value
#print axioms MatchingDriver.whole_value
end PNP.Concrete.NormalizerBlocks
