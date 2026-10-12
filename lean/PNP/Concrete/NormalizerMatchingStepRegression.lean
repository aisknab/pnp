import PNP.Concrete.NormalizerMatchingStep
namespace PNP.Concrete.NormalizerBlocks
example (r : MatchingDriver.State) (active : r.remaining ≠ []) :
    (MatchingDriver.bodyResult r).remaining.length < r.remaining.length := MatchingDriver.body_shorter r active
example (r : MatchingDriver.State) :
    (MatchingDriver.bodyResult r).width = r.width := (MatchingDriver.body_frame r).1
#print axioms MatchingDriver.stop_exec
#print axioms MatchingDriver.consume_exec
#print axioms MatchingDriver.continueRound_exec
#print axioms MatchingDriver.choose_exec
#print axioms MatchingDriver.body_exec
#print axioms MatchingDriver.body_frame
#print axioms MatchingDriver.body_progress
#print axioms MatchingDriver.body_shorter
#print axioms MatchingDriver.searchResult_canonical
#print axioms MatchingDriver.body_terminal
#print axioms MatchingDriver.body_augment
end PNP.Concrete.NormalizerBlocks
