import PNP.Concrete.NormalizerCandidateCanonicalBody

namespace PNP.Concrete.NormalizerBlocks

example (r : Candidate.State) (index : Nat) (matching seen : MatchingTable.Entries)
    (target : r.core.target = List.replicate index true)
    (m : r.matching = MatchingTable.encode matching) (s : r.seen = MatchingTable.encode seen) :
    Candidate.result r =
      match TableOwner.owner matching index with
      | some _ => Candidate.advanced (Candidate.matchingResult r)
      | none => match TableOwner.owner seen index with
          | none => Candidate.advanced (Candidate.seenResult (Candidate.matchingResult r))
          | some _ => Candidate.chosen (Candidate.seenResult (Candidate.matchingResult r)) :=
  Candidate.result_canonical r index matching seen target m s
example (r : Candidate.State) (index : Nat) (target : r.core.target = List.replicate index true) :
    (Candidate.advanced (Candidate.matchingResult r)).core.target = List.replicate (index + 1) true :=
  Candidate.advanced_matching_target r index target
example (r : Candidate.State) (index : Nat) (target : r.core.target = List.replicate index true) :
    (Candidate.chosen (Candidate.seenResult (Candidate.matchingResult r))).output =
      TableOwner.answer (some index) := Candidate.chosen_output r index target

#print axioms Candidate.result_canonical
#print axioms Candidate.advanced_matching_target
#print axioms Candidate.advanced_seen_target
#print axioms Candidate.chosen_output

end PNP.Concrete.NormalizerBlocks
