import PNP.Concrete.NormalizerCandidateLookup

namespace PNP.Concrete.NormalizerBlocks

example (r : Candidate.State) :
    Exec Candidate.readMatching r.store (Candidate.matchingFuel r) (Candidate.matchingResult r).store :=
  Candidate.readMatching_exec r
example (r : Candidate.State) :
    Exec Candidate.readSeen r.store (Candidate.seenFuel r) (Candidate.seenResult r).store :=
  Candidate.readSeen_exec r
example (r : Candidate.State) : (Candidate.matchingResult r).core.target = r.core.target :=
  Candidate.matching_target r
example (r : Candidate.State) :
    Candidate.matchingFuel r ≤ 12 * r.matching.length + 23 ∧
      Candidate.seenFuel r ≤ 12 * r.seen.length + 23 :=
  ⟨Candidate.matchingFuel_bound r, Candidate.seenFuel_bound r⟩

example (r : Occurrence.Registers) :
    Exec Candidate.clean r.store 9 (TableOwner.prepared r.target r.input).store := Candidate.clean_exec r

#print axioms Candidate.clearScratch_exec
#print axioms Candidate.activate_exec
#print axioms Candidate.clean_exec
#print axioms Candidate.setup_exec
#print axioms Candidate.lookup_exec
#print axioms Candidate.readMatching_exec
#print axioms Candidate.readSeen_exec
#print axioms Candidate.matching_target
#print axioms Candidate.seen_target
#print axioms Candidate.matchingFuel_bound
#print axioms Candidate.seenFuel_bound
#print axioms Candidate.matching_canonical
#print axioms Candidate.seen_canonical

end PNP.Concrete.NormalizerBlocks
