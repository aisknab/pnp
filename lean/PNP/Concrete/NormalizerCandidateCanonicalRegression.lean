import PNP.Concrete.NormalizerCandidateCanonical

namespace PNP.Concrete.NormalizerBlocks

example (count : Nat) (matching seen : MatchingTable.Entries) :
    (Candidate.whole (Candidate.initial count (MatchingTable.encode matching)
      (MatchingTable.encode seen))).state.output =
      TableOwner.answer (Candidate.selectFrom matching seen count 0) :=
  Candidate.whole_canonical count matching seen
example (fuel : Nat) (r : Candidate.State) (empty : r.remaining = []) :
    Candidate.run fuel r = ⟨1,r⟩ := Candidate.run_empty fuel r empty
example : Candidate.selectFrom [some 0] [some 0,some 1] 3 0 = some 1 := rfl
example : Candidate.selectFrom [] [] 3 0 = none := rfl
example : Candidate.selectFrom [some 1] [some 0,some 1] 3 0 = some 0 := rfl

#print axioms Candidate.run_empty
#print axioms Candidate.run_canonical
#print axioms Candidate.whole_canonical

end PNP.Concrete.NormalizerBlocks
