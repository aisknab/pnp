import PNP.Concrete.NormalizerCandidateLoop

namespace PNP.Concrete.NormalizerBlocks

example (r : Candidate.State) :
    Exec Candidate.loop r.store (Candidate.whole r).fuel (Candidate.whole r).state.store :=
  Candidate.whole_exec r
example (r : Candidate.State) : (Candidate.whole r).state.remaining = [] := Candidate.whole_stopped r
example (r : Candidate.State) :
    (Candidate.whole r).fuel ≤
      (12 * r.matching.length + 12 * r.seen.length + 52) * (r.remaining.length + 1) + 1 :=
  Candidate.whole_fuel_bound r
example (fuel : Nat) (r : Candidate.State) :
    (Candidate.run fuel r).state.matching = r.matching ∧ (Candidate.run fuel r).state.seen = r.seen :=
  Candidate.run_frame fuel r

#print axioms Candidate.run_exec
#print axioms Candidate.run_stopped
#print axioms Candidate.run_frame
#print axioms Candidate.run_fuel_bound
#print axioms Candidate.whole_exec
#print axioms Candidate.whole_stopped
#print axioms Candidate.whole_fuel_bound

end PNP.Concrete.NormalizerBlocks
