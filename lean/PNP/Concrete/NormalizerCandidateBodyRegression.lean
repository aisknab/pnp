import PNP.Concrete.NormalizerCandidateBody

namespace PNP.Concrete.NormalizerBlocks

example (r : Candidate.State) :
    Exec Candidate.body r.store (Candidate.bodyFuel r) (Candidate.result r).store := Candidate.body_exec r
example (r : Candidate.State) :
    (Candidate.result r).matching = r.matching ∧ (Candidate.result r).seen = r.seen := Candidate.result_frame r
example (r : Candidate.State) (nonempty : r.remaining ≠ []) :
    (Candidate.result r).remaining.length < r.remaining.length := Candidate.remaining_strict r nonempty
example (r : Candidate.State) :
    Candidate.bodyFuel r ≤ 12 * r.matching.length + 12 * r.seen.length + 51 := Candidate.bodyFuel_bound r

#print axioms Candidate.advance_exec
#print axioms Candidate.choose_exec
#print axioms Candidate.finish_exec
#print axioms Candidate.decision_exec
#print axioms Candidate.body_exec
#print axioms Candidate.finish_frame
#print axioms Candidate.decision_frame
#print axioms Candidate.result_frame
#print axioms Candidate.finish_remaining_strict
#print axioms Candidate.decision_remaining_strict
#print axioms Candidate.remaining_strict
#print axioms Candidate.finish_fuel_bound
#print axioms Candidate.decision_fuel_bound
#print axioms Candidate.bodyFuel_bound

end PNP.Concrete.NormalizerBlocks
