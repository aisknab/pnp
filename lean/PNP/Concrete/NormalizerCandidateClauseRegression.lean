import PNP.Concrete.NormalizerCandidateClause
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (r : CandidateTruth.State) : (CandidateTruth.clauseResult r).registers.output.length = 1 := rfl
example (r : CandidateTruth.State) : (CandidateTruth.clauseResult r).matching = r.matching :=
  (CandidateTruth.clause_fields r).2.2
example : CandidateTruth.value [true,false] ⟨false,1⟩ = true := rfl
example : CandidateTruth.value [true,false] ⟨true,1⟩ = false := rfl
#print axioms CandidateTruth.setPosition_exec
#print axioms CandidateTruth.atPosition_exec
#print axioms CandidateTruth.at_canonical
#print axioms CandidateTruth.addTruth_exec
#print axioms CandidateTruth.accumulated_truth
#print axioms CandidateTruth.accumulateFuel_bound
#print axioms CandidateTruth.finish_exec
#print axioms CandidateTruth.clause_exec
#print axioms CandidateTruth.clause_fields
#print axioms CandidateTruth.clause_canonical
#print axioms CandidateTruth.clauseFuel_bound
end PNP.Concrete.NormalizerBlocks
