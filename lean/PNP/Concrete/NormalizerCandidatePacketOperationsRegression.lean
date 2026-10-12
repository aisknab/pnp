import PNP.Concrete.NormalizerCandidatePacketOperations

namespace PNP.Concrete.NormalizerBlocks

example (r : Candidate.State) :
    Exec CandidatePacket.loadTable r.store (CandidatePacket.tableFuel r) (CandidatePacket.tableResult r).store :=
  CandidatePacket.loadTable_exec r
example (r : Candidate.State) :
    CandidatePacket.tableFuel r ≤ 33 * r.core.input.length + 50 := CandidatePacket.tableFuel_bound r
example (r : Candidate.State) :
    (CandidatePacket.tableResult r).core.input.length ≤ r.core.input.length ∧
      (CandidatePacket.tableResult r).core.output.length ≤ r.core.input.length :=
  CandidatePacket.tableResult_size r
example (r : Candidate.State) :
    Exec CandidatePacket.startCandidates r.store 10 (CandidatePacket.started r).store :=
  CandidatePacket.startCandidates_exec r

#print axioms CandidatePacket.clearLeft_exec
#print axioms CandidatePacket.clearRight_exec
#print axioms CandidatePacket.resetCore_exec
#print axioms CandidatePacket.loadTable_exec
#print axioms CandidatePacket.tableFuel_bound
#print axioms CandidatePacket.tableResult_size
#print axioms CandidatePacket.saveCount_exec
#print axioms CandidatePacket.saveMatching_exec
#print axioms CandidatePacket.saveSeen_exec
#print axioms CandidatePacket.startCandidates_exec

end PNP.Concrete.NormalizerBlocks
