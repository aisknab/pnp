import PNP.Concrete.NormalizerCandidatePacketLoader

namespace PNP.Concrete.NormalizerBlocks

example (input : BitString) :
    Exec CandidatePacket.loader (CandidatePacket.initial input).store (CandidatePacket.loaderFuel input)
      (CandidatePacket.loaded input).store := CandidatePacket.loader_exec input
example (input : BitString) : CandidatePacket.loaderFuel input ≤ 70 * input.length + 119 :=
  CandidatePacket.loaderFuel_bound input
example (input : BitString) :
    (CandidatePacket.loaded input).matching.length ≤ input.length ∧
      (CandidatePacket.loaded input).seen.length ≤ input.length ∧
        (CandidatePacket.loaded input).remaining.length ≤ 5 * input.length + 6 :=
  CandidatePacket.loaded_size input
example (count : Nat) (matching seen : MatchingTable.Entries) :
    CandidatePacket.loaded (CandidatePacket.encode count matching seen) =
      Candidate.initial count (MatchingTable.encode matching) (MatchingTable.encode seen) :=
  CandidatePacket.loaded_canonical count matching seen

#print axioms CandidatePacket.head_exec
#print axioms CandidatePacket.first_exec
#print axioms CandidatePacket.second_exec
#print axioms CandidatePacket.loader_exec
#print axioms CandidatePacket.head_input_bound
#print axioms CandidatePacket.head_counter_bound
#print axioms CandidatePacket.first_size
#print axioms CandidatePacket.second_size
#print axioms CandidatePacket.loaded_size
#print axioms CandidatePacket.loaderFuel_bound
#print axioms CandidatePacket.loaded_canonical

end PNP.Concrete.NormalizerBlocks
