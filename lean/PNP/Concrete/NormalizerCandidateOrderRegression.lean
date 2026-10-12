import PNP.Concrete.NormalizerCandidateOrder

namespace PNP.Concrete.NormalizerBlocks

example (entries : MatchingTable.Entries) (target : Nat) :
    (TableOwner.owner entries target).isSome = entries.any (fun entry => entry == some target) :=
  TableOwner.owner_isSome entries target
example (matching seen : MatchingTable.Entries) (count index : Nat) :
    Candidate.selectFrom matching seen count index =
      ((List.finRange count).find? (fun i => Candidate.eligible matching seen (index + i.val))).map
        (fun i => index + i.val) :=
  Candidate.selectFrom_finRange matching seen count index
example :
    CandidatePacket.polynomial.output (CandidatePacket.encode 3 [some 0] [some 2, some 1]) = [true, true] := by
  rw [CandidatePacket.polynomial_canonical]
  rfl
example :
    CandidatePacket.polynomial.output (CandidatePacket.encode 3 [some 0, some 0] [some 0, some 2, some 2]) =
      [true, true, true] := by
  rw [CandidatePacket.polynomial_canonical]
  rfl
example :
    CandidatePacket.polynomial.output (CandidatePacket.encode 2 [none] [some 8]) = [false] := by
  rw [CandidatePacket.polynomial_canonical]
  rfl

#print axioms TableOwner.ownerFrom_isSome
#print axioms TableOwner.owner_isSome
#print axioms Candidate.selectFrom_succ
#print axioms Candidate.selectFrom_finRange
#print axioms Candidate.select_finRange
#print axioms Candidate.polynomial_finRange

end PNP.Concrete.NormalizerBlocks
