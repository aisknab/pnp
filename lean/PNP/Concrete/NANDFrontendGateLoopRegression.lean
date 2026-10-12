import PNP.Concrete.NANDFrontendGateLoop

namespace PNP.Concrete.NANDFrontend

example (base next failure : Nat) : (gateLoopCode base next failure).length = 315 :=
  gateLoopCode_length _ _ _
example (p : BitRegister.Program 9) (base next failure n k : Nat)
    (r : Registers) (gates : List LockedNAND.RawGate) (tail : BitString)
    (placed : Segment p base (gateLoopCode base next failure)) :
    BitRegister.run p (gateListFuel n k gates)
      ((traversalStart n k r (gateListInput gates tail)).state base) =
        (traversedGates n k gates r tail).state next :=
  gateList_canonical p base next failure n k r gates tail placed
example (n k : Nat) (gates : List LockedNAND.RawGate) (r : Registers) (tail : BitString) :
    (traversedGates n k gates r tail).reversed =
      (encodeTokenPairs (encodeClauseListTokens (gatesClauses n k gates))).reverse ++ r.reversed :=
  traversedGates_reversed n k gates r tail
example (n k : Nat) : gateListFuel n k [] = 9 := rfl

#print axioms gateLoopCode_length
#print axioms gateLoop_segments
#print axioms gateLoop_zero
#print axioms gateLoop_end
#print axioms gateListInput_cons
#print axioms encodedGate_starts_zero
#print axioms gateList_canonical
#print axioms clauseTokens_append
#print axioms traversedGates_reversed
#print axioms traversedGates_frame

end PNP.Concrete.NANDFrontend
