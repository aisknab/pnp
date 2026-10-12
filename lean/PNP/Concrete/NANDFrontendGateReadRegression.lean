import PNP.Concrete.NANDFrontendGateRead

namespace PNP.Concrete.NANDFrontend

example (base next failure : Nat) : (gateReadCode base next failure).length = 302 :=
  gateReadCode_length _ _ _
example (p : BitRegister.Program 9) (base next failure n k : Nat)
    (r : Registers) (gate : LockedNAND.RawGate) (tail : BitString)
    (placed : Segment p base (gateReadCode base next failure)) :
    BitRegister.run p (gateReadFuel n k gate)
      (({r with
        input := LockedNAND.encodeTokens (LockedNAND.encodeGateTokens gate) ++ tail
        inputs := List.replicate n true
        gate := List.replicate (n + 2 + k) true}).state base) =
        (emittedGate n k gate r tail).state next :=
  gateRead_canonical p base next failure n k r gate tail placed
example (n k : Nat) (gate : LockedNAND.RawGate) (r : Registers) (tail : BitString) :
    (emittedGate n k gate r tail).width = r.width := rfl
example (n k : Nat) (gate : LockedNAND.RawGate) (r : Registers) (tail : BitString) :
    (emittedGate n k gate r tail).output = r.output := rfl

#print axioms circuitBits_append
#print axioms source_canonical_run
#print axioms gateReadCode_length
#print axioms gateRead_segments
#print axioms gateRead_canonical

end PNP.Concrete.NANDFrontend
