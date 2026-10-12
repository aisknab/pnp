import PNP.Concrete.NANDFrontendOutput

namespace PNP.Concrete.NANDFrontend

example (base next failure : Nat) : (outputCode base next failure).length = 173 := outputCode_length _ _ _
example (p : BitRegister.Program 9) (base next failure : Nat) (r : Registers)
    (placed : Segment p base (outputCode base next failure)) :
    BitRegister.run p (outputResult r).fuel (r.state base) =
      (outputResult r).state.state (readerExit (outputResult r).valid next failure) :=
  output_result_run p base next failure r placed
example (r : Registers) :
    (outputResult r).fuel ≤ 256 * (r.input.length + r.inputs.length + r.width.length + r.reversed.length + 1) :=
  output_result_bound r
example (n : Nat) (source : LockedNAND.RawSource) (r : Registers)
    (original : r.inputs = List.replicate n true) :
    (outputResult {r with input := outputBits source}).valid = true := by
  rw [output_result_canonical n source r original]

example (n : Nat) (source : LockedNAND.RawSource) (r : Registers) (bit : Bool) (tail : BitString)
    (original : r.inputs = List.replicate n true) :
    (outputResult {r with input := outputBits source ++ bit :: tail}).valid = false :=
  output_result_trailing n source r bit tail original

#print axioms output_result_trailing
#print axioms outputCode_length
#print axioms output_segments
#print axioms output_result_run
#print axioms output_result_bound
#print axioms matchScan_self
#print axioms output_result_canonical

end PNP.Concrete.NANDFrontend
