import PNP.Concrete.NANDFrontendHeader

namespace PNP.Concrete.NANDFrontend

example (base next failure : Nat) : (headerCode base next failure).length = 113 := headerCode_length _ _ _
example (r : Registers) : (headerResult r).fuel ≤ 6 * r.input.length + 19 := header_result_bound r
example (p : BitRegister.Program 9) (base next failure : Nat) (r : Registers)
    (placed : Segment p base (headerCode base next failure)) :
    BitRegister.run p (headerResult r).fuel (r.state base) =
      (headerResult r).state.state (readerExit (headerResult r).valid next failure) :=
  header_result_run p base next failure r placed
example (inputs gates : Nat) (r : Registers) (suffix : BitString) :
    headerResult {r with input := headerBits inputs gates suffix} =
      ⟨8 + (1 + ((9 * inputs + 8) + (4 + ((9 * gates + 8) + 4)))),
        readHeader inputs gates r suffix, true⟩ := header_result_canonical inputs gates r suffix
example (inputs gates : Nat) (r : Registers) (suffix : BitString) :
    (readHeader inputs gates r suffix).inputs = List.replicate inputs true := rfl
example (inputs gates : Nat) (r : Registers) (suffix : BitString) :
    (readHeader inputs gates r suffix).width = List.replicate (inputs + 2 + gates) true := rfl

#print axioms headerSeed_run
#print axioms headerFinish_run
#print axioms headerCode_length
#print axioms header_segments
#print axioms header_result_run
#print axioms header_result_bound
#print axioms header_result_canonical

end PNP.Concrete.NANDFrontend
