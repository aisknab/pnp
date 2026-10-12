import PNP.Concrete.NANDFrontendSource

namespace PNP.Concrete.NANDFrontend

example (base next failure : Nat) (operand : Operand) :
    (sourceCode base operand next failure).length = 98 := sourceCode_length _ _ _ _
example (inputs old rest : BitString) :
    sourceScan inputs old (false :: true :: false :: false :: rest) = ⟨9, rest, inputs, true⟩ := rfl
example (inputs old rest : BitString) :
    sourceScan inputs old (false :: true :: false :: true :: rest) = ⟨10, rest, true :: inputs, true⟩ := rfl
example : (sourceScan [] [] [false, false, true, true, false, false, true, false]).valid = true := rfl
example : (sourceScan [] [] [false, false, true, true, false, false, true]).valid = false := rfl
example : (sourceScan [true] [] [false, true, true, false, false, false, true, false]).value =
    [true, true, true] := rfl
example (inputs old input : BitString) :
    (sourceScan inputs old input).fuel ≤ 3 * input.length + 1 := (sourceScan_bounds _ _ _).1
example (inputs old input : BitString) (h : (sourceScan inputs old input).valid = true) :
    (sourceScan inputs old input).rest.length < input.length := (sourceScan_success _ _ _ h).1

example (n : Nat) (source : LockedNAND.RawSource) (old suffix : BitString) :
    sourceScan (List.replicate n true) old
      (LockedNAND.encodeTokens (LockedNAND.encodeSourceTokens source) ++ suffix) =
        ⟨sourceReadFuel source, suffix, List.replicate (sourceIndex n source) true, true⟩ :=
  sourceScan_canonical n source old suffix

#print axioms unaryWord_add
#print axioms sourceScan_canonical
#print axioms sourceCode_length
#print axioms source_segments
#print axioms source_start
#print axioms source_tag_run
#print axioms source_run
#print axioms sourceScan_bounds
#print axioms sourceScan_success

end PNP.Concrete.NANDFrontend
