import PNP.Concrete.NANDFrontendPack

namespace PNP.Concrete.NANDFrontend

example (base next : Nat) : (packCode base next).length = 17 := rfl
example (r : Registers) : (packed r).input = r.input := rfl
example (r : Registers) : (packed r).width = r.width := rfl
example (r : Registers) : (packed r).inputs = r.inputs := rfl
example (p : BitRegister.Program 9) (base next : Nat) (r : Registers)
    (placed : Segment p base (packCode base next)) :
    BitRegister.run p (packFuel r) (r.state base) = (packed r).state next := pack_run p base next r placed
example (r : Registers) : (packed r).reversed = [] := rfl
example (r : Registers) : (packed r).temp = [] := rfl

#print axioms packReverseCode_length
#print axioms packReverse_empty
#print axioms packReverse_cons
#print axioms packReverse_run
#print axioms widthPrefixCode_length
#print axioms widthPrefix_start
#print axioms widthPrefix_loop_empty
#print axioms widthPrefix_loop_cons
#print axioms widthPrefix_loop
#print axioms widthPrefix_run
#print axioms packCode_length
#print axioms pack_run

end PNP.Concrete.NANDFrontend
