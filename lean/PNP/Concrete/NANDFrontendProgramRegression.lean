import PNP.Concrete.NANDFrontendProgram

namespace PNP.Concrete.NANDFrontend

example (operand : Operand) (r : Registers) : r.store.get operand.slot = operand.value r := Operand.read operand r
example (program : BitRegister.Program 9) : Segment program 0 program.code := Segment.full program
example (base : Nat) (first second : Bool) (next : Nat) :
    (pairCode base first second next).length = 2 := pairCode_length base first second next
example (base : Nat) (operand : Operand) (positive : Bool) (next : Nat) :
    (literalCode base operand positive next).length = 9 := literalCode_length base operand positive next
example (base : Nat) (first second third : Operand × Bool) (next : Nat) :
    (clauseCode base first second third next).length = 31 := clauseCode_length base first second third next
example (base next : Nat) : (gateCode base next).length = 93 := gateCode_length base next
example : Operand.slot .left = (4 : Fin 9) := rfl
example : Operand.slot .right = (5 : Fin 9) := rfl
example : Operand.slot .gate = (3 : Fin 9) := rfl

#print axioms Operand.read
#print axioms lookup_append_left
#print axioms lookup_append_skip
#print axioms Segment.slice
#print axioms Segment.full
#print axioms pairCode_length
#print axioms literalCode_length
#print axioms clauseCode_length
#print axioms unitCode_length
#print axioms gateCode_length

end PNP.Concrete.NANDFrontend
