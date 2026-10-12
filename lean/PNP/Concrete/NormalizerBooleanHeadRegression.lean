import PNP.Concrete.NormalizerBooleanHead

namespace PNP.Concrete.NormalizerBlocks

example (expected : Bool) (input : BitString) :
    (BooleanHead.polynomial expected).output input = [BooleanHead.value expected input] :=
  BooleanHead.polynomial_output expected input
example (found : Option Nat) :
    (BooleanHead.polynomial false).output (TableOwner.answer found) = [found.isNone] :=
  BooleanHead.absence_answer found
example (found : Option CNFLiteral) :
    (BooleanHead.polynomial true).output (Occurrence.answer found) = [found.isSome] :=
  BooleanHead.presence_answer found
example (expected : Bool) : (BooleanHead.polynomial expected).output [] = [false] :=
  BooleanHead.polynomial_output expected []

#print axioms BooleanHead.block_exec
#print axioms BooleanHead.initial_registers
#print axioms BooleanHead.closed_run
#print axioms BooleanHead.acceptsWithin
#print axioms BooleanHead.polynomial_program
#print axioms BooleanHead.polynomial_output
#print axioms BooleanHead.machine_output
#print axioms BooleanHead.absence_answer
#print axioms BooleanHead.presence_answer

end PNP.Concrete.NormalizerBlocks
