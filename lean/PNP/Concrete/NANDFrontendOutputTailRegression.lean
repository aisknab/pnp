import PNP.Concrete.NANDFrontendOutputTail

namespace PNP.Concrete.NANDFrontend

example (base next : Nat) : (outputTailCode base next).length = 50 := outputTailCode_length _ _
example (p : BitRegister.Program 9) (base next : Nat) (r : Registers)
    (placed : Segment p base (outputTailCode base next)) :
    BitRegister.run p (outputTailFuel r) (r.state base) = (finishedOutput r).state next :=
  outputTail_run p base next r placed
example (r : Registers) :
    outputTailFuel r =
      30 * r.left.length + 3 * r.reversed.length + 3 * r.width.length + 3 * r.inputs.length + 87 :=
  outputTailFuel_eq r
example (r : Registers) : (finishedOutput r).inputs = r.inputs := rfl
example (r : Registers) : (finishedOutput r).width = r.width := rfl

#print axioms outputTailCode_length
#print axioms outputTail_run
#print axioms outputTailFuel_eq
#print axioms finishedOutput_data

end PNP.Concrete.NANDFrontend
