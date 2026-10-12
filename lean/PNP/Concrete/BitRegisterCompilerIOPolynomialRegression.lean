import PNP.Concrete.BitRegisterCompilerIOPolynomial

namespace PNP.Concrete.BitRegister

open CompilerIO

private def identityProgram : Program 1 := ⟨[.accept], 0, 0, 0⟩
private def copyAndPop : Program 2 := ⟨[.copy 1 0 1, .pop 0 2, .accept], 0, 0, 1⟩
private def emptyOutput : Program 2 := ⟨[.accept], 0, 1, 0⟩

private theorem identity_accepts : AcceptsWithin identityProgram (.constant 1) := by
  intro input
  rfl

private theorem copyAndPop_accepts : AcceptsWithin copyAndPop (.constant 3) := by
  intro input
  rfl

private theorem emptyOutput_accepts : AcceptsWithin emptyOutput (.constant 1) := by
  intro input
  rfl

example (span : Nat) : spanPolynomial.eval span = CopyFreeCompiler.spanBudget span :=
  spanPolynomial_eval span

example (count bound : Nat) :
    (instructionPolynomial count).eval bound = Compiler.instructionBudget count bound :=
  instructionPolynomial_eval count bound

example (count length : Nat) (fuel : NatPolynomial) :
    (runtimePolynomial count fuel).eval length = rawBudget count length (fuel.eval length) :=
  runtimePolynomial_eval count fuel length

example : (outputPolynomial (.constant 3)).eval 5 = 8 := rfl

example (input : BitString) :
    (compilePolynomial identityProgram (.constant 1) identity_accepts).output input = input :=
  compilePolynomial_output identityProgram (.constant 1) identity_accepts input

example :
    (compilePolynomial identityProgram (.constant 1) identity_accepts).output [] = [] :=
  compilePolynomial_output identityProgram (.constant 1) identity_accepts []

example :
    (compilePolynomial identityProgram (.constant 1) identity_accepts).output [true, false, true] =
      [true, false, true] :=
  compilePolynomial_output identityProgram (.constant 1) identity_accepts [true, false, true]

example (input : BitString) :
    (compilePolynomial copyAndPop (.constant 3) copyAndPop_accepts).output input = input :=
  compilePolynomial_output copyAndPop (.constant 3) copyAndPop_accepts input

example (input : BitString) :
    (compilePolynomial emptyOutput (.constant 1) emptyOutput_accepts).output input = [] :=
  compilePolynomial_output emptyOutput (.constant 1) emptyOutput_accepts input

example (input : BitString) :
    (compilePolynomial copyAndPop (.constant 3) copyAndPop_accepts).program.Halts input :=
  (compilePolynomial copyAndPop (.constant 3) copyAndPop_accepts).haltsWithin input

example (input : BitString) :
    ((compilePolynomial copyAndPop (.constant 3) copyAndPop_accepts).output input).length ≤ input.length + 3 :=
  compilePolynomial_output_length_le copyAndPop (.constant 3) copyAndPop_accepts input

example :
    (compilePolynomial copyAndPop (.constant 3) copyAndPop_accepts).program =
      .machine (rawMachine copyAndPop) (runtimePolynomial 2 (.constant 3)) :=
  compilePolynomial_program copyAndPop (.constant 3) copyAndPop_accepts

#print axioms CompilerIO.spanPolynomial_eval
#print axioms CompilerIO.instructionPolynomial_eval
#print axioms CompilerIO.runtimePolynomial_eval
#print axioms CompilerIO.outputPolynomial_eval
#print axioms CompilerIO.compilePolynomial
#print axioms CompilerIO.compilePolynomial_program
#print axioms CompilerIO.compilePolynomial_output
#print axioms CompilerIO.compilePolynomial_accepts
#print axioms CompilerIO.compilePolynomial_output_length_le

end PNP.Concrete.BitRegister
