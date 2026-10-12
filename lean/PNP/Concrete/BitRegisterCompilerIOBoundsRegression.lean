import PNP.Concrete.BitRegisterCompilerIOBounds

namespace PNP.Concrete.BitRegister

open CompilerIO

private def identityProgram : Program 1 := ⟨[.accept], 0, 0, 0⟩
private def rejectingProgram : Program 1 := ⟨[.reject], 0, 0, 0⟩
private def missingProgram : Program 1 := ⟨[], 17, 0, 0⟩
private def copyAndPop : Program 2 := ⟨[.copy 1 0 1, .pop 0 2, .accept], 0, 0, 1⟩
private def emptyOutput : Program 2 := ⟨[.accept], 0, 1, 0⟩

example : (finalStore identityProgram 1 []).span = 2 := rfl
example : (finalStore identityProgram 1 [true, false]).span = 4 := rfl
example : (finalStore identityProgram 1 [true, false, true]).span = 5 := rfl

example (input : BitString) :
    boundedDecide (rawMachine identityProgram) (rawBudget 1 input.length 1) input = .accept :=
  raw_accepts identityProgram 1 input rfl

example (input : BitString) :
    boundedDecide (rawMachine rejectingProgram) (rawBudget 1 input.length 1) input = .reject :=
  raw_rejects rejectingProgram 1 input rfl

example (input : BitString) :
    boundedDecide (rawMachine missingProgram) (rawBudget 1 input.length 1) input = .reject :=
  raw_rejects missingProgram 1 input rfl

example (input : BitString) :
    machineOutput (rawMachine identityProgram) (rawBudget 1 input.length 1) input = input :=
  raw_output identityProgram 1 input rfl

example :
    machineOutput (rawMachine identityProgram) (rawBudget 1 0 1) [] = [] :=
  raw_output identityProgram 1 [] rfl

example :
    machineOutput (rawMachine identityProgram) (rawBudget 1 3 1) [true, false, true] = [true, false, true] :=
  raw_output identityProgram 1 [true, false, true] rfl

example :
    machineOutput (rawMachine identityProgram) (rawBudget 1 2 1) [false, true] = [false, true] :=
  raw_output identityProgram 1 [false, true] rfl

example (input : BitString) :
    machineOutput (rawMachine emptyOutput) (rawBudget 2 input.length 1) input = [] :=
  raw_output emptyOutput 1 input rfl

-- The copied result survives the subsequent destructive source pop.
example (input : BitString) :
    machineOutput (rawMachine copyAndPop) (rawBudget 2 input.length 3) input = input :=
  raw_output copyAndPop 3 input rfl

example (input : BitString) :
    boundedDecide (rawMachine copyAndPop) (rawBudget 2 input.length 3) input = .accept :=
  raw_accepts copyAndPop 3 input rfl

example {count : Nat} (program : Program count) (fuel : Nat) (input : BitString) :
    6 * acceptingSteps program fuel input ≤ rawBudget count input.length fuel :=
  accepting_rawSteps_le program fuel input

example {count : Nat} (program : Program count) (fuel : Nat) (input : BitString) :
    6 * rejectingSteps program fuel input ≤ rawBudget count input.length fuel :=
  rejecting_rawSteps_le program fuel input

#print axioms CompilerIO.finalStore_bounded
#print axioms CompilerIO.finalStore_span_le
#print axioms CompilerIO.accepting_rawSteps_le
#print axioms CompilerIO.rejecting_rawSteps_le
#print axioms CompilerIO.encoded_run_accept
#print axioms CompilerIO.encoded_run_reject
#print axioms CompilerIO.start_run_accept
#print axioms CompilerIO.start_run_reject
#print axioms CompilerIO.raw_accepts
#print axioms CompilerIO.raw_rejects
#print axioms CompilerIO.raw_output
#print axioms CompilerIO.raw_output_length_le

end PNP.Concrete.BitRegister
