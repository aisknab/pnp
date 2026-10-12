import PNP.Concrete.BitRegisterCompilerIO

namespace PNP.Concrete.BitRegister

open CompilerIO

private def identityProgram : Program 1 := ⟨[.accept], 0, 0, 0⟩
private def rejectingProgram : Program 1 := ⟨[.reject], 0, 0, 0⟩
private def missingProgram : Program 1 := ⟨[], 17, 0, 0⟩
private def loopingProgram : Program 1 := ⟨[.jump 0], 0, 0, 0⟩
private def copyAndPop : Program 2 := ⟨[.copy 1 0 1, .pop 0 2, .accept], 0, 0, 1⟩

example : (graph identityProgram).nodes.length = 3 := rfl
example : (machine identityProgram).acceptState = 0 := rfl
example : (machine identityProgram).rejectState = 1 := rfl
example : (executionNode identityProgram).onReject = .reject := rfl
example : (executionNode identityProgram).onAccept = .node (outputNode identityProgram).reference := rfl
example : (outputNode copyAndPop).program = IOAdapter.outputAt 2 := rfl

example (input : BitString) : (sourceResult identityProgram 1 input).control = .accepted := rfl
example (input : BitString) : (sourceResult rejectingProgram 1 input).control = .rejected := rfl
example (input : BitString) : (sourceResult missingProgram 1 input).control = .rejected := rfl
example (input : BitString) : (sourceResult loopingProgram 5 input).control = .running 0 := rfl

example (input : BitString) :
    workRunExact? (machine identityProgram) (acceptingSteps identityProgram 1 input)
      ⟨(machine identityProgram).startState, rawInputWorkTape input⟩ =
      some ⟨(machine identityProgram).acceptState, packedTape identityProgram 1 input⟩ :=
  work_run_accept identityProgram 1 input rfl

example (input : BitString) :
    workRunExact? (machine rejectingProgram) (rejectingSteps rejectingProgram 1 input)
      ⟨(machine rejectingProgram).startState, rawInputWorkTape input⟩ =
      some ⟨(machine rejectingProgram).rejectState, executionTape rejectingProgram 1 input⟩ :=
  work_run_reject rejectingProgram 1 input rfl

example (input : BitString) :
    workRunExact? (machine missingProgram) (rejectingSteps missingProgram 1 input)
      ⟨(machine missingProgram).startState, rawInputWorkTape input⟩ =
      some ⟨(machine missingProgram).rejectState, executionTape missingProgram 1 input⟩ :=
  work_run_reject missingProgram 1 input rfl

example (input : BitString) :
    workRunExact? (machine copyAndPop) (acceptingSteps copyAndPop 3 input)
      ⟨(machine copyAndPop).startState, rawInputWorkTape input⟩ =
      some ⟨(machine copyAndPop).acceptState, packedTape copyAndPop 3 input⟩ :=
  work_run_accept copyAndPop 3 input rfl

example (input : BitString) :
    (encodeWorkTape (packedTape copyAndPop 3 input)).outputBits = input :=
  packedTape_output copyAndPop 3 input

#print axioms CompilerIO.input_member
#print axioms CompilerIO.execution_member
#print axioms CompilerIO.output_member
#print axioms CompilerIO.graph_wellFormed
#print axioms CompilerIO.machine_wellFormed
#print axioms CompilerIO.graph_node_count
#print axioms CompilerIO.input_run
#print axioms CompilerIO.execution_accept_run
#print axioms CompilerIO.execution_reject_run
#print axioms CompilerIO.output_run
#print axioms CompilerIO.work_run_accept
#print axioms CompilerIO.work_run_reject
#print axioms CompilerIO.packedTape_output

end PNP.Concrete.BitRegister
