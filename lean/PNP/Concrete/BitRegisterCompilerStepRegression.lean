import PNP.Concrete.BitRegisterCompilerStep

namespace PNP.Concrete.BitRegister

private def sample : Store 2 := .cons [true, false] (.cons [] .nil)
private def allKinds : Program 2 :=
  ⟨[.copy 1 0 1, .clear 0 2, .push 1 true 3, .pop 0 4,
    .branch 0 5 6 7, .jump 100, .accept, .reject], 0, 0, 1⟩

example : (Compiler.scratchStore sample).get 0 = [] := rfl
example : (Compiler.scratchStore sample).get 1 = [true, false] := rfl
example : Compiler.instructionSteps (.copy 0 0 1) sample = 2 := rfl
example : Compiler.instructionSteps (.jump 100 : Instruction 2) sample = 1 := rfl
example : Compiler.instructionSlack (.clear 0 1) sample 3 = 5 := rfl
example : Compiler.instructionSlack (.push 1 true 2) sample 0 = 0 := rfl
example : Compiler.instructionSlack (.push 1 true 2) sample 3 = 2 := rfl
example : Compiler.instructionSlack (.pop 0 3) sample 3 = 4 := rfl
example : Compiler.instructionSlack (.pop 1 3) sample 3 = 3 := rfl
example : Compiler.stepSteps allKinds ⟨.accepted, sample⟩ = 0 := rfl
example : Compiler.stepSteps allKinds ⟨.rejected, sample⟩ = 0 := rfl
example : Compiler.stepSteps allKinds ⟨.running 100, sample⟩ = 1 := rfl
example : Compiler.stepSlack allKinds ⟨.running 100, sample⟩ 9 = 9 := rfl

-- Every source instruction, including copy, has the same complete-store interface.
example {count : Nat} (program : Program count) (configuration : Configuration count)
    (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (Compiler.machine program) (Compiler.stepSteps program configuration)
      (Compiler.encodeConfiguration program configuration outside slack) =
      some (Compiler.encodeConfiguration program (step program configuration) outside
        (Compiler.stepSlack program configuration slack)) :=
  Compiler.step_run program configuration outside slack

example (store : Store 2) (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (Compiler.machine allKinds) (Compiler.instructionSteps (.copy 1 0 1) store)
      (Compiler.encodeConfiguration allKinds ⟨.running 0, store⟩ outside slack) =
      some (Compiler.encodeConfiguration allKinds ⟨.running 1, store.set 1 (store.get 0)⟩ outside
        (Compiler.instructionSlack (.copy 1 0 1) store slack)) :=
  Compiler.instruction_run allKinds 0 (.copy 1 0 1) rfl store outside slack

example {count : Nat} (program : Program count) (configuration : Configuration count)
    (outside : List WorkSymbol) (slack : Nat) :
    PNP.Concrete.run (compileWorkMachine (Compiler.machine program))
      (6 * Compiler.stepSteps program configuration)
      (encodeWorkConfiguration (Compiler.encodeConfiguration program configuration outside slack)) =
      encodeWorkConfiguration (Compiler.encodeConfiguration program (step program configuration) outside
        (Compiler.stepSlack program configuration slack)) :=
  Compiler.step_raw_run program configuration outside slack

#print axioms Compiler.scratchStore_bounded
#print axioms Compiler.encode_entry
#print axioms Compiler.encode_running_found
#print axioms Compiler.main_accept_run
#print axioms Compiler.main_reject_run
#print axioms Compiler.auxiliary_accept_run
#print axioms Compiler.auxiliary_reject_run
#print axioms Compiler.branch_run
#print axioms Compiler.instruction_run
#print axioms Compiler.missing_run
#print axioms Compiler.step_run
#print axioms Compiler.step_raw_run

end PNP.Concrete.BitRegister
