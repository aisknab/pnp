import PNP.Concrete.BitRegisterCompilerExecution

namespace PNP.Concrete.BitRegister

open Compiler

private def bank (source destination : BitString) : Store 2 := .cons source (.cons destination .nil)
private def sample : Store 2 := bank [true, false] [false]
private def stop : Program 2 := ⟨[.accept], 0, 0, 1⟩
private def missing : Program 2 := ⟨[], 10, 0, 1⟩
private def copyAndPop : Program 2 := ⟨[.copy 1 0 1, .pop 0 2, .accept], 0, 0, 1⟩

example : traceSteps stop 0 ⟨.running 0, sample⟩ = 0 := rfl
example : traceSteps stop 1 ⟨.running 0, sample⟩ = 1 := rfl
example : traceSteps stop 100 ⟨.running 0, sample⟩ = 1 := rfl
example : traceSteps stop 100 ⟨.accepted, sample⟩ = 0 := traceSteps_accepted stop 100 sample
example : traceSteps stop 100 ⟨.rejected, sample⟩ = 0 := traceSteps_rejected stop 100 sample
example : traceSteps missing 100 ⟨.running 10, sample⟩ = 1 := rfl
example : traceSlack stop 100 ⟨.running 0, sample⟩ 17 = 17 := by
  change traceSlack stop 99 ⟨.accepted, sample⟩ 17 = 17
  exact traceSlack_accepted stop 99 sample 17
example : traceSlack missing 100 ⟨.running 10, sample⟩ 17 = 17 := by
  change traceSlack missing 99 ⟨.rejected, sample⟩ 17 = 17
  exact traceSlack_rejected missing 99 sample 17

-- Changing the source after copying must not change the copied destination.
example (source destination : BitString) :
    run copyAndPop 3 ⟨.running 0, bank source destination⟩ =
      ⟨.accepted, bank source.tail source⟩ := rfl

example (source destination : BitString) (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (machine copyAndPop)
      (traceSteps copyAndPop 3 ⟨.running 0, bank source destination⟩)
      (encodeConfiguration copyAndPop ⟨.running 0, bank source destination⟩ outside slack) =
      some (encodeConfiguration copyAndPop ⟨.accepted, bank source.tail source⟩ outside
        (traceSlack copyAndPop 3 ⟨.running 0, bank source destination⟩ slack)) :=
  run_simulation copyAndPop 3 _ outside slack

example {count : Nat} (program : Program count) (fuel : Nat)
    (configuration : Configuration count) (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (machine program) (traceSteps program fuel configuration)
      (encodeConfiguration program configuration outside slack) =
      some (encodeConfiguration program (run program fuel configuration) outside
        (traceSlack program fuel configuration slack)) :=
  run_simulation program fuel configuration outside slack

example {count bound : Nat} (program : Program count) (fuel : Nat)
    (configuration : Configuration count) (bounded : configuration.store.Bounded bound) :
    6 * traceSteps program fuel configuration ≤
      6 * (fuel * instructionBudget count (bound + fuel)) :=
  raw_traceSteps_le program fuel configuration bounded

example (input : BitString) (outside : List WorkSymbol) (slack : Nat) :
    PNP.Concrete.run (compileWorkMachine (machine copyAndPop))
      (6 * traceSteps copyAndPop 3 (initial copyAndPop input))
      (encodeWorkConfiguration
        ⟨(machine copyAndPop).startState, (scratchStore (initial copyAndPop input).store).tape outside slack⟩) =
      encodeWorkConfiguration
        (encodeConfiguration copyAndPop (run copyAndPop 3 (initial copyAndPop input)) outside
          (traceSlack copyAndPop 3 (initial copyAndPop input) slack)) :=
  initial_raw_run copyAndPop 3 input outside slack

example (input : BitString) :
    6 * traceSteps copyAndPop 3 (initial copyAndPop input) ≤
      6 * (3 * instructionBudget 2 (input.length + 3)) :=
  initial_rawSteps_le copyAndPop 3 input

#print axioms Compiler.traceSteps_accepted
#print axioms Compiler.traceSteps_rejected
#print axioms Compiler.traceSlack_accepted
#print axioms Compiler.traceSlack_rejected
#print axioms Compiler.run_simulation
#print axioms Compiler.raw_run_simulation
#print axioms Compiler.instructionBudget_mono
#print axioms Compiler.baseline_le_instructionBudget
#print axioms Compiler.lifted_instructionSteps_le
#print axioms Compiler.instructionSteps_bounded
#print axioms Compiler.stepSteps_bounded
#print axioms Compiler.traceSteps_le
#print axioms Compiler.raw_traceSteps_le
#print axioms Compiler.initial_run
#print axioms Compiler.initial_raw_run
#print axioms Compiler.initial_rawSteps_le

end PNP.Concrete.BitRegister
