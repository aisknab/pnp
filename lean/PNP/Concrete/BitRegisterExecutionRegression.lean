import PNP.Concrete.BitRegisterExecution

namespace PNP.Concrete.BitRegister

open CopyFreeCompiler

private def sample : Store 2 := .cons [true, false] (.cons [false] .nil)
private def stop : Program 2 := ⟨[.accept], 0, 0, 1⟩
private def missing : Program 2 := ⟨[], 10, 0, 1⟩

example : traceSteps stop 0 ⟨.running 0, sample⟩ = 0 := rfl
example : traceSteps stop 1 ⟨.running 0, sample⟩ = 1 := rfl
example : traceSteps stop 100 ⟨.running 0, sample⟩ = 1 := rfl
example : traceSteps stop 100 ⟨.accepted, sample⟩ = 0 := rfl
example : traceSteps stop 100 ⟨.rejected, sample⟩ = 0 := rfl
example : traceSteps missing 100 ⟨.running 10, sample⟩ = 1 := rfl
example : traceSlack stop 100 ⟨.running 0, sample⟩ 17 = 17 := by
  change traceSlack stop 99 ⟨.accepted, sample⟩ 17 = 17
  exact traceSlack_accepted stop 99 sample 17
example : traceSlack missing 100 ⟨.running 10, sample⟩ 17 = 17 := by
  change traceSlack missing 99 ⟨.rejected, sample⟩ 17 = 17
  exact traceSlack_rejected missing 99 sample 17
example : copySteps (0 : Fin 2) 0 sample = 1 := rfl
example : copySteps (1 : Fin 2) 1 sample = 1 := rfl
example : copySlack (0 : Fin 2) 0 sample 17 = 17 := rfl

example {count : Nat} (program : Program count) (supported : CopyFree program)
    (fuel : Nat) (configuration : Configuration count) (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (machine program) (traceSteps program fuel configuration)
      (encodeConfiguration program configuration outside slack) =
      some (encodeConfiguration program (run program fuel configuration) outside
        (traceSlack program fuel configuration slack)) :=
  run_simulation program supported fuel configuration outside slack

example {count bound : Nat} (program : Program count) (fuel : Nat)
    (configuration : Configuration count) (bounded : configuration.store.Bounded bound) :
    6 * traceSteps program fuel configuration ≤
      6 * (fuel * spanBudget (count * (bound + fuel + 1))) :=
  raw_traceSteps_le program fuel configuration bounded

example {count : Nat} (destination source : Fin count) (store : Store count)
    (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (machine (CopyProgram.program destination source)) (copySteps destination source store)
      ⟨(machine (CopyProgram.program destination source)).startState,
        (Store.cons [] store).tape outside slack⟩ =
      some ⟨(machine (CopyProgram.program destination source)).acceptState,
        (Store.cons [] (store.set destination (store.get source))).tape outside
          (copySlack destination source store slack)⟩ :=
  copy_run destination source store outside slack

example {count bound : Nat} (destination source : Fin count) (store : Store count)
    (bounded : store.Bounded bound) :
    6 * copySteps destination source store ≤
      6 * ((7 * bound + 5) * spanBudget ((count + 1) * (bound + (7 * bound + 5) + 1))) :=
  copyRawSteps_le destination source store bounded

#print axioms CopyFreeCompiler.traceSteps_accepted
#print axioms CopyFreeCompiler.traceSteps_rejected
#print axioms CopyFreeCompiler.traceSlack_accepted
#print axioms CopyFreeCompiler.traceSlack_rejected
#print axioms CopyFreeCompiler.run_simulation
#print axioms CopyFreeCompiler.raw_run_simulation
#print axioms CopyFreeCompiler.spanBudget_mono
#print axioms CopyFreeCompiler.instructionSteps_le
#print axioms CopyFreeCompiler.stepSteps_le
#print axioms CopyFreeCompiler.stepSteps_bounded
#print axioms CopyFreeCompiler.traceSteps_le
#print axioms CopyFreeCompiler.raw_traceSteps_le
#print axioms CopyFreeCompiler.copy_run
#print axioms CopyFreeCompiler.copy_raw_run
#print axioms CopyFreeCompiler.copySteps_le
#print axioms CopyFreeCompiler.copyRawSteps_le

end PNP.Concrete.BitRegister
