import PNP.Concrete.BitRegisterStep

namespace PNP.Concrete.BitRegister

private def sample : Store 2 := .cons [true, false] (.cons [] .nil)
private def allKinds : Program 2 :=
  ⟨[.clear 0 1, .push 1 true 2, .pop 0 3, .branch 0 4 5 6, .jump 100, .accept, .reject], 0, 0, 1⟩

private theorem allKinds_copyFree : CopyFreeCompiler.CopyFree allKinds := by
  intro instruction member
  simp only [allKinds, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact True.intro

example : CopyFreeCompiler.instructionSteps (.jump 100 : Instruction 2) sample = 1 := rfl
example : CopyFreeCompiler.instructionSlack (.clear 0 1) sample 3 = 5 := rfl
example : CopyFreeCompiler.instructionSlack (.push 1 true 2) sample 0 = 0 := rfl
example : CopyFreeCompiler.instructionSlack (.push 1 true 2) sample 3 = 2 := rfl
example : CopyFreeCompiler.instructionSlack (.pop 0 3) sample 3 = 4 := rfl
example : CopyFreeCompiler.instructionSlack (.pop 1 3) sample 3 = 3 := rfl
example : CopyFreeCompiler.stepSteps allKinds ⟨.accepted, sample⟩ = 0 := rfl
example : CopyFreeCompiler.stepSteps allKinds ⟨.rejected, sample⟩ = 0 := rfl
example : CopyFreeCompiler.stepSteps allKinds ⟨.running 100, sample⟩ = 1 := rfl
example : CopyFreeCompiler.stepSlack allKinds ⟨.running 100, sample⟩ 9 = 9 := rfl

-- Outside symbols and represented blank slack are arbitrary, not discarded.
example (control : Control) (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (CopyFreeCompiler.machine allKinds)
      (CopyFreeCompiler.stepSteps allKinds ⟨control, sample⟩)
      (CopyFreeCompiler.encodeConfiguration allKinds ⟨control, sample⟩ outside slack) =
      some (CopyFreeCompiler.encodeConfiguration allKinds (step allKinds ⟨control, sample⟩)
        outside (CopyFreeCompiler.stepSlack allKinds ⟨control, sample⟩ slack)) :=
  CopyFreeCompiler.step_run allKinds allKinds_copyFree _ outside slack

example (configuration : Configuration 2) (outside : List WorkSymbol) (slack : Nat) :
    PNP.Concrete.run (compileWorkMachine (CopyFreeCompiler.machine allKinds))
      (6 * CopyFreeCompiler.stepSteps allKinds configuration)
      (encodeWorkConfiguration (CopyFreeCompiler.encodeConfiguration allKinds configuration outside slack)) =
      encodeWorkConfiguration (CopyFreeCompiler.encodeConfiguration allKinds (step allKinds configuration)
        outside (CopyFreeCompiler.stepSlack allKinds configuration slack)) :=
  CopyFreeCompiler.step_raw_run allKinds allKinds_copyFree configuration outside slack

example (destination source : Fin 2) (configuration : Configuration 3)
    (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (CopyFreeCompiler.machine (CopyProgram.program destination source))
      (CopyFreeCompiler.stepSteps (CopyProgram.program destination source) configuration)
      (CopyFreeCompiler.encodeConfiguration (CopyProgram.program destination source) configuration outside slack) =
      some (CopyFreeCompiler.encodeConfiguration (CopyProgram.program destination source)
        (step (CopyProgram.program destination source) configuration) outside
        (CopyFreeCompiler.stepSlack (CopyProgram.program destination source) configuration slack)) :=
  CopyFreeCompiler.step_run _ (CopyProgram.program_copyFree destination source) configuration outside slack

#print axioms CopyFreeCompiler.encode_entry
#print axioms CopyFreeCompiler.encode_running_found
#print axioms CopyFreeCompiler.main_accept_run
#print axioms CopyFreeCompiler.main_reject_run
#print axioms CopyFreeCompiler.auxiliary_accept_run
#print axioms CopyFreeCompiler.auxiliary_reject_run
#print axioms CopyFreeCompiler.branch_run
#print axioms CopyFreeCompiler.instruction_run
#print axioms CopyFreeCompiler.lookup_mem
#print axioms CopyFreeCompiler.missing_run
#print axioms CopyFreeCompiler.step_run
#print axioms CopyFreeCompiler.step_raw_run

end PNP.Concrete.BitRegister
