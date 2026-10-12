/-
Copyright (c) 2026 PNP Labs.

Complete ordinary-input semantics and a uniform raw-transition budget for the
finite register compiler. The budget includes loading, nested copy execution,
output packing and all three graph handoffs. Source acceptance or rejection at
the stated fuel is an explicit premise: arbitrary programs need not terminate.
-/

import PNP.Concrete.BitRegisterCompilerIO

namespace PNP.Concrete.BitRegister.CompilerIO

open IOAdapter WorkMachineProgramGraph

def rawMachine {count : Nat} (program : Program count) : Machine :=
  compileWorkMachine (machine program)

def rawBudget (count inputLength fuel : Nat) : Nat :=
  (inputRawBound count).eval inputLength +
    6 * (fuel * Compiler.instructionBudget count (inputLength + fuel)) +
    outputRawBound.eval ((count + 1) * (inputLength + fuel + 1)) + 18

theorem finalStore_bounded {count : Nat} (program : Program count) (fuel : Nat) (input : BitString) :
    (finalStore program fuel input).Bounded (input.length + fuel) :=
  Compiler.scratchStore_bounded _
    (run_bounded program fuel _ (initial_bounded program input))

theorem finalStore_span_le {count : Nat} (program : Program count) (fuel : Nat) (input : BitString) :
    (finalStore program fuel input).span ≤ (count + 1) * (input.length + fuel + 1) :=
  Store.span_le _ (finalStore_bounded program fuel input)

theorem accepting_rawSteps_le {count : Nat} (program : Program count) (fuel : Nat) (input : BitString) :
    6 * acceptingSteps program fuel input ≤ rawBudget count input.length fuel := by
  have loaded := inputAdapter_rawSteps_le program input
  have executed := Compiler.initial_rawSteps_le program fuel input
  have packed := Nat.le_trans (outputAt_rawSteps_le (finalStore program fuel input) program.output.succ)
    (NatPolynomial.eval_mono outputRawBound (finalStore_span_le program fuel input))
  simp only [acceptingSteps, rawBudget]
  omega

theorem rejecting_rawSteps_le {count : Nat} (program : Program count) (fuel : Nat) (input : BitString) :
    6 * rejectingSteps program fuel input ≤ rawBudget count input.length fuel := by
  have loaded := inputAdapter_rawSteps_le program input
  have executed := Compiler.initial_rawSteps_le program fuel input
  simp only [rejectingSteps, rawBudget]
  omega

theorem encoded_run_accept {count : Nat} (program : Program count) (fuel : Nat) (input : BitString)
    (accepted : (sourceResult program fuel input).control = .accepted) :
    PNP.Concrete.run (rawMachine program) (rawBudget count input.length fuel)
      (encodeWorkConfiguration ⟨(machine program).startState, rawInputWorkTape input⟩) =
      encodeWorkConfiguration ⟨(machine program).acceptState, packedTape program fuel input⟩ :=
  run_compileWorkMachine_of_workRunExact_halted_le _ _ _ _ _
    (work_run_accept program fuel input accepted) (accept_isHalted _ _)
    (accepting_rawSteps_le program fuel input)

theorem encoded_run_reject {count : Nat} (program : Program count) (fuel : Nat) (input : BitString)
    (rejected : (sourceResult program fuel input).control = .rejected) :
    PNP.Concrete.run (rawMachine program) (rawBudget count input.length fuel)
      (encodeWorkConfiguration ⟨(machine program).startState, rawInputWorkTape input⟩) =
      encodeWorkConfiguration ⟨(machine program).rejectState, executionTape program fuel input⟩ :=
  run_compileWorkMachine_of_workRunExact_halted_le _ _ _ _ _
    (work_run_reject program fuel input rejected) (global_reject_halted (graph program) _)
    (rejecting_rawSteps_le program fuel input)

theorem start_run_accept {count : Nat} (program : Program count) (fuel : Nat) (input : BitString)
    (accepted : (sourceResult program fuel input).control = .accepted) :
    PNP.Concrete.Configuration.BlankEquivalent
      (PNP.Concrete.run (rawMachine program) (rawBudget count input.length fuel)
        (startConfig (rawMachine program) input))
      (encodeWorkConfiguration ⟨(machine program).acceptState, packedTape program fuel input⟩) := by
  have checked := run_blankEquivalent (rawMachine program) (rawBudget count input.length fuel)
    (startConfig_compileWorkMachine_blankEquivalent (machine program) input)
  simp only [workStartConfiguration] at checked
  rw [encoded_run_accept program fuel input accepted] at checked
  exact checked

theorem start_run_reject {count : Nat} (program : Program count) (fuel : Nat) (input : BitString)
    (rejected : (sourceResult program fuel input).control = .rejected) :
    PNP.Concrete.Configuration.BlankEquivalent
      (PNP.Concrete.run (rawMachine program) (rawBudget count input.length fuel)
        (startConfig (rawMachine program) input))
      (encodeWorkConfiguration ⟨(machine program).rejectState, executionTape program fuel input⟩) := by
  have checked := run_blankEquivalent (rawMachine program) (rawBudget count input.length fuel)
    (startConfig_compileWorkMachine_blankEquivalent (machine program) input)
  simp only [workStartConfiguration] at checked
  rw [encoded_run_reject program fuel input rejected] at checked
  exact checked

theorem raw_accepts {count : Nat} (program : Program count) (fuel : Nat) (input : BitString)
    (accepted : (sourceResult program fuel input).control = .accepted) :
    boundedDecide (rawMachine program) (rawBudget count input.length fuel) input = .accept := by
  apply (boundedDecide_accept_iff_final _ _ _).mpr
  exact (start_run_accept program fuel input accepted).1

theorem raw_rejects {count : Nat} (program : Program count) (fuel : Nat) (input : BitString)
    (rejected : (sourceResult program fuel input).control = .rejected) :
    boundedDecide (rawMachine program) (rawBudget count input.length fuel) input = .reject := by
  apply (boundedDecide_reject_iff_final _ _ _).mpr
  have finalState := (start_run_reject program fuel input rejected).1
  refine ⟨?_, finalState⟩
  rw [finalState]
  intro impossible
  have equal := (encodeWorkConfiguration_accept_iff (machine program) _).mp impossible
  exact (machine_accept_ne_reject (graph program)) equal.symm

theorem raw_output {count : Nat} (program : Program count) (fuel : Nat) (input : BitString)
    (accepted : (sourceResult program fuel input).control = .accepted) :
    machineOutput (rawMachine program) (rawBudget count input.length fuel) input =
      (sourceResult program fuel input).store.get program.output := by
  have preserved := Tape.outputBits_eq_of_blankEquivalent
    (start_run_accept program fuel input accepted).2
  exact preserved.trans (packedTape_output program fuel input)

theorem raw_output_length_le {count : Nat} (program : Program count) (fuel : Nat) (input : BitString)
    (accepted : (sourceResult program fuel input).control = .accepted) :
    (machineOutput (rawMachine program) (rawBudget count input.length fuel) input).length ≤ input.length + fuel := by
  rw [raw_output program fuel input accepted]
  exact Store.get_length_le _ _ (run_bounded program fuel _ (initial_bounded program input))

end PNP.Concrete.BitRegister.CompilerIO
