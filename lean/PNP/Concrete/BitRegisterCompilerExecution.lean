/-
Copyright (c) 2026 PNP Labs.

Exact complete finite-trace simulation for every finite bit-register program.
The compiler-owned scratch word is restored at every source-step boundary.
The bound includes the actual nested copy machine and is polynomial in the
source fuel and initial bank-size bound. It is not a termination theorem for
an arbitrary program, an input/output adapter, or the complete normalizer.
-/

import PNP.Concrete.BitRegisterCompilerStep

namespace PNP.Concrete.BitRegister.Compiler

def traceSteps {count : Nat} (program : Program count) :
    Nat → Configuration count → Nat
  | 0, _ => 0
  | fuel + 1, configuration =>
      stepSteps program configuration + traceSteps program fuel (step program configuration)

def traceSlack {count : Nat} (program : Program count) :
    Nat → Configuration count → Nat → Nat
  | 0, _, slack => slack
  | fuel + 1, configuration, slack =>
      traceSlack program fuel (step program configuration) (stepSlack program configuration slack)

theorem traceSteps_accepted {count : Nat} (program : Program count) (fuel : Nat) (store : Store count) :
    traceSteps program fuel ⟨.accepted, store⟩ = 0 := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [traceSteps, stepSteps, step, Nat.zero_add] using ih

theorem traceSteps_rejected {count : Nat} (program : Program count) (fuel : Nat) (store : Store count) :
    traceSteps program fuel ⟨.rejected, store⟩ = 0 := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [traceSteps, stepSteps, step, Nat.zero_add] using ih

theorem traceSlack_accepted {count : Nat} (program : Program count)
    (fuel : Nat) (store : Store count) (slack : Nat) :
    traceSlack program fuel ⟨.accepted, store⟩ slack = slack := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact ih

theorem traceSlack_rejected {count : Nat} (program : Program count)
    (fuel : Nat) (store : Store count) (slack : Nat) :
    traceSlack program fuel ⟨.rejected, store⟩ slack = slack := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact ih

theorem run_simulation {count : Nat} (program : Program count)
    (fuel : Nat) (configuration : Configuration count) (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (machine program) (traceSteps program fuel configuration)
      (encodeConfiguration program configuration outside slack) =
      some (encodeConfiguration program (BitRegister.run program fuel configuration) outside
        (traceSlack program fuel configuration slack)) := by
  induction fuel generalizing configuration slack with
  | zero => rfl
  | succ fuel ih =>
      exact PipelineMachineSimulation.workRunExact?_compose
        (machine program) (stepSteps program configuration)
        (traceSteps program fuel (step program configuration)) _ _ _
        (step_run program configuration outside slack)
        (ih (step program configuration) (stepSlack program configuration slack))

theorem raw_run_simulation {count : Nat} (program : Program count)
    (fuel : Nat) (configuration : Configuration count) (outside : List WorkSymbol) (slack : Nat) :
    PNP.Concrete.run (compileWorkMachine (machine program)) (6 * traceSteps program fuel configuration)
      (encodeWorkConfiguration (encodeConfiguration program configuration outside slack)) =
      encodeWorkConfiguration (encodeConfiguration program (BitRegister.run program fuel configuration) outside
        (traceSlack program fuel configuration slack)) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (run_simulation program fuel configuration outside slack)

/-- Copy costs dominate the simpler lifted instructions; the final unit
charges the outer graph bridge after the nested copy machine accepts. -/
def instructionBudget (count bound : Nat) : Nat :=
  (7 * bound + 5) *
    CopyFreeCompiler.spanBudget ((count + 1) * (bound + (7 * bound + 5) + 1)) + 1

theorem instructionBudget_mono (count : Nat) {small large : Nat} (bound : small ≤ large) :
    instructionBudget count small ≤ instructionBudget count large := by
  have factor := Nat.add_le_add_right (Nat.mul_le_mul_left 7 bound) 5
  have span := Nat.mul_le_mul_left (count + 1)
    (Nat.add_le_add_right (Nat.add_le_add bound factor) 1)
  exact Nat.add_le_add_right
    (Nat.mul_le_mul factor (CopyFreeCompiler.spanBudget_mono span)) 1

theorem baseline_le_instructionBudget (count bound : Nat) :
    CopyFreeCompiler.spanBudget ((count + 1) * (bound + 1)) ≤ instructionBudget count bound := by
  have enlarged := CopyFreeCompiler.spanBudget_mono
    (Nat.mul_le_mul_left (count + 1)
      (Nat.add_le_add_right (Nat.le_add_right bound (7 * bound + 5)) 1))
  have factor : 1 ≤ 7 * bound + 5 := by omega
  have scaled := Nat.mul_le_mul_right
    (CopyFreeCompiler.spanBudget ((count + 1) * (bound + (7 * bound + 5) + 1))) factor
  simp only [Nat.one_mul] at scaled
  exact Nat.le_trans enlarged (Nat.le_trans scaled (Nat.le_succ _))

theorem lifted_instructionSteps_le {count bound : Nat} (instruction : Instruction count)
    (store : Store count) (bounded : store.Bounded bound) :
    CopyFreeCompiler.instructionSteps (liftInstruction instruction) (scratchStore store) ≤
      instructionBudget count bound :=
  Nat.le_trans (CopyFreeCompiler.instructionSteps_le _ _)
    (Nat.le_trans (CopyFreeCompiler.spanBudget_mono
      (Store.span_le (scratchStore store) (scratchStore_bounded store bounded)))
      (baseline_le_instructionBudget count bound))

theorem instructionSteps_bounded {count bound : Nat} (instruction : Instruction count)
    (store : Store count) (bounded : store.Bounded bound) :
    instructionSteps instruction store ≤ instructionBudget count bound := by
  cases instruction with
  | clear destination next => exact lifted_instructionSteps_le (.clear destination next) store bounded
  | copy destination source next =>
      exact Nat.add_le_add_right (CopyFreeCompiler.copySteps_le destination source store bounded) 1
  | push destination bit next => exact lifted_instructionSteps_le (.push destination bit next) store bounded
  | pop destination next => exact lifted_instructionSteps_le (.pop destination next) store bounded
  | branch source empty zeroBranch oneBranch =>
      exact lifted_instructionSteps_le (.branch source empty zeroBranch oneBranch) store bounded
  | jump next => exact lifted_instructionSteps_le (.jump next) store bounded
  | accept => exact lifted_instructionSteps_le .accept store bounded
  | reject => exact lifted_instructionSteps_le .reject store bounded

theorem stepSteps_bounded {count bound : Nat} (program : Program count)
    (configuration : Configuration count) (bounded : configuration.store.Bounded bound) :
    stepSteps program configuration ≤ instructionBudget count bound := by
  cases configuration with
  | mk control store =>
      cases control with
      | accepted => exact Nat.zero_le _
      | rejected => exact Nat.zero_le _
      | running address =>
          cases found : lookup program.code address with
          | none =>
              have positive : 1 ≤ instructionBudget count bound := Nat.succ_le_succ (Nat.zero_le _)
              simpa only [stepSteps, found] using positive
          | some instruction =>
              simpa only [stepSteps, found] using instructionSteps_bounded instruction store bounded

/-- Source copies do not increase the maximum word length; source pushes add at
most one bit. Internal copying and scratch storage are charged by the budget. -/
theorem traceSteps_le {count bound : Nat} (program : Program count) (fuel : Nat)
    (configuration : Configuration count) (bounded : configuration.store.Bounded bound) :
    traceSteps program fuel configuration ≤ fuel * instructionBudget count (bound + fuel) := by
  induction fuel generalizing configuration bound with
  | zero => exact Nat.zero_le _
  | succ fuel ih =>
      have sum : bound + 1 + fuel = bound + (fuel + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 fuel]
      have remaining := ih (step program configuration) (step_bounded program configuration bounded)
      rw [sum] at remaining
      have first := Nat.le_trans (stepSteps_bounded program configuration bounded)
        (instructionBudget_mono count (Nat.le_add_right bound (fuel + 1)))
      calc
        traceSteps program (fuel + 1) configuration
            ≤ instructionBudget count (bound + (fuel + 1)) +
                fuel * instructionBudget count (bound + (fuel + 1)) :=
          Nat.add_le_add first remaining
        _ = (fuel + 1) * instructionBudget count (bound + (fuel + 1)) := by
          rw [Nat.succ_mul, Nat.add_comm]

theorem raw_traceSteps_le {count bound : Nat} (program : Program count) (fuel : Nat)
    (configuration : Configuration count) (bounded : configuration.store.Bounded bound) :
    6 * traceSteps program fuel configuration ≤
      6 * (fuel * instructionBudget count (bound + fuel)) :=
  Nat.mul_le_mul_left 6 (traceSteps_le program fuel configuration bounded)

theorem initial_run {count : Nat} (program : Program count) (fuel : Nat)
    (input : BitString) (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (machine program) (traceSteps program fuel (initial program input))
      ⟨(machine program).startState, (scratchStore (initial program input).store).tape outside slack⟩ =
      some (encodeConfiguration program (BitRegister.run program fuel (initial program input)) outside
        (traceSlack program fuel (initial program input) slack)) := by
  have checked := run_simulation program fuel (initial program input) outside slack
  rw [show encodeConfiguration program (initial program input) outside slack =
      ⟨(machine program).startState, (scratchStore (initial program input).store).tape outside slack⟩ from
    encode_entry program _ outside slack] at checked
  exact checked

theorem initial_raw_run {count : Nat} (program : Program count) (fuel : Nat)
    (input : BitString) (outside : List WorkSymbol) (slack : Nat) :
    PNP.Concrete.run (compileWorkMachine (machine program))
      (6 * traceSteps program fuel (initial program input))
      (encodeWorkConfiguration
        ⟨(machine program).startState, (scratchStore (initial program input).store).tape outside slack⟩) =
      encodeWorkConfiguration
        (encodeConfiguration program (BitRegister.run program fuel (initial program input)) outside
          (traceSlack program fuel (initial program input) slack)) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (initial_run program fuel input outside slack)

theorem initial_rawSteps_le {count : Nat} (program : Program count) (fuel : Nat) (input : BitString) :
    6 * traceSteps program fuel (initial program input) ≤
      6 * (fuel * instructionBudget count (input.length + fuel)) :=
  raw_traceSteps_le program fuel (initial program input) (initial_bounded program input)

end PNP.Concrete.BitRegister.Compiler
