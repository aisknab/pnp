/-
Copyright (c) 2026 PNP Labs.

Complete finite-trace simulation for copy-free register programs, with a bound
on literal work-machine and raw-machine transitions. These bounds are relative
to source fuel and the initial register-size bound: they do not assert that an
arbitrary source program terminates or that the normalizer has been compiled.

The closed copy routine is then instantiated without a supplied correctness
premise. Its scratch register is restored and its whole tape is preserved.
-/

import PNP.Concrete.BitRegisterStep

namespace PNP.Concrete.BitRegister.CopyFreeCompiler

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

theorem run_simulation {count : Nat} (program : Program count) (supported : CopyFree program)
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
        (step_run program supported configuration outside slack)
        (ih (step program configuration) (stepSlack program configuration slack))

theorem raw_run_simulation {count : Nat} (program : Program count) (supported : CopyFree program)
    (fuel : Nat) (configuration : Configuration count) (outside : List WorkSymbol) (slack : Nat) :
    PNP.Concrete.run (compileWorkMachine (machine program)) (6 * traceSteps program fuel configuration)
      (encodeWorkConfiguration (encodeConfiguration program configuration outside slack)) =
      encodeWorkConfiguration (encodeConfiguration program (BitRegister.run program fuel configuration) outside
        (traceSlack program fuel configuration slack)) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (run_simulation program supported fuel configuration outside slack)

/-- A conservative per-instruction bound, including branch and graph bridges. -/
def spanBudget (span : Nat) : Nat :=
  9 * (span + 2) * (span + 2) + 15 * (span + 2) + 9

theorem spanBudget_mono {small large : Nat} (bound : small ≤ large) :
    spanBudget small ≤ spanBudget large := by
  have enlarged := Nat.add_le_add_right bound 2
  exact Nat.add_le_add_right
    (Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left 9 enlarged) enlarged)
      (Nat.mul_le_mul_left 15 enlarged)) 9

theorem instructionSteps_le {count : Nat} (instruction : Instruction count) (store : Store count) :
    instructionSteps instruction store ≤ spanBudget store.span := by
  cases instruction with
  | clear destination next =>
      have h := Store.clearSteps_le store destination
      simp only [instructionSteps, spanBudget]
      omega
  | copy destination source next =>
      simp only [instructionSteps, spanBudget]
      omega
  | push destination bit next =>
      have h := Store.pushSteps_le store destination
      simp only [instructionSteps, spanBudget]
      omega
  | pop destination next =>
      have h := Store.popSteps_le store destination
      simp only [instructionSteps, spanBudget]
      omega
  | branch source empty zeroBranch oneBranch =>
      have h := Store.inspectSteps_le store source
      simp only [instructionSteps, spanBudget]
      split <;> omega
  | jump next =>
      simp only [instructionSteps, spanBudget]
      omega
  | accept =>
      simp only [instructionSteps, spanBudget]
      omega
  | reject =>
      simp only [instructionSteps, spanBudget]
      omega

theorem stepSteps_le {count : Nat} (program : Program count) (configuration : Configuration count) :
    stepSteps program configuration ≤ spanBudget configuration.store.span := by
  cases configuration with
  | mk control store =>
      cases control with
      | accepted => exact Nat.zero_le _
      | rejected => exact Nat.zero_le _
      | running address =>
          cases found : lookup program.code address with
          | none =>
              simp only [stepSteps, found, spanBudget]
              omega
          | some instruction =>
              simpa only [stepSteps, found] using instructionSteps_le instruction store

theorem stepSteps_bounded {count bound : Nat} (program : Program count)
    (configuration : Configuration count) (bounded : configuration.store.Bounded bound) :
    stepSteps program configuration ≤ spanBudget (count * (bound + 1)) :=
  Nat.le_trans (stepSteps_le program configuration)
    (spanBudget_mono (Store.span_le configuration.store bounded))

/-- This charges all stored words and separators, not merely the selected word. -/
theorem traceSteps_le {count bound : Nat} (program : Program count) (fuel : Nat)
    (configuration : Configuration count) (bounded : configuration.store.Bounded bound) :
    traceSteps program fuel configuration ≤ fuel * spanBudget (count * (bound + fuel + 1)) := by
  induction fuel generalizing configuration bound with
  | zero => exact Nat.zero_le _
  | succ fuel ih =>
      have sum : bound + 1 + fuel = bound + (fuel + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 fuel]
      have remaining := ih (step program configuration) (step_bounded program configuration bounded)
      rw [sum] at remaining
      have first := Nat.le_trans (stepSteps_bounded program configuration bounded)
        (spanBudget_mono (Nat.mul_le_mul_left count
          (Nat.add_le_add_right (Nat.le_add_right bound (fuel + 1)) 1)))
      calc
        traceSteps program (fuel + 1) configuration
            ≤ spanBudget (count * (bound + (fuel + 1) + 1)) +
                fuel * spanBudget (count * (bound + (fuel + 1) + 1)) :=
          Nat.add_le_add first remaining
        _ = (fuel + 1) * spanBudget (count * (bound + (fuel + 1) + 1)) := by
          rw [Nat.succ_mul, Nat.add_comm]

theorem raw_traceSteps_le {count bound : Nat} (program : Program count) (fuel : Nat)
    (configuration : Configuration count) (bounded : configuration.store.Bounded bound) :
    6 * traceSteps program fuel configuration ≤
      6 * (fuel * spanBudget (count * (bound + fuel + 1))) :=
  Nat.mul_le_mul_left 6 (traceSteps_le program fuel configuration bounded)

def copySteps {count : Nat} (destination source : Fin count) (store : Store count) : Nat :=
  traceSteps (CopyProgram.program destination source) (CopyProgram.instructionSteps destination source store)
    ⟨.running 0, Store.cons [] store⟩

def copySlack {count : Nat} (destination source : Fin count)
    (store : Store count) (slack : Nat) : Nat :=
  traceSlack (CopyProgram.program destination source) (CopyProgram.instructionSteps destination source store)
    ⟨.running 0, Store.cons [] store⟩ slack

theorem copy_run {count : Nat} (destination source : Fin count) (store : Store count)
    (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (machine (CopyProgram.program destination source)) (copySteps destination source store)
      ⟨(machine (CopyProgram.program destination source)).startState,
        (Store.cons [] store).tape outside slack⟩ =
      some ⟨(machine (CopyProgram.program destination source)).acceptState,
        (Store.cons [] (store.set destination (store.get source))).tape outside
          (copySlack destination source store slack)⟩ := by
  have checked := run_simulation (CopyProgram.program destination source)
    (CopyProgram.program_copyFree destination source) (CopyProgram.instructionSteps destination source store)
    ⟨.running 0, Store.cons [] store⟩ outside slack
  rw [CopyProgram.run] at checked
  have entry : (CopyProgram.program destination source).entry = 0 := by
    unfold CopyProgram.program
    split <;> rfl
  have initial := encode_entry (CopyProgram.program destination source) (Store.cons [] store) outside slack
  rw [entry] at initial
  rw [initial] at checked
  exact checked

theorem copy_raw_run {count : Nat} (destination source : Fin count) (store : Store count)
    (outside : List WorkSymbol) (slack : Nat) :
    PNP.Concrete.run (compileWorkMachine (machine (CopyProgram.program destination source)))
      (6 * copySteps destination source store)
      (encodeWorkConfiguration ⟨(machine (CopyProgram.program destination source)).startState,
        (Store.cons [] store).tape outside slack⟩) =
      encodeWorkConfiguration ⟨(machine (CopyProgram.program destination source)).acceptState,
        (Store.cons [] (store.set destination (store.get source))).tape outside
          (copySlack destination source store slack)⟩ :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (copy_run destination source store outside slack)

/-- Polynomial in the entire initial bank bound, with fixed register count. -/
theorem copySteps_le {count bound : Nat} (destination source : Fin count)
    (store : Store count) (bounded : store.Bounded bound) :
    copySteps destination source store ≤
      (7 * bound + 5) * spanBudget ((count + 1) * (bound + (7 * bound + 5) + 1)) := by
  have initialBound : (Store.cons [] store).Bounded bound := ⟨Nat.zero_le bound, bounded⟩
  have stepsBound := CopyProgram.instructionSteps_le destination source store bounded
  exact Nat.le_trans
    (traceSteps_le (CopyProgram.program destination source)
      (CopyProgram.instructionSteps destination source store) ⟨.running 0, Store.cons [] store⟩ initialBound)
    (Nat.mul_le_mul stepsBound (spanBudget_mono (Nat.mul_le_mul_left (count + 1)
      (Nat.add_le_add_right (Nat.add_le_add_left stepsBound bound) 1))))

theorem copyRawSteps_le {count bound : Nat} (destination source : Fin count)
    (store : Store count) (bounded : store.Bounded bound) :
    6 * copySteps destination source store ≤
      6 * ((7 * bound + 5) * spanBudget ((count + 1) * (bound + (7 * bound + 5) + 1))) :=
  Nat.mul_le_mul_left 6 (copySteps_le destination source store bounded)

end PNP.Concrete.BitRegister.CopyFreeCompiler
