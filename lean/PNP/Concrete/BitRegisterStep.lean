/-
Copyright (c) 2026 PNP Labs.

Exact instruction simulation for the finite copy-free control compiler.
The theorem preserves the whole represented tape, including exterior data and
blank slack, and counts literal work-machine transitions, not source steps.
Copy instructions remain outside this intermediate compiler's syntactic domain.
-/

import PNP.Concrete.BitRegisterControl

namespace PNP.Concrete.BitRegister.CopyFreeCompiler

open Operation WorkMachineProgramGraph PipelineStateNamespace

def controlEndpoint {count : Nat} (program : Program count) : Control → Endpoint
  | .running address => target program address
  | .accepted => .accept
  | .rejected => .reject

def encodeConfiguration {count : Nat} (program : Program count)
    (configuration : Configuration count) (outside : List WorkSymbol) (slack : Nat) :
    WorkConfiguration :=
  endpointConfiguration (controlEndpoint program configuration.control)
    (configuration.store.tape outside slack)

theorem encode_entry {count : Nat} (program : Program count) (store : Store count)
    (outside : List WorkSymbol) (slack : Nat) :
    encodeConfiguration program ⟨.running program.entry, store⟩ outside slack =
      ⟨(machine program).startState, store.tape outside slack⟩ := by
  rfl

theorem encode_running_found {count : Nat} (program : Program count) (address : Nat)
    (instruction : Instruction count) (found : lookup program.code address = some instruction)
    (store : Store count) (outside : List WorkSymbol) (slack : Nat) :
    encodeConfiguration program ⟨.running address, store⟩ outside slack =
      renameConfiguration (mainNode program address instruction).encode
        ⟨(localProgram instruction).startState, store.tape outside slack⟩ := by
  simp only [encodeConfiguration, controlEndpoint, target, addressRef, found]
  rfl

theorem main_accept_run {count : Nat} (program : Program count) (address : Nat)
    (instruction : Instruction count) (found : lookup program.code address = some instruction)
    (store : Store count) (outside : List WorkSymbol) (slack steps : Nat)
    (finalTape : WorkTape)
    (localRun : workRunExact? (localProgram instruction) steps
      ⟨(localProgram instruction).startState, store.tape outside slack⟩ =
      some ⟨(localProgram instruction).acceptState, finalTape⟩) :
    workRunExact? (machine program) (steps + 1)
      (encodeConfiguration program ⟨.running address, store⟩ outside slack) =
      some (endpointConfiguration (mainAccept program instruction) finalTape) := by
  rw [encode_running_found program address instruction found]
  exact local_then_accept (graph program) (mainNode program address instruction)
    steps _ _ (graph_wellFormed program)
    (instruction_members program address instruction found).1 localRun rfl

theorem main_reject_run {count : Nat} (program : Program count) (address : Nat)
    (instruction : Instruction count) (found : lookup program.code address = some instruction)
    (store : Store count) (outside : List WorkSymbol) (slack steps : Nat)
    (finalTape : WorkTape)
    (localRun : workRunExact? (localProgram instruction) steps
      ⟨(localProgram instruction).startState, store.tape outside slack⟩ =
      some ⟨(localProgram instruction).rejectState, finalTape⟩) :
    workRunExact? (machine program) (steps + 1)
      (encodeConfiguration program ⟨.running address, store⟩ outside slack) =
      some (endpointConfiguration (mainReject address instruction) finalTape) := by
  rw [encode_running_found program address instruction found]
  exact local_then_reject (graph program) (mainNode program address instruction)
    steps _ _ (graph_wellFormed program)
    (instruction_members program address instruction found).1 localRun rfl

theorem auxiliary_accept_run {count : Nat} (program : Program count) (address : Nat)
    (instruction : Instruction count) (found : lookup program.code address = some instruction)
    (tape finalTape : WorkTape) (steps : Nat)
    (localRun : workRunExact? (auxiliaryProgram instruction) steps
      ⟨(auxiliaryProgram instruction).startState, tape⟩ =
      some ⟨(auxiliaryProgram instruction).acceptState, finalTape⟩) :
    workRunExact? (machine program) (steps + 1)
      (endpointConfiguration (.node (auxiliaryRef address instruction)) tape) =
      some (endpointConfiguration (auxiliaryAccept program instruction) finalTape) :=
  local_then_accept (graph program) (auxiliaryNode program address instruction)
    steps _ _ (graph_wellFormed program)
    (instruction_members program address instruction found).2 localRun rfl

theorem auxiliary_reject_run {count : Nat} (program : Program count) (address : Nat)
    (instruction : Instruction count) (found : lookup program.code address = some instruction)
    (tape finalTape : WorkTape) (steps : Nat)
    (localRun : workRunExact? (auxiliaryProgram instruction) steps
      ⟨(auxiliaryProgram instruction).startState, tape⟩ =
      some ⟨(auxiliaryProgram instruction).rejectState, finalTape⟩) :
    workRunExact? (machine program) (steps + 1)
      (endpointConfiguration (.node (auxiliaryRef address instruction)) tape) =
      some (endpointConfiguration (auxiliaryReject program instruction) finalTape) :=
  local_then_reject (graph program) (auxiliaryNode program address instruction)
    steps _ _ (graph_wellFormed program)
    (instruction_members program address instruction found).2 localRun rfl

def instructionSteps {count : Nat} (instruction : Instruction count) (store : Store count) : Nat :=
  match instruction with
  | .clear destination _ => store.clearSteps destination + 1
  | .push destination _ _ => store.pushSteps destination + 1
  | .pop destination _ => store.popSteps destination + 1
  | .branch source _ _ _ =>
      if (store.get source).isEmpty then store.inspectSteps source + 1
      else 2 * (store.inspectSteps source + 1)
  | .copy _ _ _ | .jump _ | .accept | .reject => 1

def instructionSlack {count : Nat} (instruction : Instruction count)
    (store : Store count) (slack : Nat) : Nat :=
  match instruction with
  | .clear destination _ => slack + (store.get destination).length
  | .push _ _ _ => slack - 1
  | .pop destination _ => popSlack (store.get destination) slack
  | _ => slack

theorem branch_run {count : Nat} (program : Program count) (address : Nat)
    (source : Fin count) (empty zeroBranch oneBranch : Nat)
    (found : lookup program.code address = some (.branch source empty zeroBranch oneBranch))
    (store : Store count) (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (machine program)
      (instructionSteps (.branch source empty zeroBranch oneBranch) store)
      (encodeConfiguration program ⟨.running address, store⟩ outside slack) =
      some (encodeConfiguration program
        ((Instruction.branch source empty zeroBranch oneBranch).execute store) outside slack) := by
  cases value : store.get source with
  | nil =>
      have checked := main_accept_run program address _ found store outside slack
        (store.inspectSteps source) (store.tape outside slack)
        (by simpa only [localProgram, value, List.isEmpty_nil, ite_true]
            using Store.empty_run store source outside slack)
      simpa only [instructionSteps, value, List.isEmpty_nil, ite_true,
        mainAccept, Instruction.execute, Instruction.nextControl, Instruction.update,
        encodeConfiguration, controlEndpoint] using checked
  | cons bit rest =>
      have first := main_reject_run program address _ found store outside slack
        (store.inspectSteps source) (store.tape outside slack)
        (by simpa only [localProgram, value, List.isEmpty_cons, Bool.false_eq_true, ite_false]
            using Store.empty_run store source outside slack)
      have second :
          workRunExact? (machine program) (store.inspectSteps source + 1)
            (endpointConfiguration (.node (auxiliaryRef address
              (.branch source empty zeroBranch oneBranch))) (store.tape outside slack)) =
          some (endpointConfiguration
            (target program (if bit then oneBranch else zeroBranch)) (store.tape outside slack)) := by
        cases bit with
        | false =>
            exact auxiliary_reject_run program address _ found _ _ (store.inspectSteps source)
              (by simpa only [auxiliaryProgram, Bool.false_eq_true, ite_false]
                  using Store.head_run store source false rest value outside slack)
        | true =>
            exact auxiliary_accept_run program address _ found _ _ (store.inspectSteps source)
              (by simpa only [auxiliaryProgram, ite_true]
                  using Store.head_run store source true rest value outside slack)
      have combined := PipelineMachineSimulation.workRunExact?_compose
        (machine program) (store.inspectSteps source + 1) (store.inspectSteps source + 1)
        _ _ _ first second
      cases bit <;>
        simpa only [instructionSteps, value, List.isEmpty_cons, Bool.false_eq_true,
          ite_false, ite_true, Nat.two_mul, Instruction.execute, Instruction.nextControl,
          Instruction.update, encodeConfiguration, controlEndpoint] using combined

theorem instruction_run {count : Nat} (program : Program count) (address : Nat)
    (instruction : Instruction count) (found : lookup program.code address = some instruction)
    (supported : CopyProgram.CopyFree instruction) (store : Store count)
    (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (machine program) (instructionSteps instruction store)
      (encodeConfiguration program ⟨.running address, store⟩ outside slack) =
      some (encodeConfiguration program (instruction.execute store) outside
        (instructionSlack instruction store slack)) := by
  cases instruction with
  | clear destination next =>
      simpa only [instructionSteps, instructionSlack, Instruction.execute, Instruction.update,
        Instruction.nextControl, encodeConfiguration, controlEndpoint, mainAccept] using
        main_accept_run program address _ found store outside slack _ _ (Store.clear_run store destination outside slack)
  | copy destination source next => cases supported
  | push destination bit next =>
      simpa only [instructionSteps, instructionSlack, Instruction.execute, Instruction.update,
        Instruction.nextControl, encodeConfiguration, controlEndpoint, mainAccept] using
        main_accept_run program address _ found store outside slack _ _ (Store.push_run store destination bit outside slack)
  | pop destination next =>
      simpa only [instructionSteps, instructionSlack, Instruction.execute, Instruction.update,
        Instruction.nextControl, encodeConfiguration, controlEndpoint, mainAccept] using
        main_accept_run program address _ found store outside slack _ _ (Store.pop_run store destination outside slack)
  | branch source empty zeroBranch oneBranch =>
      exact branch_run program address source empty zeroBranch oneBranch found store outside slack
  | jump next =>
      exact main_accept_run program address _ found store outside slack 0 _ rfl
  | accept =>
      exact main_accept_run program address _ found store outside slack 0 _ rfl
  | reject =>
      exact main_accept_run program address _ found store outside slack 0 _ rfl

theorem lookup_mem {α : Type u} (code : List α) (address : Nat) (value : α)
    (found : lookup code address = some value) : value ∈ code := by
  induction code generalizing address with
  | nil => cases address <;> cases found
  | cons first rest ih =>
      cases address with
      | zero =>
          change some first = some value at found
          cases Option.some.inj found
          exact List.Mem.head _
      | succ address => exact List.Mem.tail _ (ih address found)

def stepSteps {count : Nat} (program : Program count) (configuration : Configuration count) : Nat :=
  match configuration.control with
  | .accepted | .rejected => 0
  | .running address =>
      match lookup program.code address with
      | none => 1
      | some instruction => instructionSteps instruction configuration.store

def stepSlack {count : Nat} (program : Program count)
    (configuration : Configuration count) (slack : Nat) : Nat :=
  match configuration.control with
  | .accepted | .rejected => slack
  | .running address =>
      match lookup program.code address with
      | none => slack
      | some instruction => instructionSlack instruction configuration.store slack

theorem missing_run {count : Nat} (program : Program count) (address : Nat)
    (missing : lookup program.code address = none) (store : Store count)
    (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (machine program) 1
      (encodeConfiguration program ⟨.running address, store⟩ outside slack) =
      some (encodeConfiguration program ⟨.rejected, store⟩ outside slack) := by
  have entry : encodeConfiguration program ⟨.running address, store⟩ outside slack =
      renameConfiguration (fallbackNode program).encode ⟨idle.startState, store.tape outside slack⟩ := by
    simp only [encodeConfiguration, controlEndpoint, target, addressRef, missing]
    rfl
  rw [entry]
  exact local_then_accept (graph program) (fallbackNode program) 0 _ _
    (graph_wellFormed program) (fallback_member program) rfl rfl

theorem step_run {count : Nat} (program : Program count) (supported : CopyFree program)
    (configuration : Configuration count) (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (machine program) (stepSteps program configuration)
      (encodeConfiguration program configuration outside slack) =
      some (encodeConfiguration program (step program configuration) outside
        (stepSlack program configuration slack)) := by
  cases configuration with
  | mk control store =>
      cases control with
      | accepted => rfl
      | rejected => rfl
      | running address =>
          cases found : lookup program.code address with
          | none =>
              simpa only [stepSteps, stepSlack, step, found] using
                missing_run program address found store outside slack
          | some instruction =>
              simpa only [stepSteps, stepSlack, step, found] using
                instruction_run program address instruction found
                  (supported instruction (lookup_mem program.code address instruction found)) store outside slack

theorem step_raw_run {count : Nat} (program : Program count) (supported : CopyFree program)
    (configuration : Configuration count) (outside : List WorkSymbol) (slack : Nat) :
    PNP.Concrete.run (compileWorkMachine (machine program)) (6 * stepSteps program configuration)
      (encodeWorkConfiguration (encodeConfiguration program configuration outside slack)) =
      encodeWorkConfiguration (encodeConfiguration program (step program configuration) outside
        (stepSlack program configuration slack)) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (step_run program supported configuration outside slack)

end PNP.Concrete.BitRegister.CopyFreeCompiler
