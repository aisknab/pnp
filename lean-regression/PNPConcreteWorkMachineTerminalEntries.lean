/- Entry-selected continuation contracts and fixed-start compatibility. -/
import PNP.Concrete.WorkMachineTerminalHandoff

namespace PNP.Concrete.WorkMachineTerminalHandoff
open PipelineStateNamespace PipelineStageBridges
open WorkMachineProgramGraph (NoRuleAt QueryDistinct)

example (source after : WorkMachine) (classify : Nat → Fin 6) :
    machineWithEntries source after (fun _ => after.startState) classify = machine source after classify :=
  machineWithEntries_constant source after classify

example (source after : WorkMachine) (entry : Fin 6 → Nat) (classify : Nat → Fin 6)
    (hSource : source.rules.Pairwise QueryDistinct)
    (hAfter : after.rules.Pairwise QueryDistinct) (hNo : NoRuleAt after after.acceptState) :
    (machineWithEntries source after entry classify).rules.Pairwise QueryDistinct :=
  rules_pairwise_with_entries source after entry classify hSource hAfter hNo

example (source after : WorkMachine) (entry : Fin 6 → Nat) (classify : Nat → Fin 6)
    (outcome : Fin 6) : NoRuleAt (machineWithEntries source after entry classify) outcome.val :=
  noRuleAt_outcome_with_entries source after entry classify outcome

example (source after : WorkMachine) (entry : Fin 6 → Nat) (classify : Nat → Fin 6)
    (sourceSteps afterSteps : Nat) (initial : WorkTape) (middle : WorkConfiguration) (finalTape : WorkTape)
    (hSourceRules : source.rules.Pairwise QueryDistinct)
    (hAfterRules : after.rules.Pairwise QueryDistinct) (hAfterNo : NoRuleAt after after.acceptState)
    (hSource : workRunExact? source sourceSteps (workStartConfiguration source initial) = some middle)
    (hTerminal : NoRuleAt source middle.state)
    (hAfter : workRunExact? after afterSteps {state := entry (classify middle.state), tape := middle.tape} =
      some {state := after.acceptState, tape := finalTape}) :
    workRunExact? (machineWithEntries source after entry classify) (sourceSteps + 1 + afterSteps + 1)
      (workStartConfiguration (machineWithEntries source after entry classify) initial) =
      some {state := (classify middle.state).val, tape := finalTape} :=
  workRunExact_with_entries source after entry classify sourceSteps afterSteps initial middle finalTape hSourceRules hAfterRules hAfterNo hSource hTerminal hAfter

example (source after : WorkMachine) (entry : Fin 6 → Nat) (classify : Nat → Fin 6)
    (sourceSteps afterSteps : Nat) (initial : WorkTape) (middle : WorkConfiguration) (finalTape : WorkTape)
    (hSourceRules : source.rules.Pairwise QueryDistinct)
    (hAfterRules : after.rules.Pairwise QueryDistinct) (hAfterNo : NoRuleAt after after.acceptState)
    (hSource : workRunExact? source sourceSteps (workStartConfiguration source initial) = some middle)
    (hTerminal : NoRuleAt source middle.state)
    (hAfter : workRunExact? after afterSteps {state := entry (classify middle.state), tape := middle.tape} =
      some {state := after.acceptState, tape := finalTape}) :
    run (compileWorkMachine (machineWithEntries source after entry classify)) (6 * (sourceSteps + 1 + afterSteps + 1))
      (encodeWorkConfiguration (workStartConfiguration (machineWithEntries source after entry classify) initial)) =
      encodeWorkConfiguration {state := (classify middle.state).val, tape := finalTape} :=
  run_compile_exact_with_entries source after entry classify sourceSteps afterSteps initial middle finalTape hSourceRules hAfterRules hAfterNo hSource hTerminal hAfter

-- Pin the previous complete machine shape, not just an alias equation.
example (source after : WorkMachine) (classify : Nat → Fin 6) :
    machine source after classify =
      {rules := sourceRules source ++
        (terminalStates source).flatMap (fun terminal =>
          launchRules (state 0 terminal) (state ((classify terminal).val + 1) after.startState)) ++
          outcomes.flatMap (recoveryBlock after),
        startState := state 0 source.startState, acceptState := 0, rejectState := 1} := by
  simp only [machine, machineWithEntries, terminalRulesWithEntries, List.append_assoc]

-- The table selects the entry for the observed outcome, not a fixed result.
example (entry : Fin 6 → Nat) (outcome : Fin 6) :
    terminalRulesWithEntries
      {rules := [], startState := 20, acceptState := 21, rejectState := 22}
      {rules := [], startState := 999, acceptState := 50, rejectState := 51}
      entry (fun _ => outcome) =
      launchRules (state 0 20) (state (outcome.val + 1) (entry outcome)) := by
  rfl

-- The continuation's ordinary start is deliberately unusable.
example :
    workRunExact?
      {rules := launchRules 40 50, startState := 999, acceptState := 50, rejectState := 51} 1
      {state := 999, tape := {left := [], head := .blank, right := []}} = none := rfl

-- Every outcome and every tape instead execute the selected nondefault entry.
example (outcome : Fin 6) (tape : WorkTape) :
    workRunExact?
      (machineWithEntries
        {rules := [], startState := 20, acceptState := 21, rejectState := 22}
        {rules := launchRules 40 50, startState := 999, acceptState := 50, rejectState := 51}
        (fun _ => 40) (fun _ => outcome)) 3
      (workStartConfiguration
        (machineWithEntries
          {rules := [], startState := 20, acceptState := 21, rejectState := 22}
          {rules := launchRules 40 50, startState := 999, acceptState := 50, rejectState := 51}
          (fun _ => 40) (fun _ => outcome)) tape) =
      some {state := outcome.val, tape := tape} := by
  let source : WorkMachine := {rules := [], startState := 20, acceptState := 21, rejectState := 22}
  let after : WorkMachine :=
    {rules := launchRules 40 50, startState := 999, acceptState := 50, rejectState := 51}
  have hRules : after.rules.Pairwise QueryDistinct := by
    unfold QueryDistinct
    decide
  have hNo : NoRuleAt after after.acceptState := by
    intro rule member
    rcases List.mem_map.mp member with ⟨symbol, _, equality⟩
    rw [← equality]
    change 40 ≠ 50
    decide
  have hStep : workStep? after {state := 40, tape := tape} = some {state := 50, tape := tape} := by
    have h := workStep?_eq_apply_of_find after {state := 40, tape := tape}
      (launchRule 40 50 tape.head) rfl (findWorkRule_launchRules 40 50 tape.head)
    exact h
  have hAfter : workRunExact? after 1 {state := 40, tape := tape} = some {state := 50, tape := tape} := by
    simp only [workRunExact?, hStep]
  exact workRunExact_with_entries source after (fun _ => 40) (fun _ => outcome)
    0 1 tape {state := 20, tape := tape} tape List.Pairwise.nil hRules hNo rfl
    (fun _ member => nomatch member) hAfter

end PNP.Concrete.WorkMachineTerminalHandoff
