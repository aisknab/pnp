/- Exact interfaces and adversarial finite-control contracts, not proof implementations. -/
import PNP.Concrete.WorkMachineTerminalHandoff

namespace PNP.Concrete.WorkMachineTerminalHandoff
open PipelineStateNamespace PipelineStageBridges
open WorkMachineProgramGraph (NoRuleAt QueryDistinct)

example (source : WorkMachine) (state : Nat) :
    state ∈ terminalStates source ↔ state ∈ candidates source ∧ NoRuleAt source state :=
  terminalStates_spec source state

example (source : WorkMachine) :
    (terminalStates source).Nodup :=
  terminalStates_nodup source

example (source : WorkMachine) (steps : Nat) (tape : WorkTape)
    (final : WorkConfiguration)
    (hRun : workRunExact? source steps (workStartConfiguration source tape) = some final)
    (hNo : NoRuleAt source final.state) : final.state ∈ terminalStates source :=
  reached_terminal_mem source steps tape final hRun hNo

example (outcome : Fin 6) : outcome ∈ outcomes :=
  outcomes_mem outcome

example {leftName rightName left right : Nat}
    (h : state leftName left = state rightName right) :
    leftName = rightName ∧ left = right :=
  state_injective h

example (name localState : Nat) (outcome : Fin 6) :
    state name localState ≠ outcome.val :=
  state_ne_outcome name localState outcome

example (source after : WorkMachine) (classify : Nat → Fin 6)
    (hSource : source.rules.Pairwise QueryDistinct)
    (hAfter : after.rules.Pairwise QueryDistinct) (hNo : NoRuleAt after after.acceptState) :
    (machine source after classify).rules.Pairwise QueryDistinct :=
  rules_pairwise source after classify hSource hAfter hNo

example (source after : WorkMachine) (classify : Nat → Fin 6)
    (outcome : Fin 6) : NoRuleAt (machine source after classify) outcome.val :=
  noRuleAt_outcome source after classify outcome

example (source after : WorkMachine) (classify : Nat → Fin 6)
    (sourceSteps afterSteps : Nat) (initial : WorkTape) (middle : WorkConfiguration) (finalTape : WorkTape)
    (hSourceRules : source.rules.Pairwise QueryDistinct)
    (hAfterRules : after.rules.Pairwise QueryDistinct) (hAfterNo : NoRuleAt after after.acceptState)
    (hSource : workRunExact? source sourceSteps (workStartConfiguration source initial) = some middle)
    (hTerminal : NoRuleAt source middle.state)
    (hAfter : workRunExact? after afterSteps (workStartConfiguration after middle.tape) =
      some {state := after.acceptState, tape := finalTape}) :
    workRunExact? (machine source after classify) (sourceSteps + 1 + afterSteps + 1)
      (workStartConfiguration (machine source after classify) initial) =
      some {state := (classify middle.state).val, tape := finalTape} :=
  workRunExact source after classify sourceSteps afterSteps initial middle finalTape hSourceRules hAfterRules hAfterNo hSource hTerminal hAfter

example (source after : WorkMachine) (classify : Nat → Fin 6)
    (sourceSteps afterSteps : Nat) (initial : WorkTape) (middle : WorkConfiguration) (finalTape : WorkTape)
    (hSourceRules : source.rules.Pairwise QueryDistinct)
    (hAfterRules : after.rules.Pairwise QueryDistinct) (hAfterNo : NoRuleAt after after.acceptState)
    (hSource : workRunExact? source sourceSteps (workStartConfiguration source initial) = some middle)
    (hTerminal : NoRuleAt source middle.state)
    (hAfter : workRunExact? after afterSteps (workStartConfiguration after middle.tape) =
      some {state := after.acceptState, tape := finalTape}) :
    run (compileWorkMachine (machine source after classify)) (6 * (sourceSteps + 1 + afterSteps + 1))
      (encodeWorkConfiguration (workStartConfiguration (machine source after classify) initial)) =
      encodeWorkConfiguration {state := (classify middle.state).val, tape := finalTape} :=
  run_compile_exact source after classify sourceSteps afterSteps initial middle finalTape hSourceRules hAfterRules hAfterNo hSource hTerminal hAfter

-- Duplicate rule targets yield one terminal bridge, not duplicate queries.
example :
    terminalStates {rules := [launchRule 0 2 .blank, launchRule 0 2 .blankZero], startState := 0, acceptState := 2, rejectState := 3} = [2] := by decide

-- A no-rule state absent from the finite program is not invented as a route.
example :
    99 ∉ terminalStates {rules := [launchRule 0 2 .blank], startState := 0, acceptState := 2, rejectState := 3} := by decide

-- The start itself is covered for a zero-step source.
example :
    terminalStates {rules := [], startState := 20, acceptState := 21, rejectState := 22} = [20] := by decide

-- A state with an outgoing rule must never receive a terminal bridge.
example :
    0 ∉ terminalStates {rules := [launchRule 0 2 .blank], startState := 0, acceptState := 2, rejectState := 3} := by decide

-- Conflicting source queries do not satisfy the composition premise.
example :
    ¬ ([launchRule 0 2 .blank, launchRule 0 3 .blank].Pairwise QueryDistinct) := by
  unfold QueryDistinct
  decide

example : outcomes.length = 6 := rfl

example (first second : Fin 6) (h : first ≠ second) : first.val ≠ second.val := by
  intro equality
  exact h (Fin.ext equality)

example (first second : Fin 6) (left right : Nat) (h : first ≠ second) :
    state (first.val + 1) left ≠ state (second.val + 1) right := by
  intro equality
  apply h
  apply Fin.ext
  have hNames := (state_injective equality).1
  omega

-- All six outcomes and every tape survive a zero-step continuation.
example (outcome : Fin 6) (tape : WorkTape) :
    workRunExact?
      (machine
        {rules := [], startState := 20, acceptState := 21, rejectState := 22}
        {rules := [], startState := 10, acceptState := 10, rejectState := 11}
        (fun _ => outcome)) 2
      (workStartConfiguration
        (machine
          {rules := [], startState := 20, acceptState := 21, rejectState := 22}
          {rules := [], startState := 10, acceptState := 10, rejectState := 11}
          (fun _ => outcome)) tape) =
      some {state := outcome.val, tape := tape} := by
  exact workRunExact _ _ _ 0 0 tape {state := 20, tape := tape} tape
    List.Pairwise.nil List.Pairwise.nil
    (fun _ member => nomatch member) rfl
    (fun _ member => nomatch member) rfl

end PNP.Concrete.WorkMachineTerminalHandoff
