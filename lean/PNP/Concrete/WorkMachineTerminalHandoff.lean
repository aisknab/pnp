/-
Copyright (c) 2026 PNP Labs.

Finite outcome-preserving composition at every reachable no-rule terminal.
The terminal table is derived from the source program, not supplied by an
input or correctness certificate. Six disjoint copies of the continuation
retain the terminal classification. Both tape-preserving bridges are charged.
-/
import PNP.Concrete.WorkMachineProgramGraph

namespace PNP.Concrete.WorkMachineTerminalHandoff

open PipelineStateNamespace PipelineStageBridges
open WorkMachineProgramGraph (NoRuleAt QueryDistinct)

/-- Deduplicate the fixed program's candidate states, without scanning a numeric range. -/
private def distinctStates : List Nat → List Nat
  | [] => []
  | first :: rest =>
      if first ∈ distinctStates rest then distinctStates rest
      else first :: distinctStates rest

private theorem mem_distinctStates (states : List Nat) (state : Nat) :
    state ∈ distinctStates states ↔ state ∈ states := by
  induction states generalizing state with
  | nil => rfl
  | cons first rest ih =>
      by_cases h : first ∈ distinctStates rest
      · have hFirst := (ih first).mp h
        rw [distinctStates, if_pos h]
        simp only [List.mem_cons, ih]
        constructor
        · intro member
          exact Or.inr member
        · intro member
          rcases member with equality | member
          · rw [equality]
            exact hFirst
          · exact member
      · rw [distinctStates, if_neg h]
        simp only [List.mem_cons, ih]

private theorem distinctStates_nodup (states : List Nat) :
    (distinctStates states).Nodup := by
  induction states with
  | nil => exact List.Pairwise.nil
  | cons first rest ih =>
      by_cases h : first ∈ distinctStates rest
      · simpa only [distinctStates, if_pos h] using ih
      · simpa only [distinctStates, if_neg h, List.nodup_cons] using And.intro h ih

def candidates (source : WorkMachine) : List Nat :=
  source.startState :: source.rules.map WorkRule.targetState

def terminalStates (source : WorkMachine) : List Nat :=
  (distinctStates (candidates source)).filter
    (fun state => source.rules.all (fun rule => decide (rule.sourceState ≠ state)))

theorem terminalStates_spec (source : WorkMachine) (state : Nat) :
    state ∈ terminalStates source ↔ state ∈ candidates source ∧ NoRuleAt source state := by
  simp only [terminalStates, List.mem_filter, mem_distinctStates, List.all_eq_true,
    decide_eq_true_eq, NoRuleAt]

theorem terminalStates_nodup (source : WorkMachine) :
    (terminalStates source).Nodup :=
  (distinctStates_nodup (candidates source)).filter _

private theorem selected_member {rules : List WorkRule} {state : Nat}
    {symbol : WorkSymbol} {selected : WorkRule}
    (hFind : findWorkRule rules state symbol = some selected) : selected ∈ rules := by
  induction rules with
  | nil => contradiction
  | cons first rest ih =>
      by_cases hMatches : first.sourceState = state ∧ first.readSymbol = symbol
      · have hHead := findWorkRule_cons_of_matches first rest state symbol hMatches
        have hEqual : first = selected := Option.some.inj (hHead.symm.trans hFind)
        subst selected
        exact List.Mem.head rest
      · have hTail := findWorkRule_cons_of_not_matches first rest state symbol hMatches
        exact List.Mem.tail first (ih (hTail.symm.trans hFind))

private theorem run_target (source : WorkMachine) (steps : Nat)
    (initial final : WorkConfiguration)
    (hRun : workRunExact? source steps initial = some final) :
    final.state = initial.state ∨ final.state ∈ source.rules.map WorkRule.targetState := by
  induction steps generalizing initial with
  | zero =>
      have h := Option.some.inj hRun
      exact Or.inl (congrArg WorkConfiguration.state h.symm)
  | succ steps ih =>
      cases hStep : workStep? source initial with
      | none =>
          simp only [workRunExact?, hStep] at hRun
          cases hRun
      | some next =>
          have hRest : workRunExact? source steps next = some final := by
            simpa only [workRunExact?, hStep] using hRun
          rcases ih next hRest with hSame | hTarget
          · rcases workStep?_some_exists source initial next hStep with
              ⟨rule, _, hFind, hNext⟩
            exact Or.inr (List.mem_map.mpr
              ⟨rule, selected_member hFind, by rw [hSame, hNext]; rfl⟩)
          · exact Or.inr hTarget

/-- Every actual no-rule endpoint, including a zero-step start, is covered. -/
theorem reached_terminal_mem (source : WorkMachine) (steps : Nat) (tape : WorkTape)
    (final : WorkConfiguration)
    (hRun : workRunExact? source steps (workStartConfiguration source tape) = some final)
    (hNo : NoRuleAt source final.state) : final.state ∈ terminalStates source := by
  apply (terminalStates_spec source final.state).mpr
  refine ⟨?_, hNo⟩
  exact List.mem_cons.mpr (run_target source steps _ final hRun)

/-- Six fixed result classes; classification happens in the finite control. -/
def outcomes : List (Fin 6) := [0, 1, 2, 3, 4, 5]

theorem outcomes_mem (outcome : Fin 6) : outcome ∈ outcomes := by
  simp only [outcomes, List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff]
  omega

private theorem outcomes_nodup : outcomes.Nodup := by decide

/-- All running states are disjoint from the six stable result states. -/
def state (name localState : Nat) : Nat :=
  WorkMachineProgramGraph.nodeState name localState + 6

theorem state_injective {leftName rightName left right : Nat}
    (h : state leftName left = state rightName right) :
    leftName = rightName ∧ left = right :=
  WorkMachineProgramGraph.nodeState_injective (Nat.add_right_cancel h)

private theorem fixed_injective (name : Nat) : Function.Injective (state name) := by
  intro left right h
  exact (state_injective h).2

theorem state_ne_outcome (name localState : Nat) (outcome : Fin 6) :
    state name localState ≠ outcome.val := by
  have h := WorkMachineProgramGraph.nodeState_ge_three name localState
  unfold state
  omega

def sourceRules (source : WorkMachine) : List WorkRule :=
  source.rules.map (renameRule (state 0))

def terminalRules (source after : WorkMachine) (classify : Nat → Fin 6) : List WorkRule :=
  (terminalStates source).flatMap (fun terminal =>
    launchRules (state 0 terminal) (state ((classify terminal).val + 1) after.startState))

def recoveryBlock (after : WorkMachine) (outcome : Fin 6) : List WorkRule :=
  after.rules.map (renameRule (state (outcome.val + 1))) ++
    launchRules (state (outcome.val + 1) after.acceptState) outcome.val

def machine (source after : WorkMachine) (classify : Nat → Fin 6) : WorkMachine :=
  {rules := sourceRules source ++
      (terminalRules source after classify ++ outcomes.flatMap (recoveryBlock after)),
    startState := state 0 source.startState, acceptState := 0, rejectState := 1}

private theorem query_of_source_ne {left right : WorkRule}
    (h : left.sourceState ≠ right.sourceState) : QueryDistinct left right := by
  intro equality
  exact h (congrArg Prod.fst equality)

private theorem renamed_pairwise (encode : Nat → Nat) (hInjective : Function.Injective encode)
    (rules : List WorkRule) (hRules : rules.Pairwise QueryDistinct) :
    (rules.map (renameRule encode)).Pairwise QueryDistinct :=
  List.Pairwise.map (renameRule encode)
    (fun left right hDistinct => by
      intro equality
      apply hDistinct
      apply Prod.ext
      · exact hInjective (by simpa [renameRule] using congrArg Prod.fst equality)
      · simpa [renameRule] using congrArg Prod.snd equality) hRules

private theorem launch_pairwise (source target : Nat) :
    (launchRules source target).Pairwise QueryDistinct := by
  unfold launchRules PipelineMachineSimulation.allWorkSymbols
  simp [QueryDistinct, launchRule, WorkSymbol.blank, WorkSymbol.blankZero, WorkSymbol.blankOne,
    WorkSymbol.zeroBlank, WorkSymbol.zeroZero, WorkSymbol.zeroOne,
    WorkSymbol.oneBlank, WorkSymbol.oneZero, WorkSymbol.oneOne]

private theorem launch_source {source target : Nat} {rule : WorkRule}
    (h : rule ∈ launchRules source target) : rule.sourceState = source := by
  rcases List.mem_map.mp h with ⟨symbol, _, equality⟩
  rw [← equality]
  rfl

private theorem renamed_source {rules : List WorkRule} {encode : Nat → Nat} {rule : WorkRule}
    (h : rule ∈ rules.map (renameRule encode)) :
    ∃ original ∈ rules, rule.sourceState = encode original.sourceState := by
  rcases List.mem_map.mp h with ⟨original, member, equality⟩
  exact ⟨original, member, by rw [← equality]; rfl⟩

private theorem flatMap_pairwise {α : Type} (items : List α) (blocks : α → List WorkRule)
    (hNodup : items.Nodup)
    (hBlock : ∀ item ∈ items, (blocks item).Pairwise QueryDistinct)
    (hCross : ∀ left ∈ items, ∀ right ∈ items, left ≠ right →
      ∀ a ∈ blocks left, ∀ b ∈ blocks right, QueryDistinct a b) :
    (items.flatMap blocks).Pairwise QueryDistinct := by
  induction items with
  | nil => exact List.Pairwise.nil
  | cons first rest ih =>
      have hParts := List.nodup_cons.mp hNodup
      rw [List.flatMap_cons, List.pairwise_append]
      refine ⟨hBlock first List.mem_cons_self,
        ih hParts.2 (fun item member => hBlock item (List.mem_cons_of_mem _ member))
          (fun left hl right hr => hCross left (List.mem_cons_of_mem _ hl)
            right (List.mem_cons_of_mem _ hr)), ?_⟩
      intro a ha b hb
      rcases List.mem_flatMap.mp hb with ⟨right, hr, hbr⟩
      exact hCross first List.mem_cons_self right (List.mem_cons_of_mem _ hr)
        (fun equality => hParts.1 (equality ▸ hr)) a ha b hbr

private theorem terminal_source (source after : WorkMachine) (classify : Nat → Fin 6)
    (rule : WorkRule) (h : rule ∈ terminalRules source after classify) :
    ∃ terminal ∈ terminalStates source, rule.sourceState = state 0 terminal := by
  rcases List.mem_flatMap.mp h with ⟨terminal, member, hr⟩
  exact ⟨terminal, member, launch_source hr⟩

private theorem recovery_source (after : WorkMachine) (outcome : Fin 6)
    (rule : WorkRule) (h : rule ∈ recoveryBlock after outcome) :
    ∃ localState, rule.sourceState = state (outcome.val + 1) localState := by
  rcases List.mem_append.mp h with hLocal | hFinish
  · rcases renamed_source hLocal with ⟨original, _, equality⟩
    exact ⟨original.sourceState, equality⟩
  · exact ⟨after.acceptState, launch_source hFinish⟩

private theorem recovery_pairwise (after : WorkMachine) (outcome : Fin 6)
    (hRules : after.rules.Pairwise QueryDistinct) (hNo : NoRuleAt after after.acceptState) :
    (recoveryBlock after outcome).Pairwise QueryDistinct := by
  unfold recoveryBlock
  rw [List.pairwise_append]
  refine ⟨renamed_pairwise _ (fixed_injective _) _ hRules, launch_pairwise _ _, ?_⟩
  intro a ha b hb
  rcases renamed_source ha with ⟨original, member, equality⟩
  apply query_of_source_ne
  rw [equality, launch_source hb]
  intro equality
  exact hNo original member ((state_injective equality).2)

/-- Duplicate source targets and all nine work symbols cannot introduce query collisions. -/
theorem rules_pairwise (source after : WorkMachine) (classify : Nat → Fin 6)
    (hSource : source.rules.Pairwise QueryDistinct)
    (hAfter : after.rules.Pairwise QueryDistinct) (hNo : NoRuleAt after after.acceptState) :
    (machine source after classify).rules.Pairwise QueryDistinct := by
  have hTerminal : (terminalRules source after classify).Pairwise QueryDistinct := by
    apply flatMap_pairwise _ _ (terminalStates_nodup source)
    · intro terminal _
      exact launch_pairwise _ _
    · intro left _ right _ hDifferent a ha b hb
      apply query_of_source_ne
      rw [launch_source ha, launch_source hb]
      intro equality
      exact hDifferent ((state_injective equality).2)
  have hRecovery : (outcomes.flatMap (recoveryBlock after)).Pairwise QueryDistinct := by
    apply flatMap_pairwise _ _ outcomes_nodup
    · intro outcome _
      exact recovery_pairwise after outcome hAfter hNo
    · intro left _ right _ hDifferent a ha b hb
      rcases recovery_source after left a ha with ⟨localA, hA⟩
      rcases recovery_source after right b hb with ⟨localB, hB⟩
      apply query_of_source_ne
      rw [hA, hB]
      intro equality
      apply hDifferent
      apply Fin.ext
      have hNames := (state_injective equality).1
      omega
  change (sourceRules source ++
    (terminalRules source after classify ++ outcomes.flatMap (recoveryBlock after))).Pairwise _
  rw [List.pairwise_append, List.pairwise_append]
  refine ⟨renamed_pairwise _ (fixed_injective 0) _ hSource, ⟨hTerminal, hRecovery, ?_⟩, ?_⟩
  · intro a ha b hb
    rcases terminal_source source after classify a ha with ⟨terminal, _, hA⟩
    rcases List.mem_flatMap.mp hb with ⟨outcome, _, hB⟩
    rcases recovery_source after outcome b hB with ⟨localState, equality⟩
    apply query_of_source_ne
    rw [hA, equality]
    intro h
    have hNames := (state_injective h).1
    omega
  · intro a ha b hb
    rcases renamed_source ha with ⟨original, member, hA⟩
    rcases List.mem_append.mp hb with hTerminal | hRecovery
    · rcases terminal_source source after classify b hTerminal with ⟨terminal, ht, hB⟩
      apply query_of_source_ne
      rw [hA, hB]
      intro h
      exact ((terminalStates_spec source terminal).mp ht).2 original member ((state_injective h).2)
    · rcases List.mem_flatMap.mp hRecovery with ⟨outcome, _, hB⟩
      rcases recovery_source after outcome b hB with ⟨localState, equality⟩
      apply query_of_source_ne
      rw [hA, equality]
      intro h
      have hNames := (state_injective h).1
      omega

/-- Each result state is stable independently of reachability or source well-formedness. -/
theorem noRuleAt_outcome (source after : WorkMachine) (classify : Nat → Fin 6)
    (outcome : Fin 6) : NoRuleAt (machine source after classify) outcome.val := by
  intro rule member
  rcases List.mem_append.mp member with hSource | hRest
  · rcases renamed_source hSource with ⟨original, _, equality⟩
    rw [equality]
    exact state_ne_outcome _ _ outcome
  · rcases List.mem_append.mp hRest with hTerminal | hRecovery
    · rcases terminal_source source after classify rule hTerminal with ⟨terminal, _, equality⟩
      rw [equality]
      exact state_ne_outcome _ _ outcome
    · rcases List.mem_flatMap.mp hRecovery with ⟨tag, _, hTag⟩
      rcases recovery_source after tag rule hTag with ⟨localState, equality⟩
      rw [equality]
      exact state_ne_outcome _ _ outcome

private theorem find_member (rules : List WorkRule) (selected : WorkRule)
    (hRules : rules.Pairwise QueryDistinct) (hMember : selected ∈ rules) :
    findWorkRule rules selected.sourceState selected.readSymbol = some selected := by
  induction rules with
  | nil => contradiction
  | cons first rest ih =>
      have hParts := List.pairwise_cons.mp hRules
      rcases List.mem_cons.mp hMember with hEqual | hRest
      · subst selected
        exact findWorkRule_cons_of_matches _ _ _ _ ⟨rfl, rfl⟩
      · rw [findWorkRule_cons_of_not_matches]
        · exact ih hParts.2 hRest
        · intro hMatch
          exact hParts.1 selected hRest (Prod.ext hMatch.1 hMatch.2)

private theorem running_not_halted (source after : WorkMachine) (classify : Nat → Fin 6)
    (name localState : Nat) (tape : WorkTape) :
    (machine source after classify).isHalted {state := state name localState, tape := tape} = false := by
  have hZero : state name localState ≠ 0 := state_ne_outcome name localState (0 : Fin 6)
  have hOne : state name localState ≠ 1 := state_ne_outcome name localState (1 : Fin 6)
  simpa only [WorkMachine.isHalted, machine, Bool.or_eq_false_iff, beq_eq_false_iff_ne] using
    And.intro hZero hOne

private theorem source_rule_mem (source after : WorkMachine) (classify : Nat → Fin 6)
    (rule : WorkRule) (h : rule ∈ source.rules) :
    renameRule (state 0) rule ∈ (machine source after classify).rules :=
  List.mem_append_left _ (List.mem_map.mpr ⟨rule, h, rfl⟩)

private theorem recovery_rule_mem (source after : WorkMachine) (classify : Nat → Fin 6)
    (outcome : Fin 6) (rule : WorkRule) (h : rule ∈ after.rules) :
    renameRule (state (outcome.val + 1)) rule ∈ (machine source after classify).rules :=
  List.mem_append_right _ (List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨outcome, outcomes_mem outcome, List.mem_append_left _ (List.mem_map.mpr ⟨rule, h, rfl⟩)⟩))

private theorem lift_step (original combined : WorkMachine) (name : Nat)
    (hPairwise : combined.rules.Pairwise QueryDistinct)
    (hMembers : ∀ rule ∈ original.rules, renameRule (state name) rule ∈ combined.rules)
    (hHalted : ∀ localState tape,
      combined.isHalted {state := state name localState, tape := tape} = false)
    (initial final : WorkConfiguration) (hStep : workStep? original initial = some final) :
    workStep? combined (renameConfiguration (state name) initial) =
      some (renameConfiguration (state name) final) := by
  rcases workStep?_some_exists original initial final hStep with ⟨rule, _, hFind, hFinal⟩
  have hMatches := findWorkRule_some_matches hFind
  have hLookup := find_member combined.rules (renameRule (state name) rule) hPairwise
    (hMembers rule (selected_member hFind))
  have hAt : findWorkRule combined.rules (state name initial.state) initial.tape.head =
      some (renameRule (state name) rule) := by
    simpa only [renameRule, hMatches.1, hMatches.2] using hLookup
  have h := workStep?_eq_apply_of_find combined (renameConfiguration (state name) initial)
    (renameRule (state name) rule) (hHalted initial.state initial.tape) hAt
  rw [hFinal]
  exact h

private theorem bridge_step (source after : WorkMachine) (classify : Nat → Fin 6)
    (hPairwise : (machine source after classify).rules.Pairwise QueryDistinct)
    (name localState target : Nat) (tape : WorkTape)
    (hMembers : ∀ symbol, launchRule (state name localState) target symbol ∈
      (machine source after classify).rules) :
    workStep? (machine source after classify) {state := state name localState, tape := tape} =
      some {state := target, tape := tape} := by
  have hFind := find_member _ (launchRule (state name localState) target tape.head)
    hPairwise (hMembers tape.head)
  have h := workStep?_eq_apply_of_find _ _ _
    (running_not_halted source after classify name localState tape) hFind
  exact h

private theorem launch_member (source target : Nat) (symbol : WorkSymbol) :
    launchRule source target symbol ∈ launchRules source target :=
  List.mem_map.mpr ⟨symbol, PipelineMachineSimulation.allWorkSymbols_mem symbol, rfl⟩

/-- The source, launch, continuation and finish execute in one finite machine.
The classification is retained even when the continuation erases all scratch. -/
theorem workRunExact (source after : WorkMachine) (classify : Nat → Fin 6)
    (sourceSteps afterSteps : Nat) (initial : WorkTape) (middle : WorkConfiguration) (finalTape : WorkTape)
    (hSourceRules : source.rules.Pairwise QueryDistinct)
    (hAfterRules : after.rules.Pairwise QueryDistinct) (hAfterNo : NoRuleAt after after.acceptState)
    (hSource : workRunExact? source sourceSteps (workStartConfiguration source initial) = some middle)
    (hTerminal : NoRuleAt source middle.state)
    (hAfter : workRunExact? after afterSteps (workStartConfiguration after middle.tape) =
      some {state := after.acceptState, tape := finalTape}) :
    workRunExact? (machine source after classify) (sourceSteps + 1 + afterSteps + 1)
      (workStartConfiguration (machine source after classify) initial) =
      some {state := (classify middle.state).val, tape := finalTape} := by
  have hPairwise := rules_pairwise source after classify hSourceRules hAfterRules hAfterNo
  let outcome := classify middle.state
  have hFirst := PipelineStageBridges.workRunExact?_transport source (machine source after classify)
    (state 0) (lift_step source _ 0 hPairwise (source_rule_mem source after classify)
      (running_not_halted source after classify 0))
    sourceSteps (workStartConfiguration source initial) middle hSource
  have hMember := reached_terminal_mem source sourceSteps initial middle hSource hTerminal
  have hLaunch := bridge_step source after classify hPairwise 0 middle.state
    (state (outcome.val + 1) after.startState) middle.tape (by
      intro symbol
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_flatMap.mpr
        ⟨middle.state, hMember, launch_member _ _ symbol⟩)))
  have hNext := PipelineStageBridges.workRunExact?_transport after (machine source after classify)
    (state (outcome.val + 1))
    (lift_step after _ _ hPairwise (recovery_rule_mem source after classify outcome)
      (running_not_halted source after classify _))
    afterSteps (workStartConfiguration after middle.tape)
    {state := after.acceptState, tape := finalTape} hAfter
  have hFinish := bridge_step source after classify hPairwise (outcome.val + 1) after.acceptState
    outcome.val finalTape (by
      intro symbol
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨outcome, outcomes_mem outcome, List.mem_append_right _ (launch_member _ _ symbol)⟩)))
  have hLaunchRun : workRunExact? (machine source after classify) 1
      (renameConfiguration (state 0) middle) =
      some (renameConfiguration (state (outcome.val + 1)) (workStartConfiguration after middle.tape)) := by
    simp only [workRunExact?, renameConfiguration, workStartConfiguration, hLaunch]
  have hFinishRun : workRunExact? (machine source after classify) 1
      (renameConfiguration (state (outcome.val + 1)) {state := after.acceptState, tape := finalTape}) =
      some {state := outcome.val, tape := finalTape} := by
    simp only [workRunExact?, renameConfiguration, hFinish]
  have hJoin := PipelineMachineSimulation.workRunExact?_compose _ _ _ _ _ _ hFirst hLaunchRun
  have hJoin := PipelineMachineSimulation.workRunExact?_compose _ _ _ _ _ _ hJoin hNext
  exact PipelineMachineSimulation.workRunExact?_compose _ _ _ _ _ _ hJoin hFinishRun

theorem run_compile_exact (source after : WorkMachine) (classify : Nat → Fin 6)
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
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (workRunExact source after classify sourceSteps afterSteps initial middle finalTape
      hSourceRules hAfterRules hAfterNo hSource hTerminal hAfter)

end PNP.Concrete.WorkMachineTerminalHandoff
