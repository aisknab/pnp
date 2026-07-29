/-
Copyright (c) 2026 PNP Labs.

Generic sequential composition for literal work machines.

The first and second machines are injectively renamed into disjoint pipeline
state namespaces.  A total nine-symbol bridge launches the second machine
from the first machine's accept endpoint.  This low-level module contains no
Cook--Levin or locked-NAND construction.
-/

import PNP.Concrete.PipelineStateNamespace
import PNP.Concrete.PipelineStageBridges

namespace PNP.Concrete.WorkMachineChain

open PipelineStateNamespace PipelineStageBridges

def firstState (state : Nat) : Nat := inputState state
def secondState (state : Nat) : Nat := simulationState state

theorem firstState_injective : Function.Injective firstState :=
  inputState_injective

theorem secondState_injective : Function.Injective secondState :=
  simulationState_injective

theorem firstState_ne_secondState (left right : Nat) :
    firstState left ≠ secondState right :=
  inputState_ne_simulationState left right

def bridgeRules (first second : WorkMachine) : List WorkRule :=
  launchRules (firstState first.acceptState) (secondState second.startState)

def rules (first second : WorkMachine) : List WorkRule :=
  bridgeRules first second ++
    (first.rules.map (renameRule firstState) ++
      second.rules.map (renameRule secondState))

def machine (first second : WorkMachine) : WorkMachine :=
  { rules := rules first second
    startState := firstState first.startState
    acceptState := secondState second.acceptState
    rejectState := secondState second.rejectState }

def QueryDistinct (left right : WorkRule) : Prop :=
  (left.sourceState, left.readSymbol) ≠
    (right.sourceState, right.readSymbol)

def NoRuleAtAccept (localMachine : WorkMachine) : Prop :=
  ∀ rule, rule ∈ localMachine.rules →
    rule.sourceState ≠ localMachine.acceptState

private theorem queryDistinct_of_source_ne (left right : WorkRule)
    (hSource : left.sourceState ≠ right.sourceState) :
    QueryDistinct left right := by
  intro hQuery
  exact hSource (congrArg Prod.fst hQuery)

private theorem renameRules_pairwise (encode : Nat -> Nat)
    (hInjective : Function.Injective encode) (localRules : List WorkRule)
    (hPairwise : localRules.Pairwise QueryDistinct) :
    (localRules.map (renameRule encode)).Pairwise QueryDistinct := by
  exact List.Pairwise.map (renameRule encode) (fun left right hDistinct => by
    intro hEqual
    apply hDistinct
    apply Prod.ext
    · exact hInjective (by
        simpa [renameRule] using congrArg Prod.fst hEqual)
    · simpa [renameRule] using congrArg Prod.snd hEqual) hPairwise

private theorem launchRules_pairwise (source target : Nat) :
    (launchRules source target).Pairwise QueryDistinct := by
  unfold launchRules PipelineMachineSimulation.allWorkSymbols
  simp [QueryDistinct, launchRule, WorkSymbol.blank,
    WorkSymbol.blankZero, WorkSymbol.blankOne, WorkSymbol.zeroBlank,
    WorkSymbol.zeroZero, WorkSymbol.zeroOne, WorkSymbol.oneBlank,
    WorkSymbol.oneZero, WorkSymbol.oneOne]

private theorem launchRules_source_eq {source target : Nat}
    {rule : WorkRule} (hMem : rule ∈ launchRules source target) :
    rule.sourceState = source := by
  rcases List.mem_map.mp hMem with ⟨symbol, _hSymbol, hRule⟩
  rw [← hRule]
  rfl

private theorem renamedRules_source {encode : Nat -> Nat}
    {localRules : List WorkRule} {rule : WorkRule}
    (hMem : rule ∈ localRules.map (renameRule encode)) :
    ∃ localRule ∈ localRules,
      rule.sourceState = encode localRule.sourceState := by
  rcases List.mem_map.mp hMem with ⟨localRule, hLocal, hRule⟩
  exact ⟨localRule, hLocal, by rw [← hRule]; rfl⟩

private theorem renamedRules_cross
    (leftEncode rightEncode : Nat -> Nat)
    (leftRules rightRules : List WorkRule)
    (hDisjoint : ∀ left right,
      leftEncode left ≠ rightEncode right) :
    ∀ leftRule ∈ leftRules.map (renameRule leftEncode),
      ∀ rightRule ∈ rightRules.map (renameRule rightEncode),
        QueryDistinct leftRule rightRule := by
  intro leftRule hLeft rightRule hRight
  rcases renamedRules_source hLeft with
    ⟨leftLocal, _hLeftLocal, hLeftSource⟩
  rcases renamedRules_source hRight with
    ⟨rightLocal, _hRightLocal, hRightSource⟩
  apply queryDistinct_of_source_ne
  rw [hLeftSource, hRightSource]
  exact hDisjoint leftLocal.sourceState rightLocal.sourceState

private theorem launchRenamed_cross (source target : Nat)
    (encode : Nat -> Nat) (localRules : List WorkRule)
    (hSource : ∀ localRule ∈ localRules,
      source ≠ encode localRule.sourceState) :
    ∀ bridgeRule ∈ launchRules source target,
      ∀ componentRule ∈ localRules.map (renameRule encode),
        QueryDistinct bridgeRule componentRule := by
  intro bridgeRule hBridge componentRule hComponent
  rcases renamedRules_source hComponent with
    ⟨localRule, hLocal, hComponentSource⟩
  apply queryDistinct_of_source_ne
  rw [launchRules_source_eq hBridge, hComponentSource]
  exact hSource localRule hLocal

theorem rules_pairwise_query_distinct (first second : WorkMachine)
    (hFirst : first.rules.Pairwise QueryDistinct)
    (hSecond : second.rules.Pairwise QueryDistinct)
    (hFirstAccept : NoRuleAtAccept first) :
    (rules first second).Pairwise QueryDistinct := by
  have hBridge := launchRules_pairwise
    (firstState first.acceptState) (secondState second.startState)
  have hFirstRenamed := renameRules_pairwise firstState firstState_injective
    first.rules hFirst
  have hSecondRenamed := renameRules_pairwise secondState
    secondState_injective second.rules hSecond
  have hComponents :
      (first.rules.map (renameRule firstState) ++
        second.rules.map (renameRule secondState)).Pairwise QueryDistinct := by
    rw [List.pairwise_append]
    exact ⟨hFirstRenamed, hSecondRenamed,
      renamedRules_cross firstState secondState first.rules second.rules
        firstState_ne_secondState⟩
  have hBridgeFirst := launchRenamed_cross
    (firstState first.acceptState) (secondState second.startState)
    firstState first.rules (by
      intro localRule hLocal hEqual
      exact hFirstAccept localRule hLocal
        (firstState_injective hEqual).symm)
  have hBridgeSecond := launchRenamed_cross
    (firstState first.acceptState) (secondState second.startState)
    secondState second.rules (by
      intro localRule _hLocal
      exact firstState_ne_secondState _ _)
  unfold rules bridgeRules
  rw [List.pairwise_append]
  refine ⟨hBridge, hComponents, ?_⟩
  intro bridge hBridgeMem component hComponent
  simp only [List.mem_append] at hComponent
  rcases hComponent with hFirstComponent | hSecondComponent
  · exact hBridgeFirst bridge hBridgeMem component hFirstComponent
  · exact hBridgeSecond bridge hBridgeMem component hSecondComponent

theorem noRuleAtAccept (first second : WorkMachine)
    (hSecond : NoRuleAtAccept second) :
    NoRuleAtAccept (machine first second) := by
  intro rule hRule
  simp only [machine, rules, bridgeRules, List.mem_append] at hRule
  rcases hRule with hBridge | hFirst | hSecondRule
  · intro hSource
    have hBridgeSource := launchRules_source_eq hBridge
    rw [hBridgeSource] at hSource
    exact firstState_ne_secondState _ _ hSource
  · rcases renamedRules_source hFirst with
      ⟨localRule, _hLocal, hSource⟩
    intro hEqual
    rw [hSource] at hEqual
    exact firstState_ne_secondState _ _ hEqual
  · rcases renamedRules_source hSecondRule with
      ⟨localRule, hLocal, hSource⟩
    intro hEqual
    rw [hSource] at hEqual
    exact hSecond localRule hLocal (secondState_injective hEqual)

theorem machine_acceptState_ne_rejectState (first second : WorkMachine)
    (hSecond : second.acceptState ≠ second.rejectState) :
    (machine first second).acceptState ≠
      (machine first second).rejectState := by
  intro h
  exact hSecond (secondState_injective h)

private theorem nat_beq_false_of_ne (left right : Nat)
    (h : left ≠ right) : (left == right) = false := by
  cases hBool : (left == right) with
  | false => rfl
  | true => exact False.elim (h ((nat_beq_true_iff left right).mp hBool))

private theorem state_ne_accept_of_not_halted
    (source : WorkMachine) (config : WorkConfiguration)
    (hHalted : source.isHalted config = false) :
    config.state ≠ source.acceptState := by
  intro hState
  unfold WorkMachine.isHalted at hHalted
  rw [hState, (nat_beq_true_iff _ _).mpr rfl] at hHalted
  contradiction

private theorem state_ne_reject_of_not_halted
    (source : WorkMachine) (config : WorkConfiguration)
    (hHalted : source.isHalted config = false) :
    config.state ≠ source.rejectState := by
  intro hState
  unfold WorkMachine.isHalted at hHalted
  rw [hState, (nat_beq_true_iff _ _).mpr rfl] at hHalted
  simp at hHalted

theorem machine_isHalted_first_false (first second : WorkMachine)
    (config : WorkConfiguration) :
    (machine first second).isHalted
      (renameConfiguration firstState config) = false := by
  unfold WorkMachine.isHalted machine renameConfiguration
  rw [nat_beq_false_of_ne _ _ (firstState_ne_secondState _ _),
    nat_beq_false_of_ne _ _ (firstState_ne_secondState _ _)]
  rfl

theorem machine_isHalted_second_false_of_local
    (first second : WorkMachine) (config : WorkConfiguration)
    (hLocal : second.isHalted config = false) :
    (machine first second).isHalted
      (renameConfiguration secondState config) = false := by
  have hAccept := state_ne_accept_of_not_halted second config hLocal
  have hReject := state_ne_reject_of_not_halted second config hLocal
  unfold WorkMachine.isHalted machine renameConfiguration
  rw [nat_beq_false_of_ne _ _ (fun h => hAccept (secondState_injective h)),
    nat_beq_false_of_ne _ _ (fun h => hReject (secondState_injective h))]
  rfl

theorem findWorkRule_first_of_some (first second : WorkMachine)
    (state : Nat) (symbol : WorkSymbol) (rule : WorkRule)
    (hAccept : state ≠ first.acceptState)
    (hFind : findWorkRule first.rules state symbol = some rule) :
    findWorkRule (machine first second).rules
        (firstState state) symbol =
      some (renameRule firstState rule) := by
  have hBridge : findWorkRule (bridgeRules first second)
      (firstState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro h
    exact hAccept (firstState_injective h).symm
  have hRenamed := findWorkRule_rename firstState firstState_injective
    first.rules state symbol
  rw [hFind] at hRenamed
  have hSecondRules : findWorkRule
      (second.rules.map (renameRule secondState))
      (firstState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact Ne.symm (firstState_ne_secondState _ _)
  unfold machine rules
  rw [findWorkRule_append_of_none _ _ _ _ hBridge]
  exact findWorkRule_append_of_some _ _ _ _ _ hRenamed

theorem findWorkRule_second_of_some (first second : WorkMachine)
    (state : Nat) (symbol : WorkSymbol) (rule : WorkRule)
    (hFind : findWorkRule second.rules state symbol = some rule) :
    findWorkRule (machine first second).rules
        (secondState state) symbol =
      some (renameRule secondState rule) := by
  have hBridge : findWorkRule (bridgeRules first second)
      (secondState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact firstState_ne_secondState _ _
  have hFirstRules : findWorkRule
      (first.rules.map (renameRule firstState))
      (secondState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact firstState_ne_secondState _ _
  have hRenamed := findWorkRule_rename secondState secondState_injective
    second.rules state symbol
  rw [hFind] at hRenamed
  unfold machine rules
  rw [findWorkRule_append_of_none _ _ _ _ hBridge,
    findWorkRule_append_of_none _ _ _ _ hFirstRules]
  exact hRenamed

private theorem findWorkRule_none_of_workStep_none
    (source : WorkMachine) (config : WorkConfiguration)
    (hHalted : source.isHalted config = false)
    (hStep : workStep? source config = none) :
    findWorkRule source.rules config.state config.tape.head = none := by
  unfold workStep? at hStep
  rw [hHalted] at hStep
  cases hFind : findWorkRule source.rules config.state config.tape.head with
  | none => rfl
  | some rule =>
      rw [hFind] at hStep
      contradiction

private theorem findWorkRule_first_of_none (first second : WorkMachine)
    (state : Nat) (symbol : WorkSymbol)
    (hAccept : state ≠ first.acceptState)
    (hFind : findWorkRule first.rules state symbol = none) :
    findWorkRule (machine first second).rules (firstState state) symbol =
      none := by
  have hBridge : findWorkRule (bridgeRules first second)
      (firstState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro h
    exact hAccept (firstState_injective h).symm
  have hFirst := findWorkRule_rename firstState firstState_injective
    first.rules state symbol
  rw [hFind] at hFirst
  have hSecond : findWorkRule
      (second.rules.map (renameRule secondState))
      (firstState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact Ne.symm (firstState_ne_secondState _ _)
  unfold machine rules
  rw [findWorkRule_append_of_none _ _ _ _ hBridge,
    findWorkRule_append_of_none _ _ _ _ hFirst]
  exact hSecond

private theorem findWorkRule_second_of_none (first second : WorkMachine)
    (state : Nat) (symbol : WorkSymbol)
    (hFind : findWorkRule second.rules state symbol = none) :
    findWorkRule (machine first second).rules (secondState state) symbol =
      none := by
  have hBridge : findWorkRule (bridgeRules first second)
      (secondState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact firstState_ne_secondState _ _
  have hFirst : findWorkRule
      (first.rules.map (renameRule firstState))
      (secondState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact firstState_ne_secondState _ _
  have hSecond := findWorkRule_rename secondState secondState_injective
    second.rules state symbol
  rw [hFind] at hSecond
  unfold machine rules
  rw [findWorkRule_append_of_none _ _ _ _ hBridge,
    findWorkRule_append_of_none _ _ _ _ hFirst]
  exact hSecond

private theorem first_workStep_none_of_local (first second : WorkMachine)
    (config : WorkConfiguration)
    (hAccept : config.state ≠ first.acceptState)
    (hLocalHalted : first.isHalted config = false)
    (hLocalStep : workStep? first config = none) :
    workStep? (machine first second)
        (renameConfiguration firstState config) = none := by
  have hFind := findWorkRule_none_of_workStep_none first config
    hLocalHalted hLocalStep
  have hGlobalFind := findWorkRule_first_of_none first second
    config.state config.tape.head hAccept hFind
  unfold workStep?
  rw [machine_isHalted_first_false first second config]
  change
    (match findWorkRule (machine first second).rules
        (firstState config.state) config.tape.head with
     | none => none
     | some rule => some (applyWorkRule rule
         (renameConfiguration firstState config))) = none
  rw [hGlobalFind]

private theorem second_workStep_none_of_local (first second : WorkMachine)
    (config : WorkConfiguration)
    (hLocalHalted : second.isHalted config = false)
    (hLocalStep : workStep? second config = none) :
    workStep? (machine first second)
        (renameConfiguration secondState config) = none := by
  have hFind := findWorkRule_none_of_workStep_none second config
    hLocalHalted hLocalStep
  have hGlobalFind := findWorkRule_second_of_none first second
    config.state config.tape.head hFind
  unfold workStep?
  rw [machine_isHalted_second_false_of_local first second config
    hLocalHalted]
  change
    (match findWorkRule (machine first second).rules
        (secondState config.state) config.tape.head with
     | none => none
     | some rule => some (applyWorkRule rule
         (renameConfiguration secondState config))) = none
  rw [hGlobalFind]

theorem first_workStep_of_some (first second : WorkMachine)
    (config next : WorkConfiguration)
    (hStep : workStep? first config = some next) :
    workStep? (machine first second)
        (renameConfiguration firstState config) =
      some (renameConfiguration firstState next) := by
  rcases workStep?_some_exists first config next hStep with
    ⟨rule, hHalted, hFind, hNext⟩
  have hAccept := state_ne_accept_of_not_halted first config hHalted
  have hGlobalHalted := machine_isHalted_first_false first second config
  have hGlobalFind := findWorkRule_first_of_some first second
    config.state config.tape.head rule hAccept hFind
  have hGlobalStep := workStep?_eq_apply_of_find (machine first second)
    (renameConfiguration firstState config) (renameRule firstState rule)
    hGlobalHalted hGlobalFind
  calc
    workStep? (machine first second) (renameConfiguration firstState config) =
        some (applyWorkRule (renameRule firstState rule)
          (renameConfiguration firstState config)) := hGlobalStep
    _ = some (renameConfiguration firstState (applyWorkRule rule config)) :=
      congrArg Option.some (applyWorkRule_rename firstState rule config)
    _ = some (renameConfiguration firstState next) :=
      congrArg (fun value => some (renameConfiguration firstState value))
        hNext.symm

theorem second_workStep_of_some (first second : WorkMachine)
    (config next : WorkConfiguration)
    (hStep : workStep? second config = some next) :
    workStep? (machine first second)
        (renameConfiguration secondState config) =
      some (renameConfiguration secondState next) := by
  rcases workStep?_some_exists second config next hStep with
    ⟨rule, hHalted, hFind, hNext⟩
  have hGlobalHalted := machine_isHalted_second_false_of_local
    first second config hHalted
  have hGlobalFind := findWorkRule_second_of_some first second
    config.state config.tape.head rule hFind
  have hGlobalStep := workStep?_eq_apply_of_find (machine first second)
    (renameConfiguration secondState config) (renameRule secondState rule)
    hGlobalHalted hGlobalFind
  calc
    workStep? (machine first second) (renameConfiguration secondState config) =
        some (applyWorkRule (renameRule secondState rule)
          (renameConfiguration secondState config)) := hGlobalStep
    _ = some (renameConfiguration secondState (applyWorkRule rule config)) :=
      congrArg Option.some (applyWorkRule_rename secondState rule config)
    _ = some (renameConfiguration secondState next) :=
      congrArg (fun value => some (renameConfiguration secondState value))
        hNext.symm

theorem launch_workStep (first second : WorkMachine) (tape : WorkTape) :
    workStep? (machine first second)
        (renameConfiguration firstState
          { state := first.acceptState, tape := tape }) =
      some (renameConfiguration secondState
        { state := second.startState, tape := tape }) := by
  let final : WorkConfiguration :=
    { state := first.acceptState, tape := tape }
  have hHalted := machine_isHalted_first_false first second final
  have hLaunch := findWorkRule_launchRules
    (firstState first.acceptState) (secondState second.startState) tape.head
  have hFind : findWorkRule (machine first second).rules
      (firstState first.acceptState) tape.head =
        some (launchRule (firstState first.acceptState)
          (secondState second.startState) tape.head) := by
    unfold machine rules bridgeRules
    exact findWorkRule_append_of_some _ _ _ _ _ hLaunch
  have hStep := workStep?_eq_apply_of_find (machine first second)
    (renameConfiguration firstState final)
    (launchRule (firstState first.acceptState)
      (secondState second.startState) tape.head) hHalted hFind
  simpa [final, launchRule, applyWorkRule, WorkTape.write, WorkTape.move,
    renameConfiguration] using hStep

theorem workRunExact (first second : WorkMachine)
    (firstSteps secondSteps : Nat)
    (firstInitial firstFinal secondFinal : WorkConfiguration)
    (hFirst : workRunExact? first firstSteps firstInitial = some firstFinal)
    (hFirstAccept : firstFinal.state = first.acceptState)
    (hSecond : workRunExact? second secondSteps
      { state := second.startState, tape := firstFinal.tape } =
        some secondFinal) :
    workRunExact? (machine first second) (firstSteps + 1 + secondSteps)
        (renameConfiguration firstState firstInitial) =
      some (renameConfiguration secondState secondFinal) := by
  have hFirstTransport := PipelineStageBridges.workRunExact?_transport
    first (machine first second) firstState (first_workStep_of_some first second)
    firstSteps firstInitial firstFinal hFirst
  let firstFinalRenamed := renameConfiguration firstState firstFinal
  let secondInitial : WorkConfiguration :=
    { state := second.startState, tape := firstFinal.tape }
  let secondInitialRenamed := renameConfiguration secondState secondInitial
  have hLaunch : workRunExact? (machine first second) 1 firstFinalRenamed =
      some secondInitialRenamed := by
    have hShape : firstFinal =
        { state := first.acceptState, tape := firstFinal.tape } := by
      cases firstFinal with
      | mk state tape =>
          simp only at hFirstAccept ⊢
          exact congrArg (fun nextState =>
            ({ state := nextState, tape := tape } : WorkConfiguration))
            hFirstAccept
    dsimp [firstFinalRenamed, secondInitialRenamed, secondInitial]
    rw [hShape]
    change
      (match workStep? (machine first second)
          (renameConfiguration firstState
            { state := first.acceptState, tape := firstFinal.tape }) with
       | none => none
       | some next => workRunExact? (machine first second) 0 next) = _
    have hStep := launch_workStep first second firstFinal.tape
    rw [hStep]
    rfl
  have hSecondTransport := PipelineStageBridges.workRunExact?_transport
    second (machine first second) secondState
    (second_workStep_of_some first second) secondSteps secondInitial
    secondFinal hSecond
  have h01 := PipelineMachineSimulation.workRunExact?_compose
    (machine first second) firstSteps 1
    (renameConfiguration firstState firstInitial) firstFinalRenamed
    secondInitialRenamed hFirstTransport hLaunch
  have h02 := PipelineMachineSimulation.workRunExact?_compose
    (machine first second) (firstSteps + 1) secondSteps
    (renameConfiguration firstState firstInitial) secondInitialRenamed
    (renameConfiguration secondState secondFinal) h01 hSecondTransport
  simpa [Nat.add_assoc] using h02

end PNP.Concrete.WorkMachineChain
