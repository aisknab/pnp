/-
Copyright (c) 2026 PNP Labs.

Literal completion of the first canonical Cook--Levin clause.

The machine in this file extends BuilderFirstLiteralPrefix by appending the
remaining positive variables one and two and the first clause terminator.  It
emits only the canonical prefix through that clause.  It does not implement a
dynamic schedule cursor, emit the remaining formula, provide RawRefinement or
a polynomial reduction, decide CNF-SAT, or establish P = NP.
-/

import PNP.Concrete.CookLevinBuilderFirstLiteralPrefix

namespace PNP.Concrete

namespace CookLevin

namespace BuilderFirstClausePrefix

open PipelineTape PipelineStateNamespace PipelineStageBridges

/-! ### Internal sequential composition of literal work machines -/

namespace WorkChain

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

end WorkChain

/-! ### Fixed eight-token tail of the first canonical clause -/

namespace FirstClauseTailAppender

/-- The remaining tokens after positive variable zero: positive variable one,
positive variable two, and the first clause terminator. -/
def tailTokens : List CNFToken :=
  [.t, .t, .f, .t, .t, .t, .f, .finish]

theorem tailTokens_length : tailTokens.length = 8 := by rfl

/-- The existing literal appender with its requested token selected as the
distinguished start state. -/
def tokenMachine (token : CNFToken) : WorkMachine :=
  { rules := BuilderTokenAppender.machine.rules
    startState := BuilderTokenAppender.seekInputState token
    acceptState := BuilderTokenAppender.machine.acceptState
    rejectState := BuilderTokenAppender.machine.rejectState }

private theorem tokenMachine_rules_pairwise (token : CNFToken) :
    (tokenMachine token).rules.Pairwise WorkChain.QueryDistinct := by
  change BuilderTokenAppender.rules.Pairwise (fun left right =>
    (left.sourceState, left.readSymbol) ≠
      (right.sourceState, right.readSymbol))
  simpa using
    BuilderTokenAppender.rules_pairwise_query_distinct

private theorem tokenMachine_noRuleAtAccept (token : CNFToken) :
    WorkChain.NoRuleAtAccept (tokenMachine token) := by
  intro rule hRule
  change rule.sourceState ≠ BuilderTokenAppender.machine.acceptState
  change rule ∈ BuilderTokenAppender.machine.rules at hRule
  decide +revert

private theorem tokenMachine_accept_ne_reject (token : CNFToken) :
    (tokenMachine token).acceptState ≠ (tokenMachine token).rejectState := by
  exact BuilderTokenAppender.machine_acceptState_ne_rejectState

/-- Right-associated literal chaining of one selected appender per token. -/
def chainTokens : CNFToken → List CNFToken → WorkMachine
  | first, [] => tokenMachine first
  | first, next :: rest =>
      WorkChain.machine (tokenMachine first) (chainTokens next rest)

private theorem chainTokens_rules_pairwise
    (first : CNFToken) (rest : List CNFToken) :
    (chainTokens first rest).rules.Pairwise WorkChain.QueryDistinct := by
  induction rest generalizing first with
  | nil => exact tokenMachine_rules_pairwise first
  | cons next rest ih =>
      unfold chainTokens
      exact WorkChain.rules_pairwise_query_distinct
        (tokenMachine first) (chainTokens next rest)
        (tokenMachine_rules_pairwise first) (ih next)
        (tokenMachine_noRuleAtAccept first)

private theorem chainTokens_noRuleAtAccept
    (first : CNFToken) (rest : List CNFToken) :
    WorkChain.NoRuleAtAccept (chainTokens first rest) := by
  induction rest generalizing first with
  | nil => exact tokenMachine_noRuleAtAccept first
  | cons next rest ih =>
      unfold chainTokens
      exact WorkChain.noRuleAtAccept
        (tokenMachine first) (chainTokens next rest) (ih next)

private theorem chainTokens_accept_ne_reject
    (first : CNFToken) (rest : List CNFToken) :
    (chainTokens first rest).acceptState ≠
      (chainTokens first rest).rejectState := by
  induction rest generalizing first with
  | nil => exact tokenMachine_accept_ne_reject first
  | cons next rest ih =>
      unfold chainTokens
      exact WorkChain.machine_acceptState_ne_rejectState
        (tokenMachine first) (chainTokens next rest) (ih next)

/-- Exact work cost of the selected appender chain, including one launch
between adjacent copies. -/
def chainWorkSteps (input : BitString) (output : List CNFToken) :
    CNFToken → List CNFToken → Nat
  | _, [] => BuilderTokenAppender.workSteps input output
  | first, next :: rest =>
      BuilderTokenAppender.workSteps input output + 1 +
        chainWorkSteps input (output ++ [first]) next rest

private theorem tokenMachine_workRunExact (input : BitString)
    (outside : List WorkSymbol) (output : List CNFToken)
    (token : CNFToken) :
    workRunExact? (tokenMachine token)
        (BuilderTokenAppender.workSteps input output)
        (workStartConfiguration (tokenMachine token)
          (BuilderTokenAppender.workspaceTape input outside output)) =
      some
        { state := (tokenMachine token).acceptState
          tape := BuilderTokenAppender.workspaceTape input outside
            (output ++ [token]) } := by
  have hRun : ∀ steps config,
      workRunExact? (tokenMachine token) steps config =
        workRunExact? BuilderTokenAppender.machine steps config := by
    intro steps
    induction steps with
    | zero => intro config; rfl
    | succ steps ih =>
        intro config
        unfold workRunExact?
        have hStep : workStep? (tokenMachine token) config =
            workStep? BuilderTokenAppender.machine config := by
          rfl
        rw [hStep]
        split
        · rfl
        · exact ih _
  have hLocal := BuilderTokenAppender.appendToken_workRunExact
    input outside output token
  rw [hRun]
  simpa [tokenMachine, workStartConfiguration,
    BuilderTokenAppender.entryConfiguration,
    BuilderTokenAppender.finalConfiguration] using hLocal

theorem chainTokens_workRunExact (input : BitString)
    (outside : List WorkSymbol) (output : List CNFToken)
    (first : CNFToken) (rest : List CNFToken) :
    workRunExact? (chainTokens first rest)
        (chainWorkSteps input output first rest)
        (workStartConfiguration (chainTokens first rest)
          (BuilderTokenAppender.workspaceTape input outside output)) =
      some
        { state := (chainTokens first rest).acceptState
          tape := BuilderTokenAppender.workspaceTape input outside
            (output ++ (first :: rest)) } := by
  induction rest generalizing first output with
  | nil =>
      simpa [chainTokens, chainWorkSteps] using
        tokenMachine_workRunExact input outside output first
  | cons next rest ih =>
      let firstMachine := tokenMachine first
      let remainingMachine := chainTokens next rest
      let firstInitial := workStartConfiguration firstMachine
        (BuilderTokenAppender.workspaceTape input outside output)
      let firstFinal : WorkConfiguration :=
        { state := firstMachine.acceptState
          tape := BuilderTokenAppender.workspaceTape input outside
            (output ++ [first]) }
      let remainingFinal : WorkConfiguration :=
        { state := remainingMachine.acceptState
          tape := BuilderTokenAppender.workspaceTape input outside
            ((output ++ [first]) ++ (next :: rest)) }
      have hFirst : workRunExact? firstMachine
          (BuilderTokenAppender.workSteps input output) firstInitial =
        some firstFinal := by
        simpa [firstMachine, firstInitial, firstFinal] using
          tokenMachine_workRunExact input outside output first
      have hRemaining : workRunExact? remainingMachine
          (chainWorkSteps input (output ++ [first]) next rest)
          { state := remainingMachine.startState, tape := firstFinal.tape } =
        some remainingFinal := by
        simpa [remainingMachine, firstFinal, remainingFinal,
          workStartConfiguration] using
            ih (first := next) (output := output ++ [first])
      have hCombined := WorkChain.workRunExact firstMachine remainingMachine
        (BuilderTokenAppender.workSteps input output)
        (chainWorkSteps input (output ++ [first]) next rest)
        firstInitial firstFinal remainingFinal hFirst rfl hRemaining
      simpa [chainTokens, chainWorkSteps, firstMachine, remainingMachine,
        firstInitial, remainingFinal, workStartConfiguration,
        WorkChain.machine, renameConfiguration,
        List.append_assoc] using hCombined

private theorem chainTokens_rules_length
    (first : CNFToken) (rest : List CNFToken) :
    (chainTokens first rest).rules.length = 59 + 68 * rest.length := by
  induction rest generalizing first with
  | nil =>
      simpa [chainTokens, tokenMachine, BuilderTokenAppender.machine] using
        BuilderTokenAppender.rules_length
  | cons next rest ih =>
      unfold chainTokens WorkChain.machine WorkChain.rules
        WorkChain.bridgeRules launchRules
        PipelineMachineSimulation.allWorkSymbols
      simp [tokenMachine, BuilderTokenAppender.machine,
        BuilderTokenAppender.rules_length, ih]
      omega

/-- The concrete 535-rule first-clause tail appender. -/
def machine : WorkMachine :=
  chainTokens .t [.t, .f, .t, .t, .t, .f, .finish]

def workSteps (input : BitString) (output : List CNFToken) : Nat :=
  chainWorkSteps input output .t [.t, .f, .t, .t, .t, .f, .finish]

def finalConfiguration (input : BitString) (outside : List WorkSymbol)
    (output : List CNFToken) : WorkConfiguration :=
  { state := machine.acceptState
    tape := BuilderTokenAppender.workspaceTape input outside
      (output ++ tailTokens) }

theorem rules_length : machine.rules.length = 535 := by
  simpa [machine] using chainTokens_rules_length .t
    [.t, .f, .t, .t, .t, .f, .finish]

theorem rules_pairwise_query_distinct :
    machine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  exact chainTokens_rules_pairwise .t
    [.t, .f, .t, .t, .t, .f, .finish]

theorem machine_acceptState_ne_rejectState :
    machine.acceptState ≠ machine.rejectState := by
  exact chainTokens_accept_ne_reject .t
    [.t, .f, .t, .t, .t, .f, .finish]

theorem workRunExact (input : BitString) (outside : List WorkSymbol)
    (output : List CNFToken) :
    workRunExact? machine (workSteps input output)
        (workStartConfiguration machine
          (BuilderTokenAppender.workspaceTape input outside output)) =
      some (finalConfiguration input outside output) := by
  simpa [machine, workSteps, finalConfiguration, tailTokens] using
    chainTokens_workRunExact input outside output .t
      [.t, .f, .t, .t, .t, .f, .finish]

theorem finalTape_represents (input : BitString)
    (outside : List WorkSymbol) (output : List CNFToken) :
    Represents (Tape.ofInput input)
      (finalConfiguration input outside output).tape := by
  exact BuilderTokenAppender.workspaceTape_represents input outside
    (output ++ tailTokens)

end FirstClauseTailAppender

/-! ### Retained coordinate and complete first-clause machine -/

/-- Polynomial for the token opportunity immediately after the complete
first canonical clause. -/
def nextTokenSlotPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (formulaVariableCountPolynomial verifier) (.constant 12)

def nextTokenSlot {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  (nextTokenSlotPolynomial problem.verifier).eval problem.input.length

theorem nextTokenSlot_eq_formulaVariableSlotBound_add_twelve
    {language : Language} (problem : VerifierTableauProblem language) :
    nextTokenSlot problem = problem.formulaVariableSlotBound + 12 := by
  rfl

def nextBitSlot {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  2 * nextTokenSlot problem

def nextBitCursor {language : Language}
    (problem : VerifierTableauProblem language) :
    VerifierTableauProblem.FormulaBitCursor :=
  ⟨nextBitSlot problem⟩

theorem nextBitCursor_nextSlot {language : Language}
    (problem : VerifierTableauProblem language) :
    (nextBitCursor problem).nextSlot =
      2 * (problem.formulaVariableSlotBound + 12) := by
  rw [nextBitCursor, nextBitSlot,
    nextTokenSlot_eq_formulaVariableSlotBound_add_twelve]

private theorem firstLiteral_noRuleAtAccept {language : Language}
    (problem : VerifierTableauProblem language) :
    WorkChain.NoRuleAtAccept (BuilderFirstLiteralPrefix.machine problem) := by
  exact BuilderFirstLiteralPrefix.rule_source_ne_acceptState problem

private theorem evaluator_noRuleAtAccept {language : Language}
    (problem : VerifierTableauProblem language) :
    WorkChain.NoRuleAtAccept
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)) := by
  intro rule hRule
  exact Nat.ne_of_lt (BuilderUnaryPolynomial.rule_source_lt_acceptState
    (nextTokenSlotPolynomial problem.verifier) rule hRule)

private theorem tail_noRuleAtAccept :
    WorkChain.NoRuleAtAccept FirstClauseTailAppender.machine := by
  exact FirstClauseTailAppender.chainTokens_noRuleAtAccept .t
    [.t, .f, .t, .t, .t, .f, .finish]

/-- The fresh unary coordinate evaluator followed by the fixed first-clause
tail. -/
def evaluatorTailMachine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  WorkChain.machine
    (BuilderUnaryPolynomial.machine
      (nextTokenSlotPolynomial problem.verifier))
    FirstClauseTailAppender.machine

/-- One literal finite work machine from raw input through the complete first
canonical clause. Only the final tail appender contributes global halts. -/
def machine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  WorkChain.machine (BuilderFirstLiteralPrefix.machine problem)
    (evaluatorTailMachine problem)

def firstClauseTokens {language : Language}
    (problem : VerifierTableauProblem language) : List CNFToken :=
  BuilderFirstLiteralPrefix.firstLiteralTokens problem ++
    FirstClauseTailAppender.tailTokens

def finalOutside {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  BuilderUnaryPolynomial.finalOutsideLeft
    (nextTokenSlotPolynomial problem.verifier) problem.input
    (BuilderFirstLiteralPrefix.finalOutside problem)

def finalTape {language : Language}
    (problem : VerifierTableauProblem language) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input
    (finalOutside problem) (firstClauseTokens problem)

def finalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := (machine problem).acceptState
    tape := finalTape problem }

set_option maxRecDepth 1000000 in
theorem finalConfiguration_state {language : Language}
    (problem : VerifierTableauProblem language) :
    (finalConfiguration (language := language) problem).state =
      (machine (language := language) problem).acceptState :=
  Eq.refl _

def evaluatorTailWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderUnaryPolynomial.workSteps
      (nextTokenSlotPolynomial problem.verifier) problem.input + 1 +
    FirstClauseTailAppender.workSteps problem.input
      (BuilderFirstLiteralPrefix.firstLiteralTokens problem)

def workSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderFirstLiteralPrefix.workSteps problem + 1 +
    evaluatorTailWorkSteps problem

theorem rules_length {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).rules.length =
      1138 +
        BuilderUnaryPolynomial.ruleCount
          (BuilderCompleteHeader.widthPolynomial problem) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderBodyStartPrefix.nextTokenSlotPolynomial problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFirstLiteralPrefix.nextTokenSlotPolynomial
            problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (nextTokenSlotPolynomial problem.verifier) := by
  have hPrefix := BuilderFirstLiteralPrefix.rules_length problem
  have hEvaluator := BuilderUnaryPolynomial.rules_length
    (nextTokenSlotPolynomial problem.verifier)
  have hTail := FirstClauseTailAppender.rules_length
  have hPrefix' : (BuilderFirstLiteralPrefix.machine problem).rules.length =
      585 +
        BuilderUnaryPolynomial.ruleCount
          (BuilderCompleteHeader.widthPolynomial problem) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderBodyStartPrefix.nextTokenSlotPolynomial problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFirstLiteralPrefix.nextTokenSlotPolynomial
            problem.verifier) := by
    simpa [BuilderFirstLiteralPrefix.machine] using hPrefix
  have hEvaluator' :
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).rules.length =
      BuilderUnaryPolynomial.ruleCount
        (nextTokenSlotPolynomial problem.verifier) := by
    simpa [BuilderUnaryPolynomial.machine] using hEvaluator
  have hLaunch : ∀ source target,
      (launchRules source target).length = 9 := by
    intro source target
    rfl
  unfold machine evaluatorTailMachine WorkChain.machine WorkChain.rules
    WorkChain.bridgeRules
  simp only [List.length_append, List.length_map]
  rw [hPrefix', hEvaluator', hTail, hLaunch, hLaunch]
  omega

theorem rules_pairwise_query_distinct {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  have hTail := FirstClauseTailAppender.rules_pairwise_query_distinct
  have hEvaluator := BuilderUnaryPolynomial.rules_pairwise_query_distinct
    (nextTokenSlotPolynomial problem.verifier)
  have hInner := WorkChain.rules_pairwise_query_distinct
    (BuilderUnaryPolynomial.machine
      (nextTokenSlotPolynomial problem.verifier))
    FirstClauseTailAppender.machine hEvaluator hTail
    (evaluator_noRuleAtAccept problem)
  have hOuter := WorkChain.rules_pairwise_query_distinct
    (BuilderFirstLiteralPrefix.machine problem)
    (evaluatorTailMachine problem)
    (BuilderFirstLiteralPrefix.rules_pairwise_query_distinct problem)
    hInner (firstLiteral_noRuleAtAccept problem)
  exact hOuter

theorem machine_acceptState_ne_rejectState {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).acceptState ≠ (machine problem).rejectState := by
  exact WorkChain.machine_acceptState_ne_rejectState
    (BuilderFirstLiteralPrefix.machine problem)
    (evaluatorTailMachine problem)
    (WorkChain.machine_acceptState_ne_rejectState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier))
      FirstClauseTailAppender.machine
      FirstClauseTailAppender.machine_acceptState_ne_rejectState)

theorem finalTape_represents {language : Language}
    (problem : VerifierTableauProblem language) :
    Represents (Tape.ofInput problem.input) (finalTape problem) := by
  exact BuilderTokenAppender.workspaceTape_represents problem.input
    (finalOutside problem) (firstClauseTokens problem)

theorem prefix_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem)
        (BuilderFirstLiteralPrefix.workSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (renameConfiguration WorkChain.firstState
        (BuilderFirstLiteralPrefix.finalConfiguration problem)) := by
  have hTransport := PipelineStageBridges.workRunExact?_transport
    (BuilderFirstLiteralPrefix.machine problem) (machine problem)
    WorkChain.firstState
    (WorkChain.first_workStep_of_some
      (BuilderFirstLiteralPrefix.machine problem)
      (evaluatorTailMachine problem))
    (BuilderFirstLiteralPrefix.workSteps problem)
    (workStartConfiguration (BuilderFirstLiteralPrefix.machine problem)
      (rawInputWorkTape problem.input))
    (BuilderFirstLiteralPrefix.finalConfiguration problem)
    (BuilderFirstLiteralPrefix.workRunExact problem)
  simpa [machine, WorkChain.machine, workStartConfiguration,
    renameConfiguration] using hTransport

/-- The outer bridge preserves the complete first-literal tape while
launching the fresh coordinate evaluator. -/
theorem launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep? (machine problem)
        (renameConfiguration WorkChain.firstState
          (BuilderFirstLiteralPrefix.finalConfiguration problem)) =
      some (renameConfiguration WorkChain.secondState
        (workStartConfiguration (evaluatorTailMachine problem)
          (BuilderFirstLiteralPrefix.finalTape problem))) := by
  have hLaunch := WorkChain.launch_workStep
    (BuilderFirstLiteralPrefix.machine problem)
    (evaluatorTailMachine problem)
    (BuilderFirstLiteralPrefix.finalTape problem)
  simpa [machine, BuilderFirstLiteralPrefix.finalConfiguration,
    workStartConfiguration] using hLaunch

theorem evaluator_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact?
        (BuilderUnaryPolynomial.machine
          (nextTokenSlotPolynomial problem.verifier))
        (BuilderUnaryPolynomial.workSteps
          (nextTokenSlotPolynomial problem.verifier) problem.input)
        (BuilderUnaryPolynomial.initialConfiguration
          (nextTokenSlotPolynomial problem.verifier) problem.input
          (BuilderFirstLiteralPrefix.finalOutside problem)
          (BuilderFirstLiteralPrefix.firstLiteralTokens problem)) =
      some (BuilderUnaryPolynomial.finalConfiguration
        (nextTokenSlotPolynomial problem.verifier) problem.input
        (BuilderFirstLiteralPrefix.finalOutside problem)
        (BuilderFirstLiteralPrefix.firstLiteralTokens problem)) := by
  exact BuilderUnaryPolynomial.workRunExact
    (nextTokenSlotPolynomial problem.verifier) problem.input
    (BuilderFirstLiteralPrefix.finalOutside problem)
    (BuilderFirstLiteralPrefix.firstLiteralTokens problem)

theorem tail_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? FirstClauseTailAppender.machine
        (FirstClauseTailAppender.workSteps problem.input
          (BuilderFirstLiteralPrefix.firstLiteralTokens problem))
        (workStartConfiguration FirstClauseTailAppender.machine
          (BuilderTokenAppender.workspaceTape problem.input
            (finalOutside problem)
            (BuilderFirstLiteralPrefix.firstLiteralTokens problem))) =
      some (FirstClauseTailAppender.finalConfiguration problem.input
        (finalOutside problem)
        (BuilderFirstLiteralPrefix.firstLiteralTokens problem)) := by
  exact FirstClauseTailAppender.workRunExact problem.input
    (finalOutside problem)
    (BuilderFirstLiteralPrefix.firstLiteralTokens problem)

/-- The inner bridge preserves the evaluated workspace while launching the
fixed eight-token tail. -/
theorem evaluatorTail_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep? (evaluatorTailMachine problem)
        (renameConfiguration WorkChain.firstState
          (BuilderUnaryPolynomial.finalConfiguration
            (nextTokenSlotPolynomial problem.verifier) problem.input
            (BuilderFirstLiteralPrefix.finalOutside problem)
            (BuilderFirstLiteralPrefix.firstLiteralTokens problem))) =
      some (renameConfiguration WorkChain.secondState
        (workStartConfiguration FirstClauseTailAppender.machine
          (BuilderTokenAppender.workspaceTape problem.input
            (finalOutside problem)
            (BuilderFirstLiteralPrefix.firstLiteralTokens problem)))) := by
  have hLaunch := WorkChain.launch_workStep
    (BuilderUnaryPolynomial.machine
      (nextTokenSlotPolynomial problem.verifier))
    FirstClauseTailAppender.machine
    (BuilderTokenAppender.workspaceTape problem.input
      (finalOutside problem)
      (BuilderFirstLiteralPrefix.firstLiteralTokens problem))
  simpa [evaluatorTailMachine, finalOutside,
    BuilderUnaryPolynomial.finalConfiguration,
    workStartConfiguration] using hLaunch

private theorem evaluatorTail_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (evaluatorTailMachine problem)
        (evaluatorTailWorkSteps problem)
        (workStartConfiguration (evaluatorTailMachine problem)
          (BuilderFirstLiteralPrefix.finalTape problem)) =
      some
        { state := (evaluatorTailMachine problem).acceptState
          tape := finalTape problem } := by
  let evaluator := BuilderUnaryPolynomial.machine
    (nextTokenSlotPolynomial problem.verifier)
  let tail := FirstClauseTailAppender.machine
  let evaluatorInitial := BuilderUnaryPolynomial.initialConfiguration
    (nextTokenSlotPolynomial problem.verifier) problem.input
    (BuilderFirstLiteralPrefix.finalOutside problem)
    (BuilderFirstLiteralPrefix.firstLiteralTokens problem)
  let evaluatorFinal := BuilderUnaryPolynomial.finalConfiguration
    (nextTokenSlotPolynomial problem.verifier) problem.input
    (BuilderFirstLiteralPrefix.finalOutside problem)
    (BuilderFirstLiteralPrefix.firstLiteralTokens problem)
  let tailFinal := FirstClauseTailAppender.finalConfiguration problem.input
    (finalOutside problem)
    (BuilderFirstLiteralPrefix.firstLiteralTokens problem)
  have hEvaluator : workRunExact? evaluator
      (BuilderUnaryPolynomial.workSteps
        (nextTokenSlotPolynomial problem.verifier) problem.input)
      evaluatorInitial = some evaluatorFinal := by
    simpa [evaluator, evaluatorInitial, evaluatorFinal] using
      evaluator_workRunExact problem
  have hTail : workRunExact? tail
      (FirstClauseTailAppender.workSteps problem.input
        (BuilderFirstLiteralPrefix.firstLiteralTokens problem))
      { state := tail.startState, tape := evaluatorFinal.tape } =
        some tailFinal := by
    simpa [tail, evaluatorFinal, tailFinal, finalOutside,
      BuilderUnaryPolynomial.finalConfiguration,
      workStartConfiguration] using tail_workRunExact problem
  have hCombined := WorkChain.workRunExact evaluator tail
    (BuilderUnaryPolynomial.workSteps
      (nextTokenSlotPolynomial problem.verifier) problem.input)
    (FirstClauseTailAppender.workSteps problem.input
      (BuilderFirstLiteralPrefix.firstLiteralTokens problem))
    evaluatorInitial evaluatorFinal tailFinal hEvaluator rfl hTail
  simpa [evaluatorTailMachine, evaluatorTailWorkSteps, evaluator, tail,
    evaluatorInitial, tailFinal, BuilderFirstLiteralPrefix.finalTape,
    BuilderUnaryPolynomial.initialConfiguration,
    finalTape, firstClauseTokens,
    FirstClauseTailAppender.finalConfiguration,
    FirstClauseTailAppender.tailTokens, WorkChain.machine,
    workStartConfiguration, renameConfiguration, List.append_assoc] using
      hCombined

set_option maxRecDepth 3000 in
set_option maxHeartbeats 1200000 in
/-- Every raw input follows one exact successful trace through the first
canonical clause. -/
theorem workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem) (workSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (finalConfiguration problem) := by
  let prefixInitial := workStartConfiguration
    (BuilderFirstLiteralPrefix.machine problem)
    (rawInputWorkTape problem.input)
  let prefixFinal := BuilderFirstLiteralPrefix.finalConfiguration problem
  let suffixFinal : WorkConfiguration :=
    { state := (evaluatorTailMachine problem).acceptState
      tape := finalTape problem }
  have hPrefix : workRunExact? (BuilderFirstLiteralPrefix.machine problem)
      (BuilderFirstLiteralPrefix.workSteps problem) prefixInitial =
        some prefixFinal := by
    simpa [prefixInitial, prefixFinal] using
      BuilderFirstLiteralPrefix.workRunExact problem
  have hSuffix : workRunExact? (evaluatorTailMachine problem)
      (evaluatorTailWorkSteps problem)
      { state := (evaluatorTailMachine problem).startState,
        tape := prefixFinal.tape } = some suffixFinal := by
    simpa [prefixFinal, suffixFinal,
      BuilderFirstLiteralPrefix.finalConfiguration,
      workStartConfiguration] using evaluatorTail_workRunExact problem
  have hCombined := WorkChain.workRunExact
    (BuilderFirstLiteralPrefix.machine problem)
    (evaluatorTailMachine problem)
    (BuilderFirstLiteralPrefix.workSteps problem)
    (evaluatorTailWorkSteps problem)
    prefixInitial prefixFinal suffixFinal hPrefix rfl hSuffix
  simpa [machine, workSteps, prefixInitial, suffixFinal,
    finalConfiguration, WorkChain.machine, workStartConfiguration,
    renameConfiguration] using hCombined

/-! ### Exact first canonical clause -/

theorem firstClauseTokens_eq_canonical_prefix {language : Language}
    (problem : VerifierTableauProblem language) :
    firstClauseTokens problem =
      encodeUnaryTokens problem.FormulaWidth ++
        [.sep, .t, .f, .t, .t, .f, .t, .t, .t, .f, .finish] := by
  unfold firstClauseTokens
  rw [BuilderFirstLiteralPrefix.firstLiteralTokens_eq_canonical_prefix]
  simp [FirstClauseTailAppender.tailTokens, List.append_assoc]

private theorem finiteIndices_starts_zero (width : Nat)
    (hWidth : 0 < width) :
    ∃ rest, finiteIndices width = ⟨0, hWidth⟩ :: rest := by
  cases width with
  | zero => exact False.elim (Nat.not_lt_zero 0 hWidth)
  | succ width => exact ⟨(finiteIndices width).map Fin.succ, rfl⟩

private theorem scheduledShapeConstraints_starts_firstSymbol
    {language : Language} (problem : VerifierTableauProblem language) :
    let time : Fin problem.dimensions.timeCount :=
      ⟨0, problem.dimensions.timeCount_positive⟩
    let position : Fin
        (problem.dimensions.tapeWidth problem.tableauInputMode) :=
      ⟨0, problem.dimensions.tapeWidth_positive problem.tableauInputMode⟩
    ∃ rest,
      problem.scheduledShapeConstraints =
        some (problem.symbolShapeAt time position) :: rest := by
  dsimp
  let time : Fin problem.dimensions.timeCount :=
    ⟨0, problem.dimensions.timeCount_positive⟩
  let position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode) :=
    ⟨0, problem.dimensions.tapeWidth_positive problem.tableauInputMode⟩
  rcases finiteIndices_starts_zero problem.dimensions.timeCount
      problem.dimensions.timeCount_positive with ⟨times, hTimes⟩
  rcases finiteIndices_starts_zero
      (problem.dimensions.tapeWidth problem.tableauInputMode)
      (problem.dimensions.tapeWidth_positive problem.tableauInputMode) with
    ⟨positions, hPositions⟩
  refine ⟨(positions.map fun next =>
      some (problem.symbolShapeAt time next)) ++
      [some (problem.headShapeAt time), some (problem.stateShapeAt time)] ++
      times.flatMap fun next =>
        ((finiteIndices
          (problem.dimensions.tapeWidth problem.tableauInputMode)).map
            fun nextPosition =>
              some (problem.symbolShapeAt next nextPosition)) ++
          [some (problem.headShapeAt next), some (problem.stateShapeAt next)],
    ?_⟩
  unfold VerifierTableauProblem.scheduledShapeConstraints
  rw [hTimes]
  simp only [List.flatMap_cons]
  rw [hPositions]
  rfl

private theorem formulaConstraintSchedule_starts_firstSymbol
    {language : Language} (problem : VerifierTableauProblem language) :
    let time : Fin problem.dimensions.timeCount :=
      ⟨0, problem.dimensions.timeCount_positive⟩
    let position : Fin
        (problem.dimensions.tapeWidth problem.tableauInputMode) :=
      ⟨0, problem.dimensions.tapeWidth_positive problem.tableauInputMode⟩
    ∃ rest,
      problem.formulaConstraintSchedule =
        some (problem.symbolShapeAt time position) :: rest := by
  dsimp
  rcases scheduledShapeConstraints_starts_firstSymbol problem with
    ⟨rest, hRest⟩
  refine ⟨rest ++ problem.scheduledInitialConstraints ++
      problem.scheduledControlConstraints ++
      problem.scheduledPreservationConstraints ++
      [some (.require
        (problem.stateLiteral problem.finalTime problem.acceptingState))], ?_⟩
  unfold VerifierTableauProblem.formulaConstraintSchedule
  rw [hRest]
  simp [List.append_assoc]

private theorem formulaClauseSchedule_starts_firstShapeClause
    {language : Language} (problem : VerifierTableauProblem language) :
    let time : Fin problem.dimensions.timeCount :=
      ⟨0, problem.dimensions.timeCount_positive⟩
    let position : Fin
        (problem.dimensions.tapeWidth problem.tableauInputMode) :=
      ⟨0, problem.dimensions.tapeWidth_positive problem.tableauInputMode⟩
    ∃ rest,
      problem.formulaClauseSchedule =
        some (atLeastOneBoundedClause
          (problem.symbolVariables time position)) :: rest := by
  dsimp
  rcases formulaConstraintSchedule_starts_firstSymbol problem with
    ⟨constraints, hConstraints⟩
  rw [VerifierTableauProblem.formulaClauseSchedule, hConstraints]
  simp only [List.flatMap_cons]
  unfold VerifierTableauProblem.symbolShapeAt
  dsimp [VerifierTableauProblem.scheduledConstraintClauses,
    LocalConstraint.emit, exactlyOneBoundedClauses, FormulaSchedule.pad]
  exact ⟨_, rfl⟩

private theorem firstShapeClause_emit_eq
    {language : Language} (problem : VerifierTableauProblem language) :
    let time : Fin problem.dimensions.timeCount :=
      ⟨0, problem.dimensions.timeCount_positive⟩
    let position : Fin
        (problem.dimensions.tapeWidth problem.tableauInputMode) :=
      ⟨0, problem.dimensions.tapeWidth_positive problem.tableauInputMode⟩
    BoundedClause.emit
        (atLeastOneBoundedClause
          (problem.symbolVariables time position)) =
      [{ positive := true, variableIndex := 0 },
       { positive := true, variableIndex := 1 },
       { positive := true, variableIndex := 2 }] := by
  dsimp
  simp [BoundedClause.emit, atLeastOneBoundedClause,
    VerifierTableauProblem.symbolVariables, tapeSymbols, trueLiteral,
    BoundedLiteral.emit, VerifierTableauProblem.symbolLiteral,
    VariableLayout.symbolVariable, VariableLayout.symbolLocalIndex,
    VariableLayout.symbolBlock, VariableBlock.index,
    VariableLayout.flattenTwo, VariableLayout.tapeSymbolCode]

private theorem formulaClauseTokens_starts_firstClause
    {language : Language} (problem : VerifierTableauProblem language) :
    ∃ rest,
      problem.formulaClauseSchedule.flatMap problem.scheduledClauseTokens =
        some CNFToken.sep ::
        some CNFToken.t :: some CNFToken.f ::
        some CNFToken.t :: some CNFToken.t :: some CNFToken.f ::
        some CNFToken.t :: some CNFToken.t :: some CNFToken.t ::
        some CNFToken.f :: some CNFToken.finish :: rest := by
  rcases formulaClauseSchedule_starts_firstShapeClause problem with
    ⟨clauses, hClauses⟩
  rw [hClauses]
  simp only [List.flatMap_cons]
  dsimp [VerifierTableauProblem.scheduledClauseTokens]
  rw [firstShapeClause_emit_eq]
  simp only [encodeClauseTokens, encodeLiteralListTokens,
    encodeLiteralTokens, encodeUnaryTokens]
  unfold FormulaSchedule.pad
  exact ⟨_, rfl⟩

private theorem encodeCNFTokens_starts_firstClausePrefix
    {language : Language} (problem : VerifierTableauProblem language) :
    ∃ rest,
      encodeCNFTokens problem.formula =
        encodeUnaryTokens problem.FormulaWidth ++
          CNFToken.sep ::
          CNFToken.t :: CNFToken.f ::
          CNFToken.t :: CNFToken.t :: CNFToken.f ::
          CNFToken.t :: CNFToken.t :: CNFToken.t ::
          CNFToken.f :: CNFToken.finish :: rest := by
  rcases formulaClauseTokens_starts_firstClause problem with
    ⟨clauseTail, hClauseTail⟩
  refine ⟨FormulaSchedule.emit clauseTail ++ [CNFToken.finish], ?_⟩
  rw [← problem.formulaTokenSchedule_emit_eq_encodeCNFTokens]
  unfold VerifierTableauProblem.formulaTokenSchedule
  rw [FormulaSchedule.emit_append, FormulaSchedule.emit_append,
    FormulaSchedule.emit_pad, hClauseTail]
  simp [List.append_assoc]

/-- The finite machine output is exactly the canonical token prefix through
the complete first Cook--Levin clause. -/
theorem firstClauseTokens_eq_canonical_formula_prefix
    {language : Language} (problem : VerifierTableauProblem language) :
    ∃ rest, encodeCNFTokens problem.formula =
      firstClauseTokens problem ++ rest := by
  rcases encodeCNFTokens_starts_firstClausePrefix problem with
    ⟨rest, hRest⟩
  refine ⟨rest, ?_⟩
  rw [firstClauseTokens_eq_canonical_prefix]
  simpa [List.append_assoc] using hRest

private theorem encodeTokenPairs_append_local
    (left right : List CNFToken) :
    encodeTokenPairs (left ++ right) =
      encodeTokenPairs left ++ encodeTokenPairs right := by
  induction left with
  | nil => rfl
  | cons token rest ih =>
      cases token <;>
        simp [encodeTokenPairs, ih, List.append_assoc]

/-- The work output bits are the exact canonical encoding prefix through the
first complete clause. -/
theorem finalTokenBits_eq_encodedFormula_firstClause
    {language : Language} (problem : VerifierTableauProblem language) :
    encodeTokenPairs (firstClauseTokens problem) =
      problem.encodedFormula.take (2 * (problem.FormulaWidth + 12)) := by
  rcases firstClauseTokens_eq_canonical_formula_prefix problem with
    ⟨rest, hTokens⟩
  have hLength : (encodeTokenPairs (firstClauseTokens problem)).length =
      2 * (problem.FormulaWidth + 12) := by
    rw [encodeTokenPairs_length, firstClauseTokens_eq_canonical_prefix]
    rw [List.length_append, encodeUnaryTokens_length]
    simp
  let suffix := encodeTokenPairs rest ++ [false]
  have hShape : problem.encodedFormula =
      encodeTokenPairs (firstClauseTokens problem) ++ suffix := by
    simp only [VerifierTableauProblem.encodedFormula, encodeCNF]
    rw [hTokens, encodeTokenPairs_append_local]
    simp [suffix, List.append_assoc]
  rw [hShape, ← hLength]
  exact List.take_left.symm

/-! ### External bound and compiled execution -/

private def scalePolynomial (coefficient : Nat)
    (polynomial : NatPolynomial) : NatPolynomial :=
  .mul (.constant coefficient) polynomial

/-- External compiled-time polynomial for the complete first-clause prefix. -/
def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderFirstLiteralPrefix.rawTimeBound verifier)
    (.add (.constant 1158)
      (.add
        (scalePolynomial 6
          (BuilderUnaryPolynomial.workTimePolynomial
            (nextTokenSlotPolynomial verifier)))
        (.add (scalePolynomial 192 .variable)
          (scalePolynomial 96 (formulaWidthPolynomial verifier)))))

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderFirstLiteralPrefix.rawTimeBound problem.verifier).eval
          problem.input.length + 1158 +
        6 * BuilderUnaryPolynomial.workSteps
          (nextTokenSlotPolynomial problem.verifier) problem.input +
        192 * problem.input.length +
        96 * problem.FormulaWidth := by
  rw [rawTimeBound]
  simp only [NatPolynomial.eval_add, NatPolynomial.eval_constant,
    NatPolynomial.eval_mul, scalePolynomial,
    BuilderUnaryPolynomial.workTimePolynomial_eval,
    NatPolynomial.eval_variable]
  have hWidth :
      (formulaWidthPolynomial problem.verifier).eval problem.input.length =
        problem.FormulaWidth := by
    simpa [BitString.size] using problem.formulaWidthPolynomial_eval
  rw [hWidth]
  omega

private theorem appender_workSteps_le (input : BitString)
    (output : List CNFToken) :
    BuilderTokenAppender.workSteps input output ≤
      4 * input.length + 2 * output.length + 8 := by
  have hSource := BuilderTokenAppender.sourceCellCount_le input
  unfold BuilderTokenAppender.workSteps BuilderTokenAppender.halfSteps
  omega

private theorem tail_workSteps_le {language : Language}
    (problem : VerifierTableauProblem language) :
    FirstClauseTailAppender.workSteps problem.input
        (BuilderFirstLiteralPrefix.firstLiteralTokens problem) ≤
      32 * problem.input.length + 16 * problem.FormulaWidth + 191 := by
  let output0 := BuilderFirstLiteralPrefix.firstLiteralTokens problem
  let output1 := output0 ++ [.t]
  let output2 := output1 ++ [.t]
  let output3 := output2 ++ [.f]
  let output4 := output3 ++ [.t]
  let output5 := output4 ++ [.t]
  let output6 := output5 ++ [.t]
  let output7 := output6 ++ [.f]
  have hLength : output0.length = problem.FormulaWidth + 4 := by
    dsimp [output0]
    rw [BuilderFirstLiteralPrefix.firstLiteralTokens_eq_canonical_prefix]
    simp [encodeUnaryTokens_length]
  have hLength1 : output1.length = problem.FormulaWidth + 5 := by
    simp [output1, hLength]
  have hLength2 : output2.length = problem.FormulaWidth + 6 := by
    simp [output2, hLength1]
  have hLength3 : output3.length = problem.FormulaWidth + 7 := by
    simp [output3, hLength2]
  have hLength4 : output4.length = problem.FormulaWidth + 8 := by
    simp [output4, hLength3]
  have hLength5 : output5.length = problem.FormulaWidth + 9 := by
    simp [output5, hLength4]
  have hLength6 : output6.length = problem.FormulaWidth + 10 := by
    simp [output6, hLength5]
  have hLength7 : output7.length = problem.FormulaWidth + 11 := by
    simp [output7, hLength6]
  have h0 := appender_workSteps_le problem.input output0
  have h1 := appender_workSteps_le problem.input output1
  have h2 := appender_workSteps_le problem.input output2
  have h3 := appender_workSteps_le problem.input output3
  have h4 := appender_workSteps_le problem.input output4
  have h5 := appender_workSteps_le problem.input output5
  have h6 := appender_workSteps_le problem.input output6
  have h7 := appender_workSteps_le problem.input output7
  rw [hLength] at h0
  rw [hLength1] at h1
  rw [hLength2] at h2
  rw [hLength3] at h3
  rw [hLength4] at h4
  rw [hLength5] at h5
  rw [hLength6] at h6
  rw [hLength7] at h7
  unfold FirstClauseTailAppender.workSteps
  simp only [FirstClauseTailAppender.chainWorkSteps]
  change
    BuilderTokenAppender.workSteps problem.input output0 + 1 +
      (BuilderTokenAppender.workSteps problem.input output1 + 1 +
      (BuilderTokenAppender.workSteps problem.input output2 + 1 +
      (BuilderTokenAppender.workSteps problem.input output3 + 1 +
      (BuilderTokenAppender.workSteps problem.input output4 + 1 +
      (BuilderTokenAppender.workSteps problem.input output5 + 1 +
      (BuilderTokenAppender.workSteps problem.input output6 + 1 +
        BuilderTokenAppender.workSteps problem.input output7)))))) ≤ _
  omega

theorem rawTimeBound_le {language : Language}
    (problem : VerifierTableauProblem language) :
    6 * workSteps problem ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hPrefix := BuilderFirstLiteralPrefix.rawTimeBound_le problem
  have hTail := tail_workSteps_le problem
  rw [rawTimeBound_eval]
  unfold workSteps evaluatorTailWorkSteps
  omega

private theorem finalConfiguration_isHalted {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).isHalted (finalConfiguration problem) = true := by
  unfold WorkMachine.isHalted
  rw [finalConfiguration_state]
  rw [(nat_beq_true_iff _ _).mpr rfl]
  rfl

theorem run_compile_exact {language : Language}
    (problem : VerifierTableauProblem language) :
    run (compileWorkMachine (machine problem)) (6 * workSteps problem)
        (encodeWorkConfiguration
          (workStartConfiguration (machine problem)
            (rawInputWorkTape problem.input))) =
      encodeWorkConfiguration (finalConfiguration problem) := by
  exact run_compileWorkMachine_mul_of_workRunExact (machine problem)
    (workSteps problem)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (finalConfiguration problem) (workRunExact problem)

theorem run_compile_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language) :
    run (compileWorkMachine (machine problem))
        ((rawTimeBound problem.verifier).eval problem.input.length)
        (encodeWorkConfiguration
          (workStartConfiguration (machine problem)
            (rawInputWorkTape problem.input))) =
      encodeWorkConfiguration (finalConfiguration problem) := by
  exact run_compileWorkMachine_of_workRunExact_halted_le
    (machine problem) (workSteps problem)
    ((rawTimeBound problem.verifier).eval problem.input.length)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (finalConfiguration problem) (workRunExact problem)
    (finalConfiguration_isHalted problem) (rawTimeBound_le problem)

theorem run_compile_rawTimeBound_blankEquivalent {language : Language}
    (problem : VerifierTableauProblem language) :
    Configuration.BlankEquivalent
      (run (compileWorkMachine (machine problem))
        ((rawTimeBound problem.verifier).eval problem.input.length)
        (startConfig (compileWorkMachine (machine problem)) problem.input))
      (encodeWorkConfiguration (finalConfiguration problem)) := by
  have hStart := startConfig_compileWorkMachine_blankEquivalent
    (machine problem) problem.input
  have hRun := run_blankEquivalent (compileWorkMachine (machine problem))
    ((rawTimeBound problem.verifier).eval problem.input.length) hStart
  rw [run_compile_rawTimeBound problem] at hRun
  exact hRun

private theorem blankEquivalent_state {first second : Configuration}
    (hEquivalent : Configuration.BlankEquivalent first second) :
    first.state = second.state := by
  exact hEquivalent.1

private theorem blankEquivalent_accept_of_encoded
    (localMachine : WorkMachine) (first : Configuration)
    (final : WorkConfiguration)
    (hEquivalent : Configuration.BlankEquivalent first
      (encodeWorkConfiguration final))
    (hFinal : final.state = localMachine.acceptState) :
    first.state = (compileWorkMachine localMachine).acceptState := by
  have hState := blankEquivalent_state hEquivalent
  have hEncoded := (encodeWorkConfiguration_accept_iff
    localMachine final).mpr hFinal
  exact hState.trans hEncoded

set_option maxRecDepth 100000 in
theorem boundedDecide_compile_accept {language : Language}
    (problem : VerifierTableauProblem language) :
    boundedDecide (compileWorkMachine (machine problem))
        ((rawTimeBound problem.verifier).eval problem.input.length)
        problem.input = .accept := by
  apply (boundedDecide_accept_iff_final
    (compileWorkMachine (machine problem))
    ((rawTimeBound problem.verifier).eval problem.input.length)
    problem.input).mpr
  have hFinal : (finalConfiguration problem).state =
      (machine problem).acceptState := by
    exact finalConfiguration_state problem
  exact blankEquivalent_accept_of_encoded (machine problem) _
    (finalConfiguration problem)
    (run_compile_rawTimeBound_blankEquivalent problem) hFinal

theorem boundedDecide_compile_ne_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    boundedDecide (compileWorkMachine (machine problem))
        ((rawTimeBound problem.verifier).eval problem.input.length)
        problem.input ≠ .timeout := by
  rw [boundedDecide_compile_accept]
  intro impossible
  contradiction

theorem workBoundedDecide_accept {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem) (workSteps problem)
      (rawInputWorkTape problem.input) = .accept := by
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact (machine problem) (workSteps problem)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (finalConfiguration problem) (workRunExact problem)]
  dsimp only
  rw [finalConfiguration_state]
  rw [(nat_beq_true_iff _ _).mpr rfl]
  rfl

/-! ### Fail-closed trace boundaries -/

private theorem nat_beq_false_of_ne (left right : Nat)
    (h : left ≠ right) : (left == right) = false := by
  cases hBool : (left == right) with
  | false => rfl
  | true =>
      exact False.elim (h ((nat_beq_true_iff left right).mp hBool))

private theorem machine_isHalted_prefix_false {language : Language}
    (problem : VerifierTableauProblem language)
    (config : WorkConfiguration) :
    (machine problem).isHalted
        (renameConfiguration WorkChain.firstState config) = false := by
  unfold WorkMachine.isHalted machine WorkChain.machine renameConfiguration
  rw [nat_beq_false_of_ne _ _
      (WorkChain.firstState_ne_secondState config.state _),
    nat_beq_false_of_ne _ _
      (WorkChain.firstState_ne_secondState config.state _)]
  rfl

private theorem verdict_timeout_of_not_halted {language : Language}
    (problem : VerifierTableauProblem language)
    (config : WorkConfiguration)
    (hHalted : (machine problem).isHalted config = false) :
    (if config.state == (machine problem).acceptState then WorkVerdict.accept
     else if config.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  unfold WorkMachine.isHalted at hHalted
  cases hAccept : (config.state == (machine problem).acceptState) with
  | true =>
      rw [hAccept] at hHalted
      contradiction
  | false =>
      cases hReject : (config.state == (machine problem).rejectState) with
      | true =>
          rw [hAccept, hReject] at hHalted
          contradiction
      | false => rfl

private theorem stuck_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (config : WorkConfiguration)
    (hHalted : (machine problem).isHalted config = false)
    (hStep : workStep? (machine problem) config = none) :
    (let result := workRun (machine problem) fuel config
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  have hRun := workRun_eq_self_of_workStep?_eq_none
    (machine problem) config fuel hStep
  rw [hRun]
  exact verdict_timeout_of_not_halted problem config hHalted

/-- The prior first-literal endpoint is nonhalting until the outer bridge
launches the fresh unary coordinate evaluator. -/
theorem prefixEndpoint_before_launch_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderFirstLiteralPrefix.workSteps problem)
        (rawInputWorkTape problem.input) = .timeout := by
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact (machine problem)
    (BuilderFirstLiteralPrefix.workSteps problem)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (renameConfiguration WorkChain.firstState
      (BuilderFirstLiteralPrefix.finalConfiguration problem))
    (prefix_workRunExact problem)]
  exact verdict_timeout_of_not_halted problem _
    (machine_isHalted_prefix_false problem
      (BuilderFirstLiteralPrefix.finalConfiguration problem))

set_option maxRecDepth 1000000 in
private theorem evaluatorEndpoint_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem)
        (BuilderFirstLiteralPrefix.workSteps problem + 1 +
          BuilderUnaryPolynomial.workSteps
            (nextTokenSlotPolynomial problem.verifier) problem.input)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (renameConfiguration WorkChain.secondState
        (renameConfiguration WorkChain.firstState
          (BuilderUnaryPolynomial.finalConfiguration
            (nextTokenSlotPolynomial problem.verifier) problem.input
            (BuilderFirstLiteralPrefix.finalOutside problem)
            (BuilderFirstLiteralPrefix.firstLiteralTokens problem)))) := by
  let prefixFinal := renameConfiguration WorkChain.firstState
    (BuilderFirstLiteralPrefix.finalConfiguration problem)
  let evaluatorInitial := BuilderUnaryPolynomial.initialConfiguration
    (nextTokenSlotPolynomial problem.verifier) problem.input
    (BuilderFirstLiteralPrefix.finalOutside problem)
    (BuilderFirstLiteralPrefix.firstLiteralTokens problem)
  let evaluatorFinal := BuilderUnaryPolynomial.finalConfiguration
    (nextTokenSlotPolynomial problem.verifier) problem.input
    (BuilderFirstLiteralPrefix.finalOutside problem)
    (BuilderFirstLiteralPrefix.firstLiteralTokens problem)
  let innerInitial := renameConfiguration WorkChain.firstState evaluatorInitial
  let innerFinal := renameConfiguration WorkChain.firstState evaluatorFinal
  let globalInitial := renameConfiguration WorkChain.secondState innerInitial
  let globalFinal := renameConfiguration WorkChain.secondState innerFinal
  have hPrefix : workRunExact? (machine problem)
      (BuilderFirstLiteralPrefix.workSteps problem)
      (workStartConfiguration (machine problem)
        (rawInputWorkTape problem.input)) = some prefixFinal := by
    simpa [prefixFinal] using prefix_workRunExact problem
  have hLaunch : workRunExact? (machine problem) 1 prefixFinal =
      some globalInitial := by
    change
      (match workStep? (machine problem) prefixFinal with
       | none => none
       | some next => workRunExact? (machine problem) 0 next) =
        some globalInitial
    rw [show workStep? (machine problem) prefixFinal = some globalInitial by
      simpa [prefixFinal, globalInitial, innerInitial, evaluatorInitial,
        BuilderUnaryPolynomial.initialConfiguration,
        BuilderFirstLiteralPrefix.finalConfiguration,
        BuilderFirstLiteralPrefix.finalTape, evaluatorTailMachine,
        WorkChain.machine, renameConfiguration,
        workStartConfiguration] using
          launch_workStep problem]
    rfl
  have hInner := PipelineStageBridges.workRunExact?_transport
    (BuilderUnaryPolynomial.machine
      (nextTokenSlotPolynomial problem.verifier))
    (evaluatorTailMachine problem) WorkChain.firstState
    (WorkChain.first_workStep_of_some
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier))
      FirstClauseTailAppender.machine)
    (BuilderUnaryPolynomial.workSteps
      (nextTokenSlotPolynomial problem.verifier) problem.input)
    evaluatorInitial evaluatorFinal (by
      simpa [evaluatorInitial, evaluatorFinal] using
        evaluator_workRunExact problem)
  have hGlobal := PipelineStageBridges.workRunExact?_transport
    (evaluatorTailMachine problem) (machine problem) WorkChain.secondState
    (WorkChain.second_workStep_of_some
      (BuilderFirstLiteralPrefix.machine problem)
      (evaluatorTailMachine problem))
    (BuilderUnaryPolynomial.workSteps
      (nextTokenSlotPolynomial problem.verifier) problem.input)
    innerInitial innerFinal (by
      simpa [innerInitial, innerFinal] using hInner)
  have h01 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem) (BuilderFirstLiteralPrefix.workSteps problem) 1
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    prefixFinal globalInitial hPrefix hLaunch
  have h02 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem) (BuilderFirstLiteralPrefix.workSteps problem + 1)
    (BuilderUnaryPolynomial.workSteps
      (nextTokenSlotPolynomial problem.verifier) problem.input)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    globalInitial globalFinal h01 (by
      simpa [globalInitial, globalFinal] using hGlobal)
  simpa [globalFinal, innerFinal, evaluatorFinal, Nat.add_assoc] using h02

/-- The fresh evaluator endpoint is nonhalting until the inner bridge
launches the first tail appender. -/
theorem evaluatorEndpoint_before_launch_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderFirstLiteralPrefix.workSteps problem + 1 +
          BuilderUnaryPolynomial.workSteps
            (nextTokenSlotPolynomial problem.verifier) problem.input)
        (rawInputWorkTape problem.input) = .timeout := by
  let evaluatorFinal := BuilderUnaryPolynomial.finalConfiguration
    (nextTokenSlotPolynomial problem.verifier) problem.input
    (BuilderFirstLiteralPrefix.finalOutside problem)
    (BuilderFirstLiteralPrefix.firstLiteralTokens problem)
  let innerFinal := renameConfiguration WorkChain.firstState evaluatorFinal
  let globalFinal := renameConfiguration WorkChain.secondState innerFinal
  have hInnerHalted : (evaluatorTailMachine problem).isHalted innerFinal =
      false := by
    have hHalted := WorkChain.machine_isHalted_first_false
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier))
      FirstClauseTailAppender.machine evaluatorFinal
    simpa [evaluatorTailMachine, innerFinal] using hHalted
  have hGlobalHalted : (machine problem).isHalted globalFinal = false := by
    have hHalted := WorkChain.machine_isHalted_second_false_of_local
      (BuilderFirstLiteralPrefix.machine problem)
      (evaluatorTailMachine problem) innerFinal hInnerHalted
    simpa [machine, globalFinal] using hHalted
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact (machine problem)
    (BuilderFirstLiteralPrefix.workSteps problem + 1 +
      BuilderUnaryPolynomial.workSteps
        (nextTokenSlotPolynomial problem.verifier) problem.input)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input)) globalFinal (by
        simpa [globalFinal, innerFinal, evaluatorFinal] using
          evaluatorEndpoint_workRunExact problem)]
  exact verdict_timeout_of_not_halted problem globalFinal hGlobalHalted

private theorem tailFirst_stuck_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (bad : WorkConfiguration)
    (hLocalHalted : BuilderTokenAppender.machine.isHalted bad = false)
    (hLocalStep : workStep? BuilderTokenAppender.machine bad = none) :
    (let config := renameConfiguration WorkChain.secondState
        (renameConfiguration WorkChain.secondState
          (renameConfiguration WorkChain.firstState bad))
     let result := workRun (machine problem) fuel config
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let firstAppender := FirstClauseTailAppender.tokenMachine .t
  let remaining := FirstClauseTailAppender.chainTokens .t
    [.f, .t, .t, .t, .f, .finish]
  let tailConfig := renameConfiguration WorkChain.firstState bad
  let innerConfig := renameConfiguration WorkChain.secondState tailConfig
  let globalConfig := renameConfiguration WorkChain.secondState innerConfig
  have hFirstHalted : firstAppender.isHalted bad = false := by
    change BuilderTokenAppender.machine.isHalted bad = false
    exact hLocalHalted
  have hFirstStep : workStep? firstAppender bad = none := by
    change workStep? BuilderTokenAppender.machine bad = none
    exact hLocalStep
  have hAccept := WorkChain.state_ne_accept_of_not_halted
    firstAppender bad hFirstHalted
  have hTailStep : workStep? FirstClauseTailAppender.machine tailConfig =
      none := by
    have hStep := WorkChain.first_workStep_none_of_local
      firstAppender remaining bad hAccept hFirstHalted hFirstStep
    simpa [FirstClauseTailAppender.machine,
      FirstClauseTailAppender.chainTokens, firstAppender, remaining,
      tailConfig] using hStep
  have hTailHalted : FirstClauseTailAppender.machine.isHalted tailConfig =
      false := by
    have hHalted := WorkChain.machine_isHalted_first_false
      firstAppender remaining bad
    simpa [FirstClauseTailAppender.machine,
      FirstClauseTailAppender.chainTokens, firstAppender, remaining,
      tailConfig] using hHalted
  let evaluator := BuilderUnaryPolynomial.machine
    (nextTokenSlotPolynomial problem.verifier)
  have hInnerStep : workStep? (evaluatorTailMachine problem) innerConfig =
      none := by
    have hStep := WorkChain.second_workStep_none_of_local
      evaluator FirstClauseTailAppender.machine tailConfig
      hTailHalted hTailStep
    simpa [evaluatorTailMachine, evaluator, innerConfig] using hStep
  have hInnerHalted : (evaluatorTailMachine problem).isHalted innerConfig =
      false := by
    have hHalted := WorkChain.machine_isHalted_second_false_of_local
      evaluator FirstClauseTailAppender.machine tailConfig hTailHalted
    simpa [evaluatorTailMachine, evaluator, innerConfig] using hHalted
  have hGlobalStep : workStep? (machine problem) globalConfig = none := by
    have hStep := WorkChain.second_workStep_none_of_local
      (BuilderFirstLiteralPrefix.machine problem)
      (evaluatorTailMachine problem) innerConfig hInnerHalted hInnerStep
    simpa [machine, globalConfig] using hStep
  have hGlobalHalted : (machine problem).isHalted globalConfig = false := by
    have hHalted := WorkChain.machine_isHalted_second_false_of_local
      (BuilderFirstLiteralPrefix.machine problem)
      (evaluatorTailMachine problem) innerConfig hInnerHalted
    simpa [machine, globalConfig] using hHalted
  exact stuck_timeout problem fuel globalConfig hGlobalHalted hGlobalStep

/-- A malformed tally-phase symbol in the first tail appender remains
globally nonhalting and stuck for every fuel budget. -/
theorem malformedAppenderTally_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (request : CNFToken) (left right : List WorkSymbol) :
    (let config := renameConfiguration WorkChain.secondState
        (renameConfiguration WorkChain.secondState
          (renameConfiguration WorkChain.firstState
            (BuilderTokenAppender.malformedTallyConfiguration
              request left right)))
     let result := workRun (machine problem) fuel config
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let bad := BuilderTokenAppender.malformedTallyConfiguration
    request left right
  exact tailFirst_stuck_timeout problem fuel bad
    (BuilderTokenAppender.malformedTallySymbol_isHalted_false
      request left right)
    (BuilderTokenAppender.malformedTallySymbol_workStep_none
      request left right)

/-- A malformed output-phase symbol in the first tail appender likewise
cannot fall through to either global halt. -/
theorem malformedAppenderOutput_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (request : CNFToken) (left right : List WorkSymbol) :
    (let config := renameConfiguration WorkChain.secondState
        (renameConfiguration WorkChain.secondState
          (renameConfiguration WorkChain.firstState
            (BuilderTokenAppender.malformedOutputConfiguration
              request left right)))
     let result := workRun (machine problem) fuel config
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let bad := BuilderTokenAppender.malformedOutputConfiguration
    request left right
  exact tailFirst_stuck_timeout problem fuel bad
    (BuilderTokenAppender.malformedOutputSymbol_isHalted_false
      request left right)
    (BuilderTokenAppender.malformedOutputSymbol_workStep_none
      request left right)

private theorem workRunExact_succ_split_last {language : Language}
    (problem : VerifierTableauProblem language) :
    ∀ (steps : Nat) (initial final : WorkConfiguration),
      workRunExact? (machine problem) (steps + 1) initial = some final →
      ∃ before,
        workRunExact? (machine problem) steps initial = some before ∧
        workStep? (machine problem) before = some final := by
  intro steps
  induction steps with
  | zero =>
      intro initial final hRun
      cases hStep : workStep? (machine problem) initial with
      | none =>
          change
            (match workStep? (machine problem) initial with
             | none => none
             | some next => some next) = some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hNext : next = final := by
            change
              (match workStep? (machine problem) initial with
               | none => none
               | some result => some result) = some final at hRun
            rw [hStep] at hRun
            exact Option.some.inj hRun
          subst final
          exact ⟨initial, rfl, hStep⟩
  | succ steps ih =>
      intro initial final hRun
      cases hStep : workStep? (machine problem) initial with
      | none =>
          change
            (match workStep? (machine problem) initial with
             | none => none
             | some next =>
                 workRunExact? (machine problem) (steps + 1) next) =
              some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hTail : workRunExact? (machine problem) (steps + 1) next =
              some final := by
            change
              (match workStep? (machine problem) initial with
               | none => none
               | some result =>
                   workRunExact? (machine problem) (steps + 1) result) =
                some final at hRun
            rw [hStep] at hRun
            exact hRun
          rcases ih next final hTail with ⟨before, hPrefix, hLast⟩
          refine ⟨before, ?_, hLast⟩
          change
            (match workStep? (machine problem) initial with
             | none => none
             | some result =>
                 workRunExact? (machine problem) steps result) = some before
          rw [hStep]
          exact hPrefix

private theorem isHalted_false_of_workStep_some {language : Language}
    (problem : VerifierTableauProblem language)
    (config next : WorkConfiguration)
    (hStep : workStep? (machine problem) config = some next) :
    (machine problem).isHalted config = false := by
  cases hHalted : (machine problem).isHalted config with
  | false => rfl
  | true =>
      unfold workStep? at hStep
      rw [hHalted] at hStep
      contradiction

private theorem workSteps_positive {language : Language}
    (problem : VerifierTableauProblem language) : 0 < workSteps problem := by
  unfold workSteps
  omega

/-- Removing the final successful transition leaves a nonhalting state, so
the exact all-input trace cannot accept one work step early. -/
theorem work_one_step_short_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem) (workSteps problem - 1)
        (rawInputWorkTape problem.input) = .timeout := by
  let short := workSteps problem - 1
  let initial := workStartConfiguration (machine problem)
    (rawInputWorkTape problem.input)
  let final := finalConfiguration problem
  have hSucc : short + 1 = workSteps problem := by
    dsimp [short]
    have hPositive := workSteps_positive problem
    omega
  have hExact := workRunExact problem
  change workRunExact? (machine problem) (workSteps problem) initial =
    some final at hExact
  rw [← hSucc] at hExact
  rcases workRunExact_succ_split_last problem short initial final hExact with
    ⟨before, hPrefix, hLast⟩
  have hRun : workRun (machine problem) short initial = before :=
    workRun_eq_of_workRunExact (machine problem) short initial before hPrefix
  have hNotHalted := isHalted_false_of_workStep_some
    problem before final hLast
  unfold workBoundedDecide
  change
    (let result := workRun (machine problem) short initial
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout
  rw [hRun]
  exact verdict_timeout_of_not_halted problem before hNotHalted

end BuilderFirstClausePrefix

end CookLevin

end PNP.Concrete
