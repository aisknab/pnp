/-
Copyright (c) 2026 PNP Labs.

Literal composition of the complete Cook--Levin unary-width header with a
structurally compiled unary next-token cursor and the first formula-body
separator token.

For every fixed verifier problem, the finite work machine in this file starts
from an ordinary raw bitstring, emits exactly `T^FormulaWidth F Sep`, and
retains the next padded token-schedule coordinate in unary scratch.  This is
only a body-start prefix.  It does not dynamically interpret cursor slots,
emit a literal or a complete clause, construct the complete formula, provide
a RawRefinement or polynomial reduction, prove CNF-SAT is in P, or establish
P = NP.
-/

import PNP.Concrete.CookLevinBuilderCompleteHeader

namespace PNP.Concrete

namespace CookLevin

namespace BuilderBodyStartPrefix

open PipelineTape PipelineStateNamespace PipelineStageBridges

/-! ### Retained next-token coordinate -/

/-- Polynomial for the token opportunity immediately after the first clause
separator.  The padded header occupies `formulaVariableSlotBound + 1`
opportunities, and the separator consumes the next one. -/
def nextTokenSlotPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (formulaVariableCountPolynomial verifier) (.constant 2)

def nextTokenSlot {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  (nextTokenSlotPolynomial problem.verifier).eval problem.input.length

theorem nextTokenSlot_eq_formulaVariableSlotBound_add_two
    {language : Language} (problem : VerifierTableauProblem language) :
    nextTokenSlot problem = problem.formulaVariableSlotBound + 2 := by
  rfl

/-- Raw-bit coordinate corresponding to the retained token coordinate. -/
def nextBitSlot {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  2 * nextTokenSlot problem

/-- Specification cursor aligned with the retained token coordinate.  The
work tape stores the token coordinate itself; this definition records the
proved conversion to the existing raw-bit cursor specification. -/
def nextBitCursor {language : Language}
    (problem : VerifierTableauProblem language) :
    VerifierTableauProblem.FormulaBitCursor :=
  ⟨nextBitSlot problem⟩

theorem nextBitCursor_nextSlot {language : Language}
    (problem : VerifierTableauProblem language) :
    (nextBitCursor problem).nextSlot =
      2 * (problem.formulaVariableSlotBound + 2) := by
  rw [nextBitCursor, nextBitSlot,
    nextTokenSlot_eq_formulaVariableSlotBound_add_two]

/-! ### Three collision-free component images -/

def headerState (state : Nat) : Nat := inputState state
def cursorState (state : Nat) : Nat := simulationState state
def appenderState (state : Nat) : Nat := handoffState state

theorem headerState_injective : Function.Injective headerState :=
  inputState_injective

theorem cursorState_injective : Function.Injective cursorState :=
  simulationState_injective

theorem appenderState_injective : Function.Injective appenderState :=
  handoffState_injective

theorem headerState_ne_cursorState (left right : Nat) :
    headerState left ≠ cursorState right :=
  inputState_ne_simulationState left right

theorem headerState_ne_appenderState (left right : Nat) :
    headerState left ≠ appenderState right :=
  inputState_ne_handoffState left right

theorem cursorState_ne_appenderState (left right : Nat) :
    cursorState left ≠ appenderState right :=
  simulationState_ne_handoffState left right

def headerCursorBridge {language : Language}
    (problem : VerifierTableauProblem language) : List WorkRule :=
  launchRules
    (headerState (BuilderCompleteHeader.machine problem).acceptState)
    (cursorState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).startState)

def cursorAppenderBridge {language : Language}
    (problem : VerifierTableauProblem language) : List WorkRule :=
  launchRules
    (cursorState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).acceptState)
    (appenderState (BuilderTokenAppender.seekInputState .sep))

def bridgeRules {language : Language}
    (problem : VerifierTableauProblem language) : List WorkRule :=
  headerCursorBridge problem ++ cursorAppenderBridge problem

private def componentRules {language : Language}
    (problem : VerifierTableauProblem language) : List WorkRule :=
  (BuilderCompleteHeader.machine problem).rules.map
      (renameRule headerState) ++
    ((BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).rules.map
        (renameRule cursorState) ++
      BuilderTokenAppender.machine.rules.map (renameRule appenderState))

/-- One bridge-first literal table containing the complete header, cursor
evaluator, and token appender tables. -/
def rules {language : Language}
    (problem : VerifierTableauProblem language) : List WorkRule :=
  bridgeRules problem ++ componentRules problem

/-- Only the final appender copy contributes global halts. -/
def machine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  { rules := rules problem
    startState := headerState (BuilderCompleteHeader.machine problem).startState
    acceptState := appenderState BuilderTokenAppender.machine.acceptState
    rejectState := appenderState BuilderTokenAppender.machine.rejectState }

theorem rules_length {language : Language}
    (problem : VerifierTableauProblem language) :
    (rules problem).length =
      440 +
        BuilderUnaryPolynomial.ruleCount
          (BuilderCompleteHeader.widthPolynomial problem) +
        BuilderUnaryPolynomial.ruleCount
          (nextTokenSlotPolynomial problem.verifier) := by
  have hHeader := BuilderCompleteHeader.rules_length problem
  have hCursor := BuilderUnaryPolynomial.rules_length
    (nextTokenSlotPolynomial problem.verifier)
  have hAppender := BuilderTokenAppender.rules_length
  have hHeader' : (BuilderCompleteHeader.machine problem).rules.length =
      363 + BuilderUnaryPolynomial.ruleCount
        (BuilderCompleteHeader.widthPolynomial problem) := by
    simpa [BuilderCompleteHeader.machine] using hHeader
  have hCursor' :
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).rules.length =
      BuilderUnaryPolynomial.ruleCount
        (nextTokenSlotPolynomial problem.verifier) := by
    simpa [BuilderUnaryPolynomial.machine] using hCursor
  have hAppender' : BuilderTokenAppender.machine.rules.length = 59 := by
    simpa [BuilderTokenAppender.machine] using hAppender
  have hBridgeOne : (headerCursorBridge problem).length = 9 := by rfl
  have hBridgeTwo : (cursorAppenderBridge problem).length = 9 := by rfl
  simp only [rules, bridgeRules, componentRules, List.length_append,
    List.length_map]
  rw [hHeader', hCursor', hAppender', hBridgeOne, hBridgeTwo]
  omega

theorem machine_acceptState_ne_rejectState {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).acceptState ≠ (machine problem).rejectState := by
  intro h
  exact BuilderTokenAppender.machine_acceptState_ne_rejectState
    (appenderState_injective h)

/-! ### Literal-table determinism -/

private def QueryDistinct (left right : WorkRule) : Prop :=
  (left.sourceState, left.readSymbol) ≠
    (right.sourceState, right.readSymbol)

private theorem queryDistinct_of_source_ne (left right : WorkRule)
    (hSource : left.sourceState ≠ right.sourceState) :
    QueryDistinct left right := by
  intro hQuery
  exact hSource (congrArg Prod.fst hQuery)

private theorem renameRules_pairwise (encode : Nat → Nat)
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

private theorem renamedRules_source {encode : Nat → Nat}
    {localRules : List WorkRule} {rule : WorkRule}
    (hMem : rule ∈ localRules.map (renameRule encode)) :
    ∃ localRule ∈ localRules,
      rule.sourceState = encode localRule.sourceState := by
  rcases List.mem_map.mp hMem with ⟨localRule, hLocal, hRule⟩
  exact ⟨localRule, hLocal, by rw [← hRule]; rfl⟩

private theorem renamedRules_cross
    (leftEncode rightEncode : Nat → Nat)
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

private theorem appender_rule_source_ne_accept (rule : WorkRule)
    (hMem : rule ∈ BuilderTokenAppender.machine.rules) :
    rule.sourceState ≠ BuilderTokenAppender.machine.acceptState := by
  decide +revert

private theorem appender_rule_source_ne_reject (rule : WorkRule)
    (hMem : rule ∈ BuilderTokenAppender.machine.rules) :
    rule.sourceState ≠ BuilderTokenAppender.machine.rejectState := by
  decide +revert

private theorem completeHeader_rule_source_ne_accept
    {language : Language} (problem : VerifierTableauProblem language)
    (rule : WorkRule)
    (hMem : rule ∈ (BuilderCompleteHeader.machine problem).rules) :
    rule.sourceState ≠ (BuilderCompleteHeader.machine problem).acceptState := by
  change rule.sourceState ≠
    BuilderCompleteHeader.fAppenderState
      BuilderTokenAppender.machine.acceptState
  change rule ∈ BuilderCompleteHeader.rules problem at hMem
  unfold BuilderCompleteHeader.rules at hMem
  rcases List.mem_append.mp hMem with hBridges | hComponents
  · unfold BuilderCompleteHeader.bridgeRules at hBridges
    simp only [List.mem_append] at hBridges
    rcases hBridges with hBridgeOne | hBridgeTwo | hBridgeThree |
        hBridgeFour | hBridgeFive
    · have hSource : rule.sourceState =
          BuilderCompleteHeader.prefixState
            BuilderFirstTokenPrefix.machine.acceptState := by
        apply launchRules_source_eq
        simpa [BuilderCompleteHeader.prefixEvaluatorBridge] using hBridgeOne
      rw [hSource]
      simp only [BuilderCompleteHeader.prefixState,
        BuilderCompleteHeader.fAppenderState]
      omega
    · have hSource : rule.sourceState =
          BuilderCompleteHeader.evaluatorState
            (BuilderUnaryPolynomial.machine
              (BuilderCompleteHeader.widthPolynomial problem)).acceptState := by
        apply launchRules_source_eq
        simpa [BuilderCompleteHeader.evaluatorControllerBridge] using hBridgeTwo
      rw [hSource]
      simp only [BuilderCompleteHeader.evaluatorState,
        BuilderCompleteHeader.fAppenderState]
      omega
    · have hSource : rule.sourceState =
          BuilderCompleteHeader.controllerState
            BuilderCompleteHeader.HeaderController.moreExitState := by
        apply launchRules_source_eq
        simpa [BuilderCompleteHeader.controllerTBridge] using hBridgeThree
      rw [hSource]
      simp only [BuilderCompleteHeader.controllerState,
        BuilderCompleteHeader.fAppenderState]
      omega
    · have hSource : rule.sourceState =
          BuilderCompleteHeader.tAppenderState
            BuilderTokenAppender.machine.acceptState := by
        apply launchRules_source_eq
        simpa [BuilderCompleteHeader.tControllerBridge] using hBridgeFour
      rw [hSource]
      simp only [BuilderCompleteHeader.tAppenderState,
        BuilderCompleteHeader.fAppenderState]
      omega
    · have hSource : rule.sourceState =
          BuilderCompleteHeader.controllerState
            BuilderCompleteHeader.HeaderController.doneExitState := by
        apply launchRules_source_eq
        simpa [BuilderCompleteHeader.controllerFBridge] using hBridgeFive
      rw [hSource]
      simp only [BuilderCompleteHeader.controllerState,
        BuilderCompleteHeader.fAppenderState]
      omega
  · simp only [List.mem_append] at hComponents
    rcases hComponents with hPrefix | hEvaluator | hController |
        hTAppender | hFAppender
    · rcases renamedRules_source hPrefix with
        ⟨localRule, _hLocal, hSource⟩
      rw [hSource]
      simp only [BuilderCompleteHeader.prefixState,
        BuilderCompleteHeader.fAppenderState]
      omega
    · rcases renamedRules_source hEvaluator with
        ⟨localRule, _hLocal, hSource⟩
      rw [hSource]
      simp only [BuilderCompleteHeader.evaluatorState,
        BuilderCompleteHeader.fAppenderState]
      omega
    · rcases renamedRules_source hController with
        ⟨localRule, _hLocal, hSource⟩
      rw [hSource]
      simp only [BuilderCompleteHeader.controllerState,
        BuilderCompleteHeader.fAppenderState]
      omega
    · rcases renamedRules_source hTAppender with
        ⟨localRule, _hLocal, hSource⟩
      rw [hSource]
      simp only [BuilderCompleteHeader.tAppenderState,
        BuilderCompleteHeader.fAppenderState]
      omega
    · rcases renamedRules_source hFAppender with
        ⟨localRule, hLocal, hSource⟩
      rw [hSource]
      intro hEqual
      exact appender_rule_source_ne_accept localRule hLocal
        (BuilderCompleteHeader.fAppenderState_injective hEqual)

private theorem completeHeader_rule_source_ne_reject
    {language : Language} (problem : VerifierTableauProblem language)
    (rule : WorkRule)
    (hMem : rule ∈ (BuilderCompleteHeader.machine problem).rules) :
    rule.sourceState ≠ (BuilderCompleteHeader.machine problem).rejectState := by
  change rule.sourceState ≠
    BuilderCompleteHeader.fAppenderState
      BuilderTokenAppender.machine.rejectState
  change rule ∈ BuilderCompleteHeader.rules problem at hMem
  unfold BuilderCompleteHeader.rules at hMem
  rcases List.mem_append.mp hMem with hBridges | hComponents
  · unfold BuilderCompleteHeader.bridgeRules at hBridges
    simp only [List.mem_append] at hBridges
    rcases hBridges with hBridgeOne | hBridgeTwo | hBridgeThree |
        hBridgeFour | hBridgeFive
    · have hSource : rule.sourceState =
          BuilderCompleteHeader.prefixState
            BuilderFirstTokenPrefix.machine.acceptState := by
        apply launchRules_source_eq
        simpa [BuilderCompleteHeader.prefixEvaluatorBridge] using hBridgeOne
      rw [hSource]
      simp only [BuilderCompleteHeader.prefixState,
        BuilderCompleteHeader.fAppenderState]
      omega
    · have hSource : rule.sourceState =
          BuilderCompleteHeader.evaluatorState
            (BuilderUnaryPolynomial.machine
              (BuilderCompleteHeader.widthPolynomial problem)).acceptState := by
        apply launchRules_source_eq
        simpa [BuilderCompleteHeader.evaluatorControllerBridge] using hBridgeTwo
      rw [hSource]
      simp only [BuilderCompleteHeader.evaluatorState,
        BuilderCompleteHeader.fAppenderState]
      omega
    · have hSource : rule.sourceState =
          BuilderCompleteHeader.controllerState
            BuilderCompleteHeader.HeaderController.moreExitState := by
        apply launchRules_source_eq
        simpa [BuilderCompleteHeader.controllerTBridge] using hBridgeThree
      rw [hSource]
      simp only [BuilderCompleteHeader.controllerState,
        BuilderCompleteHeader.fAppenderState]
      omega
    · have hSource : rule.sourceState =
          BuilderCompleteHeader.tAppenderState
            BuilderTokenAppender.machine.acceptState := by
        apply launchRules_source_eq
        simpa [BuilderCompleteHeader.tControllerBridge] using hBridgeFour
      rw [hSource]
      simp only [BuilderCompleteHeader.tAppenderState,
        BuilderCompleteHeader.fAppenderState]
      omega
    · have hSource : rule.sourceState =
          BuilderCompleteHeader.controllerState
            BuilderCompleteHeader.HeaderController.doneExitState := by
        apply launchRules_source_eq
        simpa [BuilderCompleteHeader.controllerFBridge] using hBridgeFive
      rw [hSource]
      simp only [BuilderCompleteHeader.controllerState,
        BuilderCompleteHeader.fAppenderState]
      omega
  · simp only [List.mem_append] at hComponents
    rcases hComponents with hPrefix | hEvaluator | hController |
        hTAppender | hFAppender
    · rcases renamedRules_source hPrefix with
        ⟨localRule, _hLocal, hSource⟩
      rw [hSource]
      simp only [BuilderCompleteHeader.prefixState,
        BuilderCompleteHeader.fAppenderState]
      omega
    · rcases renamedRules_source hEvaluator with
        ⟨localRule, _hLocal, hSource⟩
      rw [hSource]
      simp only [BuilderCompleteHeader.evaluatorState,
        BuilderCompleteHeader.fAppenderState]
      omega
    · rcases renamedRules_source hController with
        ⟨localRule, _hLocal, hSource⟩
      rw [hSource]
      simp only [BuilderCompleteHeader.controllerState,
        BuilderCompleteHeader.fAppenderState]
      omega
    · rcases renamedRules_source hTAppender with
        ⟨localRule, _hLocal, hSource⟩
      rw [hSource]
      simp only [BuilderCompleteHeader.tAppenderState,
        BuilderCompleteHeader.fAppenderState]
      omega
    · rcases renamedRules_source hFAppender with
        ⟨localRule, hLocal, hSource⟩
      rw [hSource]
      intro hEqual
      exact appender_rule_source_ne_reject localRule hLocal
        (BuilderCompleteHeader.fAppenderState_injective hEqual)

private theorem componentRules_pairwise {language : Language}
    (problem : VerifierTableauProblem language) :
    (componentRules problem).Pairwise QueryDistinct := by
  let headerRules := (BuilderCompleteHeader.machine problem).rules.map
    (renameRule headerState)
  let cursorRules :=
    (BuilderUnaryPolynomial.machine
      (nextTokenSlotPolynomial problem.verifier)).rules.map
        (renameRule cursorState)
  let appenderRules := BuilderTokenAppender.machine.rules.map
    (renameRule appenderState)
  have hHeader := renameRules_pairwise headerState headerState_injective
    (BuilderCompleteHeader.machine problem).rules
    (BuilderCompleteHeader.rules_pairwise_query_distinct problem)
  have hCursor := renameRules_pairwise cursorState cursorState_injective
    (BuilderUnaryPolynomial.machine
      (nextTokenSlotPolynomial problem.verifier)).rules
    (BuilderUnaryPolynomial.rules_pairwise_query_distinct
      (nextTokenSlotPolynomial problem.verifier))
  have hAppender := renameRules_pairwise appenderState appenderState_injective
    BuilderTokenAppender.machine.rules
    BuilderTokenAppender.rules_pairwise_query_distinct
  have hHC := renamedRules_cross headerState cursorState
    (BuilderCompleteHeader.machine problem).rules
    (BuilderUnaryPolynomial.machine
      (nextTokenSlotPolynomial problem.verifier)).rules
    headerState_ne_cursorState
  have hHA := renamedRules_cross headerState appenderState
    (BuilderCompleteHeader.machine problem).rules
    BuilderTokenAppender.machine.rules headerState_ne_appenderState
  have hCA := renamedRules_cross cursorState appenderState
    (BuilderUnaryPolynomial.machine
      (nextTokenSlotPolynomial problem.verifier)).rules
    BuilderTokenAppender.machine.rules cursorState_ne_appenderState
  unfold componentRules
  rw [List.pairwise_append]
  refine ⟨hHeader, ?_, ?_⟩
  · rw [List.pairwise_append]
    exact ⟨hCursor, hAppender, hCA⟩
  · intro left hLeft right hRight
    simp only [List.mem_append] at hRight
    rcases hRight with hRight | hRight
    · exact hHC left hLeft right hRight
    · exact hHA left hLeft right hRight

private theorem launchRules_cross (leftSource leftTarget rightSource
    rightTarget : Nat) (hSource : leftSource ≠ rightSource) :
    ∀ left ∈ launchRules leftSource leftTarget,
      ∀ right ∈ launchRules rightSource rightTarget,
        QueryDistinct left right := by
  intro left hLeft right hRight
  apply queryDistinct_of_source_ne
  rw [launchRules_source_eq hLeft, launchRules_source_eq hRight]
  exact hSource

private theorem launchRenamed_cross (source target : Nat)
    (encode : Nat → Nat) (localRules : List WorkRule)
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

private theorem bridgeRules_pairwise {language : Language}
    (problem : VerifierTableauProblem language) :
    (bridgeRules problem).Pairwise QueryDistinct := by
  have hHeader := launchRules_pairwise
    (headerState (BuilderCompleteHeader.machine problem).acceptState)
    (cursorState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).startState)
  have hCursor := launchRules_pairwise
    (cursorState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).acceptState)
    (appenderState (BuilderTokenAppender.seekInputState .sep))
  have hCross := launchRules_cross
    (headerState (BuilderCompleteHeader.machine problem).acceptState)
    (cursorState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).startState)
    (cursorState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).acceptState)
    (appenderState (BuilderTokenAppender.seekInputState .sep))
    (headerState_ne_cursorState _ _)
  unfold bridgeRules headerCursorBridge cursorAppenderBridge
  rw [List.pairwise_append]
  exact ⟨hHeader, hCursor, hCross⟩

private theorem headerBridge_component_cross {language : Language}
    (problem : VerifierTableauProblem language) :
    ∀ bridge ∈ headerCursorBridge problem,
      ∀ component ∈ componentRules problem,
        QueryDistinct bridge component := by
  have hH := launchRenamed_cross
    (headerState (BuilderCompleteHeader.machine problem).acceptState)
    (cursorState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).startState)
    headerState (BuilderCompleteHeader.machine problem).rules (by
      intro localRule hLocal hEqual
      exact completeHeader_rule_source_ne_accept problem localRule hLocal
        (headerState_injective hEqual).symm)
  have hC := launchRenamed_cross
    (headerState (BuilderCompleteHeader.machine problem).acceptState)
    (cursorState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).startState)
    cursorState
    (BuilderUnaryPolynomial.machine
      (nextTokenSlotPolynomial problem.verifier)).rules (by
      intro localRule _hLocal
      exact headerState_ne_cursorState _ _)
  have hA := launchRenamed_cross
    (headerState (BuilderCompleteHeader.machine problem).acceptState)
    (cursorState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).startState)
    appenderState BuilderTokenAppender.machine.rules (by
      intro localRule _hLocal
      exact headerState_ne_appenderState _ _)
  intro bridge hBridge component hComponent
  simp only [componentRules, List.mem_append] at hComponent
  rcases hComponent with hComponent | hComponent | hComponent
  · exact hH bridge hBridge component hComponent
  · exact hC bridge hBridge component hComponent
  · exact hA bridge hBridge component hComponent

private theorem cursorBridge_component_cross {language : Language}
    (problem : VerifierTableauProblem language) :
    ∀ bridge ∈ cursorAppenderBridge problem,
      ∀ component ∈ componentRules problem,
        QueryDistinct bridge component := by
  let cursorMachine := BuilderUnaryPolynomial.machine
    (nextTokenSlotPolynomial problem.verifier)
  have hH := launchRenamed_cross
    (cursorState cursorMachine.acceptState)
    (appenderState (BuilderTokenAppender.seekInputState .sep))
    headerState (BuilderCompleteHeader.machine problem).rules (by
      intro localRule _hLocal
      exact Ne.symm (headerState_ne_cursorState _ _))
  have hC := launchRenamed_cross
    (cursorState cursorMachine.acceptState)
    (appenderState (BuilderTokenAppender.seekInputState .sep))
    cursorState cursorMachine.rules (by
      intro localRule hLocal hEqual
      have hState := cursorState_injective hEqual
      have hLt := BuilderUnaryPolynomial.rule_source_lt_acceptState
        (nextTokenSlotPolynomial problem.verifier) localRule hLocal
      change localRule.sourceState < cursorMachine.acceptState at hLt
      omega)
  have hA := launchRenamed_cross
    (cursorState cursorMachine.acceptState)
    (appenderState (BuilderTokenAppender.seekInputState .sep))
    appenderState BuilderTokenAppender.machine.rules (by
      intro localRule _hLocal
      exact cursorState_ne_appenderState _ _)
  intro bridge hBridge component hComponent
  simp only [componentRules, List.mem_append] at hComponent
  rcases hComponent with hComponent | hComponent | hComponent
  · exact hH bridge hBridge component hComponent
  · exact hC bridge hBridge component hComponent
  · exact hA bridge hBridge component hComponent

private theorem bridgeRules_componentRules_cross {language : Language}
    (problem : VerifierTableauProblem language) :
    ∀ bridge ∈ bridgeRules problem,
      ∀ component ∈ componentRules problem,
        QueryDistinct bridge component := by
  intro bridge hBridge component hComponent
  simp only [bridgeRules, List.mem_append] at hBridge
  rcases hBridge with hBridge | hBridge
  · exact headerBridge_component_cross problem bridge hBridge component hComponent
  · exact cursorBridge_component_cross problem bridge hBridge component hComponent

theorem rules_pairwise_query_distinct {language : Language}
    (problem : VerifierTableauProblem language) :
    (rules problem).Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  change (rules problem).Pairwise QueryDistinct
  have hBridges := bridgeRules_pairwise problem
  have hComponents := componentRules_pairwise problem
  have hCross := bridgeRules_componentRules_cross problem
  unfold rules
  rw [List.pairwise_append]
  exact ⟨hBridges, hComponents, hCross⟩

/-- No rule in the literal body-start table is sourced at its global accept
state.  This is the exact non-shadowing interface needed by a later literal
composition bridge. -/
theorem rule_source_ne_acceptState {language : Language}
    (problem : VerifierTableauProblem language) (rule : WorkRule)
    (hMem : rule ∈ (machine problem).rules) :
    rule.sourceState ≠ (machine problem).acceptState := by
  change rule.sourceState ≠
    appenderState BuilderTokenAppender.machine.acceptState
  change rule ∈ rules problem at hMem
  unfold rules at hMem
  rcases List.mem_append.mp hMem with hBridges | hComponents
  · unfold bridgeRules at hBridges
    simp only [List.mem_append] at hBridges
    rcases hBridges with hHeader | hCursor
    · have hSource : rule.sourceState =
          headerState (BuilderCompleteHeader.machine problem).acceptState := by
        apply launchRules_source_eq
        simpa [headerCursorBridge] using hHeader
      rw [hSource]
      exact headerState_ne_appenderState _ _
    · have hSource : rule.sourceState =
          cursorState
            (BuilderUnaryPolynomial.machine
              (nextTokenSlotPolynomial problem.verifier)).acceptState := by
        apply launchRules_source_eq
        simpa [cursorAppenderBridge] using hCursor
      rw [hSource]
      exact cursorState_ne_appenderState _ _
  · unfold componentRules at hComponents
    simp only [List.mem_append] at hComponents
    rcases hComponents with hHeader | hCursor | hAppender
    · rcases renamedRules_source hHeader with
        ⟨localRule, _hLocal, hSource⟩
      rw [hSource]
      exact headerState_ne_appenderState _ _
    · rcases renamedRules_source hCursor with
        ⟨localRule, _hLocal, hSource⟩
      rw [hSource]
      exact cursorState_ne_appenderState _ _
    · rcases renamedRules_source hAppender with
        ⟨localRule, hLocal, hSource⟩
      rw [hSource]
      intro hEqual
      exact appender_rule_source_ne_accept localRule hLocal
        (appenderState_injective hEqual)

/-- No rule in the literal body-start table is sourced at its global reject
state. -/
theorem rule_source_ne_rejectState {language : Language}
    (problem : VerifierTableauProblem language) (rule : WorkRule)
    (hMem : rule ∈ (machine problem).rules) :
    rule.sourceState ≠ (machine problem).rejectState := by
  change rule.sourceState ≠
    appenderState BuilderTokenAppender.machine.rejectState
  change rule ∈ rules problem at hMem
  unfold rules at hMem
  rcases List.mem_append.mp hMem with hBridges | hComponents
  · unfold bridgeRules at hBridges
    simp only [List.mem_append] at hBridges
    rcases hBridges with hHeader | hCursor
    · have hSource : rule.sourceState =
          headerState (BuilderCompleteHeader.machine problem).acceptState := by
        apply launchRules_source_eq
        simpa [headerCursorBridge] using hHeader
      rw [hSource]
      exact headerState_ne_appenderState _ _
    · have hSource : rule.sourceState =
          cursorState
            (BuilderUnaryPolynomial.machine
              (nextTokenSlotPolynomial problem.verifier)).acceptState := by
        apply launchRules_source_eq
        simpa [cursorAppenderBridge] using hCursor
      rw [hSource]
      exact cursorState_ne_appenderState _ _
  · unfold componentRules at hComponents
    simp only [List.mem_append] at hComponents
    rcases hComponents with hHeader | hCursor | hAppender
    · rcases renamedRules_source hHeader with
        ⟨localRule, _hLocal, hSource⟩
      rw [hSource]
      exact headerState_ne_appenderState _ _
    · rcases renamedRules_source hCursor with
        ⟨localRule, _hLocal, hSource⟩
      rw [hSource]
      exact cursorState_ne_appenderState _ _
    · rcases renamedRules_source hAppender with
        ⟨localRule, hLocal, hSource⟩
      rw [hSource]
      intro hEqual
      exact appender_rule_source_ne_reject localRule hLocal
        (appenderState_injective hEqual)

/-! ### Exact endpoint and costs -/

def bodyStartTokens {language : Language}
    (problem : VerifierTableauProblem language) : List CNFToken :=
  BuilderCompleteHeader.headerTokens problem ++ [.sep]

def finalOutside {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  BuilderUnaryPolynomial.finalOutsideLeft
    (nextTokenSlotPolynomial problem.verifier) problem.input
    (BuilderCompleteHeader.finalOutside problem)

def finalTape {language : Language}
    (problem : VerifierTableauProblem language) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input
    (finalOutside problem) (bodyStartTokens problem)

def finalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := (machine problem).acceptState
    tape := finalTape problem }

def workSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderCompleteHeader.workSteps problem + 1 +
    BuilderUnaryPolynomial.workSteps
      (nextTokenSlotPolynomial problem.verifier) problem.input + 1 +
    BuilderTokenAppender.workSteps problem.input
      (BuilderCompleteHeader.headerTokens problem)

private def scalePolynomial (coefficient : Nat)
    (polynomial : NatPolynomial) : NatPolynomial :=
  .mul (.constant coefficient) polynomial

/-- External compiled-time polynomial for the body-start prefix. -/
def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderCompleteHeader.rawTimeBound verifier)
    (.add (.constant 72)
      (.add
        (scalePolynomial 6
          (BuilderUnaryPolynomial.workTimePolynomial
            (nextTokenSlotPolynomial verifier)))
        (.add (scalePolynomial 24 .variable)
          (scalePolynomial 12 (formulaWidthPolynomial verifier)))))

theorem finalTape_represents {language : Language}
    (problem : VerifierTableauProblem language) :
    Represents (Tape.ofInput problem.input) (finalTape problem) := by
  exact BuilderTokenAppender.workspaceTape_represents problem.input
    (finalOutside problem) (bodyStartTokens problem)

/-- The final exterior-left region contains the evaluator's root register as
an exact unary encoding of the next token coordinate. -/
theorem finalOutside_contains_nextTokenSlot {language : Language}
    (problem : VerifierTableauProblem language) :
    ∃ wordPrefix tail,
      finalOutside problem =
        wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
          List.replicate (nextTokenSlot problem)
            BuilderUnaryPolynomial.unitSymbol ++
          BuilderUnaryPolynomial.scratchEndSymbol :: tail := by
  rcases BuilderUnaryPolynomial.root_register_length
      (nextTokenSlotPolynomial problem.verifier) problem.input.length with
    ⟨wordPrefix, hScratch, _hPrefixLength⟩
  refine ⟨wordPrefix,
    (BuilderCompleteHeader.finalOutside problem).drop
      ((BuilderUnaryPolynomial.scratchWord
        (nextTokenSlotPolynomial problem.verifier)
        problem.input.length).length + 1), ?_⟩
  unfold finalOutside BuilderUnaryPolynomial.finalOutsideLeft
    BuilderUnaryPolynomial.overlayScratch
  rw [hScratch]
  rfl

/-! ### Halt separation and lookup isolation -/

private theorem nat_beq_false_of_ne (left right : Nat)
    (h : left ≠ right) : (left == right) = false := by
  cases hBool : (left == right) with
  | false => rfl
  | true =>
      exact False.elim (h ((nat_beq_true_iff left right).mp hBool))

private theorem state_ne_accept_of_not_halted
    (source : WorkMachine) (config : WorkConfiguration)
    (hHalted : source.isHalted config = false) :
    config.state ≠ source.acceptState := by
  intro hState
  unfold WorkMachine.isHalted at hHalted
  rw [hState] at hHalted
  have hRefl : (source.acceptState == source.acceptState) = true :=
    (nat_beq_true_iff _ _).mpr rfl
  rw [hRefl] at hHalted
  contradiction

private theorem state_ne_reject_of_not_halted
    (source : WorkMachine) (config : WorkConfiguration)
    (hHalted : source.isHalted config = false) :
    config.state ≠ source.rejectState := by
  intro hState
  unfold WorkMachine.isHalted at hHalted
  rw [hState] at hHalted
  have hRefl : (source.rejectState == source.rejectState) = true :=
    (nat_beq_true_iff _ _).mpr rfl
  cases hAccept : (source.rejectState == source.acceptState) with
  | false =>
      rw [hAccept, hRefl] at hHalted
      contradiction
  | true =>
      rw [hAccept, hRefl] at hHalted
      contradiction

private theorem machine_isHalted_header_false {language : Language}
    (problem : VerifierTableauProblem language)
    (config : WorkConfiguration) :
    (machine problem).isHalted
      (renameConfiguration headerState config) = false := by
  unfold WorkMachine.isHalted machine renameConfiguration
  rw [nat_beq_false_of_ne _ _
      (headerState_ne_appenderState config.state
        BuilderTokenAppender.machine.acceptState),
    nat_beq_false_of_ne _ _
      (headerState_ne_appenderState config.state
        BuilderTokenAppender.machine.rejectState)]
  rfl

private theorem machine_isHalted_cursor_false {language : Language}
    (problem : VerifierTableauProblem language)
    (config : WorkConfiguration) :
    (machine problem).isHalted
      (renameConfiguration cursorState config) = false := by
  unfold WorkMachine.isHalted machine renameConfiguration
  rw [nat_beq_false_of_ne _ _
      (cursorState_ne_appenderState config.state
        BuilderTokenAppender.machine.acceptState),
    nat_beq_false_of_ne _ _
      (cursorState_ne_appenderState config.state
        BuilderTokenAppender.machine.rejectState)]
  rfl

private theorem machine_isHalted_appender_false_of_local
    {language : Language} (problem : VerifierTableauProblem language)
    (config : WorkConfiguration)
    (hLocal : BuilderTokenAppender.machine.isHalted config = false) :
    (machine problem).isHalted
      (renameConfiguration appenderState config) = false := by
  have hAccept := state_ne_accept_of_not_halted
    BuilderTokenAppender.machine config hLocal
  have hReject := state_ne_reject_of_not_halted
    BuilderTokenAppender.machine config hLocal
  have hGlobalAccept : appenderState config.state ≠
      appenderState BuilderTokenAppender.machine.acceptState := by
    intro h
    exact hAccept (appenderState_injective h)
  have hGlobalReject : appenderState config.state ≠
      appenderState BuilderTokenAppender.machine.rejectState := by
    intro h
    exact hReject (appenderState_injective h)
  unfold WorkMachine.isHalted machine renameConfiguration
  rw [nat_beq_false_of_ne _ _ hGlobalAccept,
    nat_beq_false_of_ne _ _ hGlobalReject]
  rfl

theorem findWorkRule_header_of_some {language : Language}
    (problem : VerifierTableauProblem language)
    (state : Nat) (symbol : WorkSymbol) (rule : WorkRule)
    (hAccept : state ≠ (BuilderCompleteHeader.machine problem).acceptState)
    (hFind : findWorkRule (BuilderCompleteHeader.machine problem).rules
      state symbol = some rule) :
    findWorkRule (machine problem).rules (headerState state) symbol =
      some (renameRule headerState rule) := by
  have hBridgeOne : findWorkRule (headerCursorBridge problem)
      (headerState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro h
    exact hAccept (headerState_injective h).symm
  have hBridgeTwo : findWorkRule (cursorAppenderBridge problem)
      (headerState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact Ne.symm (headerState_ne_cursorState _ _)
  have hBridges : findWorkRule (bridgeRules problem)
      (headerState state) symbol = none := by
    unfold bridgeRules
    rw [findWorkRule_append_of_none _ _ _ _ hBridgeOne]
    exact hBridgeTwo
  have hRenamed := findWorkRule_rename headerState headerState_injective
    (BuilderCompleteHeader.machine problem).rules state symbol
  rw [hFind] at hRenamed
  unfold machine rules componentRules
  rw [findWorkRule_append_of_none _ _ _ _ hBridges]
  exact findWorkRule_append_of_some _ _ _ _ _ hRenamed

theorem findWorkRule_cursor_of_some {language : Language}
    (problem : VerifierTableauProblem language)
    (state : Nat) (symbol : WorkSymbol) (rule : WorkRule)
    (hAccept : state ≠
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).acceptState)
    (hFind : findWorkRule
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).rules
      state symbol = some rule) :
    findWorkRule (machine problem).rules (cursorState state) symbol =
      some (renameRule cursorState rule) := by
  have hBridgeOne : findWorkRule (headerCursorBridge problem)
      (cursorState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact headerState_ne_cursorState _ _
  have hBridgeTwo : findWorkRule (cursorAppenderBridge problem)
      (cursorState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro h
    exact hAccept (cursorState_injective h).symm
  have hBridges : findWorkRule (bridgeRules problem)
      (cursorState state) symbol = none := by
    unfold bridgeRules
    rw [findWorkRule_append_of_none _ _ _ _ hBridgeOne]
    exact hBridgeTwo
  have hHeader : findWorkRule
      ((BuilderCompleteHeader.machine problem).rules.map
        (renameRule headerState)) (cursorState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact headerState_ne_cursorState source state
  have hRenamed := findWorkRule_rename cursorState cursorState_injective
    (BuilderUnaryPolynomial.machine
      (nextTokenSlotPolynomial problem.verifier)).rules state symbol
  rw [hFind] at hRenamed
  unfold machine rules componentRules
  rw [findWorkRule_append_of_none _ _ _ _ hBridges,
    findWorkRule_append_of_none _ _ _ _ hHeader]
  exact findWorkRule_append_of_some _ _ _ _ _ hRenamed

theorem findWorkRule_appender_of_some {language : Language}
    (problem : VerifierTableauProblem language)
    (state : Nat) (symbol : WorkSymbol) (rule : WorkRule)
    (hFind : findWorkRule BuilderTokenAppender.machine.rules
      state symbol = some rule) :
    findWorkRule (machine problem).rules (appenderState state) symbol =
      some (renameRule appenderState rule) := by
  have hBridgeOne : findWorkRule (headerCursorBridge problem)
      (appenderState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact headerState_ne_appenderState _ _
  have hBridgeTwo : findWorkRule (cursorAppenderBridge problem)
      (appenderState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact cursorState_ne_appenderState _ _
  have hBridges : findWorkRule (bridgeRules problem)
      (appenderState state) symbol = none := by
    unfold bridgeRules
    rw [findWorkRule_append_of_none _ _ _ _ hBridgeOne]
    exact hBridgeTwo
  have hHeader : findWorkRule
      ((BuilderCompleteHeader.machine problem).rules.map
        (renameRule headerState)) (appenderState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact headerState_ne_appenderState source state
  have hCursor : findWorkRule
      ((BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).rules.map
          (renameRule cursorState))
      (appenderState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact cursorState_ne_appenderState source state
  have hRenamed := findWorkRule_rename appenderState appenderState_injective
    BuilderTokenAppender.machine.rules state symbol
  rw [hFind] at hRenamed
  unfold machine rules componentRules
  rw [findWorkRule_append_of_none _ _ _ _ hBridges,
    findWorkRule_append_of_none _ _ _ _ hHeader,
    findWorkRule_append_of_none _ _ _ _ hCursor]
  exact hRenamed

private theorem header_workStep_of_some {language : Language}
    (problem : VerifierTableauProblem language)
    (config next : WorkConfiguration)
    (hStep : workStep? (BuilderCompleteHeader.machine problem) config =
      some next) :
    workStep? (machine problem) (renameConfiguration headerState config) =
      some (renameConfiguration headerState next) := by
  rcases workStep?_some_exists (BuilderCompleteHeader.machine problem)
      config next hStep with ⟨rule, hHalted, hFind, hNext⟩
  have hAccept := state_ne_accept_of_not_halted
    (BuilderCompleteHeader.machine problem) config hHalted
  have hGlobalHalted := machine_isHalted_header_false problem config
  have hGlobalFind := findWorkRule_header_of_some problem
    config.state config.tape.head rule hAccept hFind
  have hGlobalStep := workStep?_eq_apply_of_find (machine problem)
    (renameConfiguration headerState config) (renameRule headerState rule)
    hGlobalHalted hGlobalFind
  calc
    workStep? (machine problem) (renameConfiguration headerState config) =
        some (applyWorkRule (renameRule headerState rule)
          (renameConfiguration headerState config)) := hGlobalStep
    _ = some (renameConfiguration headerState
          (applyWorkRule rule config)) :=
      congrArg Option.some (applyWorkRule_rename headerState rule config)
    _ = some (renameConfiguration headerState next) :=
      congrArg (fun value => some (renameConfiguration headerState value))
        hNext.symm

private theorem cursor_workStep_of_some {language : Language}
    (problem : VerifierTableauProblem language)
    (config next : WorkConfiguration)
    (hStep : workStep?
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)) config = some next) :
    workStep? (machine problem) (renameConfiguration cursorState config) =
      some (renameConfiguration cursorState next) := by
  let cursorMachine := BuilderUnaryPolynomial.machine
    (nextTokenSlotPolynomial problem.verifier)
  rcases workStep?_some_exists cursorMachine config next hStep with
    ⟨rule, hHalted, hFind, hNext⟩
  have hAccept := state_ne_accept_of_not_halted cursorMachine config hHalted
  have hGlobalHalted := machine_isHalted_cursor_false problem config
  have hGlobalFind := findWorkRule_cursor_of_some problem
    config.state config.tape.head rule hAccept hFind
  have hGlobalStep := workStep?_eq_apply_of_find (machine problem)
    (renameConfiguration cursorState config) (renameRule cursorState rule)
    hGlobalHalted hGlobalFind
  calc
    workStep? (machine problem) (renameConfiguration cursorState config) =
        some (applyWorkRule (renameRule cursorState rule)
          (renameConfiguration cursorState config)) := hGlobalStep
    _ = some (renameConfiguration cursorState
          (applyWorkRule rule config)) :=
      congrArg Option.some (applyWorkRule_rename cursorState rule config)
    _ = some (renameConfiguration cursorState next) :=
      congrArg (fun value => some (renameConfiguration cursorState value))
        hNext.symm

private theorem appender_workStep_of_some {language : Language}
    (problem : VerifierTableauProblem language)
    (config next : WorkConfiguration)
    (hStep : workStep? BuilderTokenAppender.machine config = some next) :
    workStep? (machine problem) (renameConfiguration appenderState config) =
      some (renameConfiguration appenderState next) := by
  rcases workStep?_some_exists BuilderTokenAppender.machine config next hStep
    with ⟨rule, hHalted, hFind, hNext⟩
  have hGlobalHalted :=
    machine_isHalted_appender_false_of_local problem config hHalted
  have hGlobalFind := findWorkRule_appender_of_some problem
    config.state config.tape.head rule hFind
  have hGlobalStep := workStep?_eq_apply_of_find (machine problem)
    (renameConfiguration appenderState config) (renameRule appenderState rule)
    hGlobalHalted hGlobalFind
  calc
    workStep? (machine problem) (renameConfiguration appenderState config) =
        some (applyWorkRule (renameRule appenderState rule)
          (renameConfiguration appenderState config)) := hGlobalStep
    _ = some (renameConfiguration appenderState
          (applyWorkRule rule config)) :=
      congrArg Option.some (applyWorkRule_rename appenderState rule config)
    _ = some (renameConfiguration appenderState next) :=
      congrArg (fun value => some (renameConfiguration appenderState value))
        hNext.symm

/-! ### Launches and exact all-input trace -/

theorem headerCursor_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep? (machine problem)
        (renameConfiguration headerState
          (BuilderCompleteHeader.finalConfiguration problem)) =
      some (renameConfiguration cursorState
        (BuilderUnaryPolynomial.initialConfiguration
          (nextTokenSlotPolynomial problem.verifier) problem.input
          (BuilderCompleteHeader.finalOutside problem)
          (BuilderCompleteHeader.headerTokens problem))) := by
  let final := BuilderCompleteHeader.finalConfiguration problem
  have hHalted := machine_isHalted_header_false problem final
  have hLaunch := findWorkRule_launchRules
    (headerState (BuilderCompleteHeader.machine problem).acceptState)
    (cursorState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).startState)
    final.tape.head
  have hBridgeFind : findWorkRule (bridgeRules problem)
      (headerState final.state) final.tape.head =
        some (launchRule
          (headerState (BuilderCompleteHeader.machine problem).acceptState)
          (cursorState
            (BuilderUnaryPolynomial.machine
              (nextTokenSlotPolynomial problem.verifier)).startState)
          final.tape.head) := by
    unfold bridgeRules
    simpa [headerCursorBridge, final,
      BuilderCompleteHeader.finalConfiguration] using
      (findWorkRule_append_of_some _ _ _ _ _ hLaunch)
  have hFind : findWorkRule (machine problem).rules
      (headerState final.state) final.tape.head =
        some (launchRule
          (headerState (BuilderCompleteHeader.machine problem).acceptState)
          (cursorState
            (BuilderUnaryPolynomial.machine
              (nextTokenSlotPolynomial problem.verifier)).startState)
          final.tape.head) := by
    unfold machine rules
    exact findWorkRule_append_of_some _ _ _ _ _ hBridgeFind
  have hStep := workStep?_eq_apply_of_find (machine problem)
    (renameConfiguration headerState final)
    (launchRule
      (headerState (BuilderCompleteHeader.machine problem).acceptState)
      (cursorState
        (BuilderUnaryPolynomial.machine
          (nextTokenSlotPolynomial problem.verifier)).startState)
      final.tape.head) hHalted hFind
  simpa [final, launchRule, applyWorkRule, WorkTape.write, WorkTape.move,
    renameConfiguration, BuilderCompleteHeader.finalConfiguration,
    BuilderCompleteHeader.finalTape,
    BuilderUnaryPolynomial.initialConfiguration] using hStep

theorem cursorAppender_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep? (machine problem)
        (renameConfiguration cursorState
          (BuilderUnaryPolynomial.finalConfiguration
            (nextTokenSlotPolynomial problem.verifier) problem.input
            (BuilderCompleteHeader.finalOutside problem)
            (BuilderCompleteHeader.headerTokens problem))) =
      some (renameConfiguration appenderState
        (BuilderTokenAppender.entryConfiguration .sep
          (BuilderTokenAppender.workspaceTape problem.input
            (finalOutside problem)
            (BuilderCompleteHeader.headerTokens problem)))) := by
  let final := BuilderUnaryPolynomial.finalConfiguration
    (nextTokenSlotPolynomial problem.verifier) problem.input
    (BuilderCompleteHeader.finalOutside problem)
    (BuilderCompleteHeader.headerTokens problem)
  have hHalted := machine_isHalted_cursor_false problem final
  have hLaunch := findWorkRule_launchRules
    (cursorState
      (BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).acceptState)
    (appenderState (BuilderTokenAppender.seekInputState .sep))
    final.tape.head
  have hBridgeOne : findWorkRule (headerCursorBridge problem)
      (cursorState final.state) final.tape.head = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact headerState_ne_cursorState _ _
  have hBridgeFind : findWorkRule (bridgeRules problem)
      (cursorState final.state) final.tape.head =
        some (launchRule
          (cursorState
            (BuilderUnaryPolynomial.machine
              (nextTokenSlotPolynomial problem.verifier)).acceptState)
          (appenderState (BuilderTokenAppender.seekInputState .sep))
          final.tape.head) := by
    unfold bridgeRules
    rw [findWorkRule_append_of_none _ _ _ _ hBridgeOne]
    simpa [cursorAppenderBridge, final,
      BuilderUnaryPolynomial.finalConfiguration] using hLaunch
  have hFind : findWorkRule (machine problem).rules
      (cursorState final.state) final.tape.head =
        some (launchRule
          (cursorState
            (BuilderUnaryPolynomial.machine
              (nextTokenSlotPolynomial problem.verifier)).acceptState)
          (appenderState (BuilderTokenAppender.seekInputState .sep))
          final.tape.head) := by
    unfold machine rules
    exact findWorkRule_append_of_some _ _ _ _ _ hBridgeFind
  have hStep := workStep?_eq_apply_of_find (machine problem)
    (renameConfiguration cursorState final)
    (launchRule
      (cursorState
        (BuilderUnaryPolynomial.machine
          (nextTokenSlotPolynomial problem.verifier)).acceptState)
      (appenderState (BuilderTokenAppender.seekInputState .sep))
      final.tape.head) hHalted hFind
  simpa [final, launchRule, applyWorkRule, WorkTape.write, WorkTape.move,
    renameConfiguration, BuilderUnaryPolynomial.finalConfiguration,
    BuilderTokenAppender.entryConfiguration, finalOutside] using hStep

theorem header_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem) (BuilderCompleteHeader.workSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (renameConfiguration headerState
        (BuilderCompleteHeader.finalConfiguration problem)) := by
  have hTransport := PipelineStageBridges.workRunExact?_transport
    (BuilderCompleteHeader.machine problem) (machine problem) headerState
    (header_workStep_of_some problem) (BuilderCompleteHeader.workSteps problem)
    (workStartConfiguration (BuilderCompleteHeader.machine problem)
      (rawInputWorkTape problem.input))
    (BuilderCompleteHeader.finalConfiguration problem)
    (BuilderCompleteHeader.workRunExact problem)
  simpa [machine, workStartConfiguration, renameConfiguration] using hTransport

theorem cursor_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem)
        (BuilderUnaryPolynomial.workSteps
          (nextTokenSlotPolynomial problem.verifier) problem.input)
        (renameConfiguration cursorState
          (BuilderUnaryPolynomial.initialConfiguration
            (nextTokenSlotPolynomial problem.verifier) problem.input
            (BuilderCompleteHeader.finalOutside problem)
            (BuilderCompleteHeader.headerTokens problem))) =
      some (renameConfiguration cursorState
        (BuilderUnaryPolynomial.finalConfiguration
          (nextTokenSlotPolynomial problem.verifier) problem.input
          (BuilderCompleteHeader.finalOutside problem)
          (BuilderCompleteHeader.headerTokens problem))) := by
  have hLocal := BuilderUnaryPolynomial.workRunExact
    (nextTokenSlotPolynomial problem.verifier) problem.input
    (BuilderCompleteHeader.finalOutside problem)
    (BuilderCompleteHeader.headerTokens problem)
  exact PipelineStageBridges.workRunExact?_transport
    (BuilderUnaryPolynomial.machine
      (nextTokenSlotPolynomial problem.verifier))
    (machine problem) cursorState (cursor_workStep_of_some problem)
    (BuilderUnaryPolynomial.workSteps
      (nextTokenSlotPolynomial problem.verifier) problem.input)
    (BuilderUnaryPolynomial.initialConfiguration
      (nextTokenSlotPolynomial problem.verifier) problem.input
      (BuilderCompleteHeader.finalOutside problem)
      (BuilderCompleteHeader.headerTokens problem))
    (BuilderUnaryPolynomial.finalConfiguration
      (nextTokenSlotPolynomial problem.verifier) problem.input
      (BuilderCompleteHeader.finalOutside problem)
      (BuilderCompleteHeader.headerTokens problem)) hLocal

theorem appender_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem)
        (BuilderTokenAppender.workSteps problem.input
          (BuilderCompleteHeader.headerTokens problem))
        (renameConfiguration appenderState
          (BuilderTokenAppender.entryConfiguration .sep
            (BuilderTokenAppender.workspaceTape problem.input
              (finalOutside problem)
              (BuilderCompleteHeader.headerTokens problem)))) =
      some (finalConfiguration problem) := by
  have hLocal := BuilderTokenAppender.appendToken_workRunExact
    problem.input (finalOutside problem)
    (BuilderCompleteHeader.headerTokens problem) .sep
  have hTransport := PipelineStageBridges.workRunExact?_transport
    BuilderTokenAppender.machine (machine problem) appenderState
    (appender_workStep_of_some problem)
    (BuilderTokenAppender.workSteps problem.input
      (BuilderCompleteHeader.headerTokens problem))
    (BuilderTokenAppender.entryConfiguration .sep
      (BuilderTokenAppender.workspaceTape problem.input
        (finalOutside problem) (BuilderCompleteHeader.headerTokens problem)))
    (BuilderTokenAppender.finalConfiguration problem.input
      (finalOutside problem)
      (BuilderCompleteHeader.headerTokens problem ++ [.sep])) hLocal
  simpa [finalConfiguration, finalTape, bodyStartTokens, machine,
    BuilderTokenAppender.finalConfiguration, renameConfiguration] using
      hTransport

/-- Every raw input follows one exact successful trace through the complete
header, retained cursor construction, and first body token. -/
theorem workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem) (workSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (finalConfiguration problem) := by
  have hLaunchOne : workRunExact? (machine problem) 1
      (renameConfiguration headerState
        (BuilderCompleteHeader.finalConfiguration problem)) =
      some (renameConfiguration cursorState
        (BuilderUnaryPolynomial.initialConfiguration
          (nextTokenSlotPolynomial problem.verifier) problem.input
          (BuilderCompleteHeader.finalOutside problem)
          (BuilderCompleteHeader.headerTokens problem))) := by
    change
      (match workStep? (machine problem)
          (renameConfiguration headerState
            (BuilderCompleteHeader.finalConfiguration problem)) with
       | none => none
       | some next => workRunExact? (machine problem) 0 next) = _
    rw [headerCursor_launch_workStep problem]
    rfl
  have hLaunchTwo : workRunExact? (machine problem) 1
      (renameConfiguration cursorState
        (BuilderUnaryPolynomial.finalConfiguration
          (nextTokenSlotPolynomial problem.verifier) problem.input
          (BuilderCompleteHeader.finalOutside problem)
          (BuilderCompleteHeader.headerTokens problem))) =
      some (renameConfiguration appenderState
        (BuilderTokenAppender.entryConfiguration .sep
          (BuilderTokenAppender.workspaceTape problem.input
            (finalOutside problem)
            (BuilderCompleteHeader.headerTokens problem)))) := by
    change
      (match workStep? (machine problem)
          (renameConfiguration cursorState
            (BuilderUnaryPolynomial.finalConfiguration
              (nextTokenSlotPolynomial problem.verifier) problem.input
              (BuilderCompleteHeader.finalOutside problem)
              (BuilderCompleteHeader.headerTokens problem))) with
       | none => none
       | some next => workRunExact? (machine problem) 0 next) = _
    rw [cursorAppender_launch_workStep problem]
    rfl
  have h01 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem) (BuilderCompleteHeader.workSteps problem) 1
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (renameConfiguration headerState
      (BuilderCompleteHeader.finalConfiguration problem))
    (renameConfiguration cursorState
      (BuilderUnaryPolynomial.initialConfiguration
        (nextTokenSlotPolynomial problem.verifier) problem.input
        (BuilderCompleteHeader.finalOutside problem)
        (BuilderCompleteHeader.headerTokens problem)))
    (header_workRunExact problem) hLaunchOne
  have h02 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem) (BuilderCompleteHeader.workSteps problem + 1)
    (BuilderUnaryPolynomial.workSteps
      (nextTokenSlotPolynomial problem.verifier) problem.input)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (renameConfiguration cursorState
      (BuilderUnaryPolynomial.initialConfiguration
        (nextTokenSlotPolynomial problem.verifier) problem.input
        (BuilderCompleteHeader.finalOutside problem)
        (BuilderCompleteHeader.headerTokens problem)))
    (renameConfiguration cursorState
      (BuilderUnaryPolynomial.finalConfiguration
        (nextTokenSlotPolynomial problem.verifier) problem.input
        (BuilderCompleteHeader.finalOutside problem)
        (BuilderCompleteHeader.headerTokens problem))) h01
    (cursor_workRunExact problem)
  have h03 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem)
    (BuilderCompleteHeader.workSteps problem + 1 +
      BuilderUnaryPolynomial.workSteps
        (nextTokenSlotPolynomial problem.verifier) problem.input) 1
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (renameConfiguration cursorState
      (BuilderUnaryPolynomial.finalConfiguration
        (nextTokenSlotPolynomial problem.verifier) problem.input
        (BuilderCompleteHeader.finalOutside problem)
        (BuilderCompleteHeader.headerTokens problem)))
    (renameConfiguration appenderState
      (BuilderTokenAppender.entryConfiguration .sep
        (BuilderTokenAppender.workspaceTape problem.input
          (finalOutside problem)
          (BuilderCompleteHeader.headerTokens problem)))) h02 hLaunchTwo
  have h04 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem)
    (BuilderCompleteHeader.workSteps problem + 1 +
      BuilderUnaryPolynomial.workSteps
        (nextTokenSlotPolynomial problem.verifier) problem.input + 1)
    (BuilderTokenAppender.workSteps problem.input
      (BuilderCompleteHeader.headerTokens problem))
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (renameConfiguration appenderState
      (BuilderTokenAppender.entryConfiguration .sep
        (BuilderTokenAppender.workspaceTape problem.input
          (finalOutside problem)
          (BuilderCompleteHeader.headerTokens problem))))
    (finalConfiguration problem) h03 (appender_workRunExact problem)
  simpa [workSteps, Nat.add_assoc] using h04

/-! ### Canonical body prefix and external bound -/

theorem bodyStartTokens_eq_canonical_prefix {language : Language}
    (problem : VerifierTableauProblem language) :
    bodyStartTokens problem =
      encodeUnaryTokens problem.FormulaWidth ++ [.sep] := by
  rw [bodyStartTokens,
    BuilderCompleteHeader.headerTokens_eq_encodeUnaryTokens]

private theorem scheduledShapeConstraints_entry_some
    {language : Language} (problem : VerifierTableauProblem language)
    (entry : Option (LocalConstraint problem.FormulaWidth))
    (hEntry : entry ∈ problem.scheduledShapeConstraints) :
    ∃ constraint, entry = some constraint := by
  unfold VerifierTableauProblem.scheduledShapeConstraints at hEntry
  rw [List.mem_flatMap] at hEntry
  rcases hEntry with ⟨time, _hTime, hEntry⟩
  simp only [List.mem_append, List.mem_map, List.mem_cons] at hEntry
  rcases hEntry with hPosition | hHead | hState | hEmpty
  · rcases hPosition with ⟨position, _hPosition, hEqual⟩
    exact ⟨problem.symbolShapeAt time position, hEqual.symm⟩
  · exact ⟨problem.headShapeAt time, hHead⟩
  · exact ⟨problem.stateShapeAt time, hState⟩
  · contradiction

private theorem formulaConstraintSchedule_starts_some
    {language : Language} (problem : VerifierTableauProblem language) :
    ∃ constraint rest,
      problem.formulaConstraintSchedule = some constraint :: rest := by
  cases hShape : problem.scheduledShapeConstraints with
  | nil =>
      exact ⟨.require
          (problem.stateLiteral problem.initialTime problem.startState),
        some (.require
            (problem.headLiteral problem.initialTime
              problem.initialHeadPosition)) ::
          FormulaSchedule.pad
            (1 + 2 * ((problem.certificateLimit + 1) *
              problem.dimensions.tapeWidth problem.tableauInputMode))
            problem.initialSymbolsProgram ++
          problem.scheduledControlConstraints ++
          problem.scheduledPreservationConstraints ++
          [some (.require
            (problem.stateLiteral problem.finalTime
              problem.acceptingState))], by
        unfold VerifierTableauProblem.formulaConstraintSchedule
          VerifierTableauProblem.scheduledInitialConstraints
        rw [hShape]
        rfl⟩
  | cons entry rest =>
      have hEntry : entry ∈ problem.scheduledShapeConstraints := by
        rw [hShape]
        exact List.mem_cons_self
      rcases scheduledShapeConstraints_entry_some problem entry hEntry with
        ⟨constraint, hConstraint⟩
      refine ⟨constraint,
        rest ++ problem.scheduledInitialConstraints ++
          problem.scheduledControlConstraints ++
          problem.scheduledPreservationConstraints ++
          [some (.require
            (problem.stateLiteral problem.finalTime
              problem.acceptingState))], ?_⟩
      unfold VerifierTableauProblem.formulaConstraintSchedule
      rw [hShape, hConstraint]
      simp [List.append_assoc]

private theorem localConstraint_emit_cons {width : Nat}
    (constraint : LocalConstraint width) :
    ∃ clause rest, LocalConstraint.emit constraint = clause :: rest := by
  cases constraint with
  | require literal =>
      exact ⟨[literal], [], rfl⟩
  | implication premises conclusion =>
      exact ⟨BoundedClause.negated premises ++ [conclusion], [], rfl⟩
  | exactlyOne variables =>
      exact ⟨atLeastOneBoundedClause variables,
        atMostOneBoundedClauses variables, rfl⟩

private theorem formulaClauseSchedule_starts_some
    {language : Language} (problem : VerifierTableauProblem language) :
    ∃ clause rest,
      problem.formulaClauseSchedule = some clause :: rest := by
  rcases formulaConstraintSchedule_starts_some problem with
    ⟨constraint, constraints, hConstraints⟩
  rcases localConstraint_emit_cons constraint with
    ⟨clause, clauses, hClauses⟩
  unfold VerifierTableauProblem.formulaClauseSchedule
  rw [hConstraints]
  simp only [List.flatMap_cons]
  dsimp [VerifierTableauProblem.scheduledConstraintClauses]
  rw [hClauses]
  unfold FormulaSchedule.pad
  exact ⟨clause,
    List.map some clauses ++
      List.replicate
        (problem.formulaClauseSlotsPerConstraint - (clause :: clauses).length)
        none ++
      constraints.flatMap problem.scheduledConstraintClauses, by
        simp [List.append_assoc]⟩

private theorem formulaClauseTokens_starts_separator
    {language : Language} (problem : VerifierTableauProblem language) :
    ∃ rest,
      problem.formulaClauseSchedule.flatMap problem.scheduledClauseTokens =
        some CNFToken.sep :: rest := by
  rcases formulaClauseSchedule_starts_some problem with
    ⟨clause, clauses, hClauses⟩
  rw [hClauses]
  simp only [List.flatMap_cons]
  let firstTail :=
    List.map some
        (encodeLiteralListTokens (BoundedClause.emit clause) ++
          [CNFToken.finish]) ++
      List.replicate
        (problem.formulaTokensPerClause -
          (CNFToken.sep ::
            (encodeLiteralListTokens (BoundedClause.emit clause) ++
              [CNFToken.finish])).length)
        none
  have hFirst : problem.scheduledClauseTokens (some clause) =
      some CNFToken.sep :: firstTail := by
    simp [VerifierTableauProblem.scheduledClauseTokens, FormulaSchedule.pad,
      encodeClauseTokens, firstTail, List.append_assoc]
  rw [hFirst]
  exact ⟨firstTail ++ clauses.flatMap problem.scheduledClauseTokens, rfl⟩

/-- The first token opportunity after the padded header is populated by the
separator beginning the first canonical clause. -/
theorem firstBodyTokenSlotDirect_eq_separator {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formulaTokenSlotDirect
        (problem.formulaVariableSlotBound + 1) =
      some (some CNFToken.sep) := by
  rw [problem.formulaTokenSlotDirect_eq]
  have hHeader :
      (FormulaSchedule.pad (problem.formulaVariableSlotBound + 1)
        (encodeUnaryTokens problem.FormulaWidth)).length =
      problem.formulaVariableSlotBound + 1 := by
    apply FormulaSchedule.pad_length
    rw [encodeUnaryTokens_length]
    unfold VerifierTableauProblem.formulaVariableSlotBound
    exact Nat.add_le_add_right
      problem.formulaWidth_le_formulaVariableCountPolynomial 1
  unfold VerifierTableauProblem.formulaTokenSchedule
  rw [List.append_assoc]
  rw [List.getElem?_append]
  rw [hHeader]
  simp only [Nat.lt_irrefl, ↓reduceIte, Nat.sub_self]
  rcases formulaClauseTokens_starts_separator problem with ⟨rest, hRest⟩
  rw [hRest]
  rfl

private theorem encodeTokenPairs_append_local
    (left right : List CNFToken) :
    encodeTokenPairs (left ++ right) =
      encodeTokenPairs left ++ encodeTokenPairs right := by
  induction left with
  | nil => rfl
  | cons token rest ih =>
      cases token <;>
        simp [encodeTokenPairs, ih, List.append_assoc]

private theorem encodeCNFTokens_starts_bodyPrefix
    {language : Language} (problem : VerifierTableauProblem language) :
    ∃ rest,
      encodeCNFTokens problem.formula =
        encodeUnaryTokens problem.FormulaWidth ++ CNFToken.sep :: rest := by
  rcases formulaClauseTokens_starts_separator problem with
    ⟨clauseTail, hClauseTail⟩
  refine ⟨FormulaSchedule.emit clauseTail ++ [CNFToken.finish], ?_⟩
  rw [← problem.formulaTokenSchedule_emit_eq_encodeCNFTokens]
  unfold VerifierTableauProblem.formulaTokenSchedule
  rw [FormulaSchedule.emit_append, FormulaSchedule.emit_append,
    FormulaSchedule.emit_pad, hClauseTail]
  simp [List.append_assoc]

/-- The emitted token pairs are exactly the complete canonical header plus
the first separator beginning the formula body. -/
theorem finalTokenBits_eq_encodedFormula_bodyStart {language : Language}
    (problem : VerifierTableauProblem language) :
    encodeTokenPairs (bodyStartTokens problem) =
      problem.encodedFormula.take (2 * (problem.FormulaWidth + 2)) := by
  rw [bodyStartTokens_eq_canonical_prefix]
  rcases encodeCNFTokens_starts_bodyPrefix problem with ⟨rest, hTokens⟩
  have hLength := encodeTokenPairs_length
    (encodeUnaryTokens problem.FormulaWidth ++ [CNFToken.sep])
  have hUnaryLength := encodeUnaryTokens_length problem.FormulaWidth
  simp only [List.length_append, List.length_singleton, hUnaryLength] at hLength
  let suffix := encodeTokenPairs rest ++ [false]
  have hShape : problem.encodedFormula =
      encodeTokenPairs
          (encodeUnaryTokens problem.FormulaWidth ++ [CNFToken.sep]) ++
        suffix := by
    simp only [VerifierTableauProblem.encodedFormula, encodeCNF]
    rw [hTokens, show CNFToken.sep :: rest = [CNFToken.sep] ++ rest by rfl,
      ← List.append_assoc, encodeTokenPairs_append_local]
    simp [suffix, List.append_assoc]
  rw [hShape, ← hLength]
  exact List.take_left.symm

private theorem appender_workSteps_le (input : BitString)
    (output : List CNFToken) :
    BuilderTokenAppender.workSteps input output ≤
      4 * input.length + 2 * output.length + 8 := by
  have hSource := BuilderTokenAppender.sourceCellCount_le input
  unfold BuilderTokenAppender.workSteps BuilderTokenAppender.halfSteps
  omega

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderCompleteHeader.rawTimeBound problem.verifier).eval
          problem.input.length + 72 +
        6 * BuilderUnaryPolynomial.workSteps
          (nextTokenSlotPolynomial problem.verifier) problem.input +
        24 * problem.input.length +
        12 * BuilderCompleteHeader.width problem := by
  rw [rawTimeBound]
  simp [scalePolynomial, BuilderUnaryPolynomial.workTimePolynomial_eval,
    BuilderCompleteHeader.width, BuilderCompleteHeader.widthPolynomial,
    Nat.add_assoc]

theorem rawTimeBound_le {language : Language}
    (problem : VerifierTableauProblem language) :
    6 * workSteps problem ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hHeader := BuilderCompleteHeader.rawTimeBound_le problem
  have hAppender := appender_workSteps_le problem.input
    (BuilderCompleteHeader.headerTokens problem)
  have hHeaderLength :
      (BuilderCompleteHeader.headerTokens problem).length =
        BuilderCompleteHeader.width problem + 1 := by
    simp [BuilderCompleteHeader.headerTokens]
  rw [hHeaderLength] at hAppender
  rw [rawTimeBound_eval]
  unfold workSteps
  omega

private theorem finalConfiguration_isHalted {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).isHalted (finalConfiguration problem) = true := by
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

theorem boundedDecide_compile_accept {language : Language}
    (problem : VerifierTableauProblem language) :
    boundedDecide (compileWorkMachine (machine problem))
        ((rawTimeBound problem.verifier).eval problem.input.length)
        problem.input = .accept := by
  apply (boundedDecide_accept_iff_final
    (compileWorkMachine (machine problem))
    ((rawTimeBound problem.verifier).eval problem.input.length)
    problem.input).mpr
  exact (run_compile_rawTimeBound_blankEquivalent problem).1

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
  rfl

/-! ### Fail-closed trace boundaries -/

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

/-- The complete-header endpoint remains nonhalting until the first new
bridge launches the unary next-token cursor. -/
theorem headerEndpoint_before_launch_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderCompleteHeader.workSteps problem)
        (rawInputWorkTape problem.input) = .timeout := by
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact (machine problem)
    (BuilderCompleteHeader.workSteps problem)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (renameConfiguration headerState
      (BuilderCompleteHeader.finalConfiguration problem))
    (header_workRunExact problem)]
  exact verdict_timeout_of_not_halted problem _
    (machine_isHalted_header_false problem
      (BuilderCompleteHeader.finalConfiguration problem))

private theorem findWorkRule_none_of_sources_ne
    (localRules : List WorkRule) (state : Nat) (symbol : WorkSymbol)
    (hSource : ∀ rule ∈ localRules, rule.sourceState ≠ state) :
    findWorkRule localRules state symbol = none := by
  induction localRules with
  | nil => rfl
  | cons first rest ih =>
      rw [findWorkRule_cons_of_not_matches]
      · exact ih (fun rule hMem => hSource rule (List.mem_cons_of_mem first hMem))
      · intro hMatch
        exact hSource first (List.mem_cons_self) hMatch.1

private theorem findWorkRule_headerReject_none {language : Language}
    (problem : VerifierTableauProblem language) (symbol : WorkSymbol) :
    findWorkRule (machine problem).rules
        (headerState (BuilderCompleteHeader.machine problem).rejectState)
        symbol = none := by
  let headerMachine := BuilderCompleteHeader.machine problem
  have hBridgeOne : findWorkRule (headerCursorBridge problem)
      (headerState headerMachine.rejectState) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro h
    exact BuilderCompleteHeader.machine_acceptState_ne_rejectState problem
      (headerState_injective h)
  have hBridgeTwo : findWorkRule (cursorAppenderBridge problem)
      (headerState headerMachine.rejectState) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact Ne.symm (headerState_ne_cursorState _ _)
  have hBridges : findWorkRule (bridgeRules problem)
      (headerState headerMachine.rejectState) symbol = none := by
    unfold bridgeRules
    rw [findWorkRule_append_of_none _ _ _ _ hBridgeOne]
    exact hBridgeTwo
  have hLocal : findWorkRule headerMachine.rules
      headerMachine.rejectState symbol = none := by
    apply findWorkRule_none_of_sources_ne
    intro rule hMem
    exact completeHeader_rule_source_ne_reject problem rule hMem
  have hHeader := findWorkRule_rename headerState headerState_injective
    headerMachine.rules headerMachine.rejectState symbol
  rw [hLocal] at hHeader
  have hCursor : findWorkRule
      ((BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).rules.map
          (renameRule cursorState))
      (headerState headerMachine.rejectState) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact Ne.symm (headerState_ne_cursorState _ _)
  have hAppender : findWorkRule
      (BuilderTokenAppender.machine.rules.map (renameRule appenderState))
      (headerState headerMachine.rejectState) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact Ne.symm (headerState_ne_appenderState _ _)
  unfold machine rules componentRules
  rw [findWorkRule_append_of_none _ _ _ _ hBridges,
    findWorkRule_append_of_none _ _ _ _ hHeader,
    findWorkRule_append_of_none _ _ _ _ hCursor]
  exact hAppender

private theorem headerReject_workStep_none {language : Language}
    (problem : VerifierTableauProblem language) (tape : WorkTape) :
    workStep? (machine problem)
        (renameConfiguration headerState
          { state := (BuilderCompleteHeader.machine problem).rejectState
            tape := tape }) = none := by
  have hFind := findWorkRule_headerReject_none problem tape.head
  unfold workStep?
  rw [machine_isHalted_header_false problem]
  change
    (match findWorkRule (machine problem).rules
        (headerState (BuilderCompleteHeader.machine problem).rejectState)
        tape.head with
     | none => none
     | some rule =>
         some (applyWorkRule rule
           (renameConfiguration headerState
             { state := (BuilderCompleteHeader.machine problem).rejectState
               tape := tape }))) = none
  rw [hFind]

/-- A reject endpoint inside the renamed header component is deliberately
not a global reject; with no outgoing rule it remains timeout for all fuel. -/
theorem headerRejectEndpoint_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (tape : WorkTape) :
    (let config := renameConfiguration headerState
        { state := (BuilderCompleteHeader.machine problem).rejectState
          tape := tape }
     let result := workRun (machine problem) fuel config
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let bad : WorkConfiguration :=
    { state := (BuilderCompleteHeader.machine problem).rejectState
      tape := tape }
  exact stuck_timeout problem fuel (renameConfiguration headerState bad)
    (machine_isHalted_header_false problem bad)
    (by simpa [bad] using headerReject_workStep_none problem tape)

private theorem cursorEndpoint_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem)
        (BuilderCompleteHeader.workSteps problem + 1 +
          BuilderUnaryPolynomial.workSteps
            (nextTokenSlotPolynomial problem.verifier) problem.input)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (renameConfiguration cursorState
        (BuilderUnaryPolynomial.finalConfiguration
          (nextTokenSlotPolynomial problem.verifier) problem.input
          (BuilderCompleteHeader.finalOutside problem)
          (BuilderCompleteHeader.headerTokens problem))) := by
  let headerFinal := renameConfiguration headerState
    (BuilderCompleteHeader.finalConfiguration problem)
  let cursorInitial := renameConfiguration cursorState
    (BuilderUnaryPolynomial.initialConfiguration
      (nextTokenSlotPolynomial problem.verifier) problem.input
      (BuilderCompleteHeader.finalOutside problem)
      (BuilderCompleteHeader.headerTokens problem))
  let cursorFinal := renameConfiguration cursorState
    (BuilderUnaryPolynomial.finalConfiguration
      (nextTokenSlotPolynomial problem.verifier) problem.input
      (BuilderCompleteHeader.finalOutside problem)
      (BuilderCompleteHeader.headerTokens problem))
  have hHeader : workRunExact? (machine problem)
      (BuilderCompleteHeader.workSteps problem)
      (workStartConfiguration (machine problem)
        (rawInputWorkTape problem.input)) = some headerFinal := by
    simpa [headerFinal] using header_workRunExact problem
  have hLaunch : workRunExact? (machine problem) 1 headerFinal =
      some cursorInitial := by
    change
      (match workStep? (machine problem) headerFinal with
       | none => none
       | some next => workRunExact? (machine problem) 0 next) =
        some cursorInitial
    rw [show workStep? (machine problem) headerFinal = some cursorInitial by
      simpa [headerFinal, cursorInitial] using
        headerCursor_launch_workStep problem]
    rfl
  have hCursor : workRunExact? (machine problem)
      (BuilderUnaryPolynomial.workSteps
        (nextTokenSlotPolynomial problem.verifier) problem.input)
      cursorInitial = some cursorFinal := by
    simpa [cursorInitial, cursorFinal] using cursor_workRunExact problem
  have h01 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem) (BuilderCompleteHeader.workSteps problem) 1
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    headerFinal cursorInitial hHeader hLaunch
  have h02 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem) (BuilderCompleteHeader.workSteps problem + 1)
    (BuilderUnaryPolynomial.workSteps
      (nextTokenSlotPolynomial problem.verifier) problem.input)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    cursorInitial cursorFinal h01 hCursor
  simpa [cursorFinal, Nat.add_assoc] using h02

/-- The exact cursor endpoint is still nonhalting until the second new
bridge launches the separator appender. -/
theorem cursorEndpoint_before_launch_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderCompleteHeader.workSteps problem + 1 +
          BuilderUnaryPolynomial.workSteps
            (nextTokenSlotPolynomial problem.verifier) problem.input)
        (rawInputWorkTape problem.input) = .timeout := by
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact (machine problem)
    (BuilderCompleteHeader.workSteps problem + 1 +
      BuilderUnaryPolynomial.workSteps
        (nextTokenSlotPolynomial problem.verifier) problem.input)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (renameConfiguration cursorState
      (BuilderUnaryPolynomial.finalConfiguration
        (nextTokenSlotPolynomial problem.verifier) problem.input
        (BuilderCompleteHeader.finalOutside problem)
        (BuilderCompleteHeader.headerTokens problem)))
    (cursorEndpoint_workRunExact problem)]
  exact verdict_timeout_of_not_halted problem _
    (machine_isHalted_cursor_false problem
      (BuilderUnaryPolynomial.finalConfiguration
        (nextTokenSlotPolynomial problem.verifier) problem.input
        (BuilderCompleteHeader.finalOutside problem)
        (BuilderCompleteHeader.headerTokens problem)))

private theorem findWorkRule_cursorDead_none {language : Language}
    (problem : VerifierTableauProblem language) (symbol : WorkSymbol) :
    findWorkRule (machine problem).rules
        (cursorState (BuilderUnaryPolynomial.deadState
          (nextTokenSlotPolynomial problem.verifier))) symbol = none := by
  let polynomial := nextTokenSlotPolynomial problem.verifier
  have hBridgeOne : findWorkRule (headerCursorBridge problem)
      (cursorState (BuilderUnaryPolynomial.deadState polynomial)) symbol =
        none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact headerState_ne_cursorState _ _
  have hBridgeTwo : findWorkRule (cursorAppenderBridge problem)
      (cursorState (BuilderUnaryPolynomial.deadState polynomial)) symbol =
        none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro h
    have hLocal := cursorState_injective h
    unfold BuilderUnaryPolynomial.deadState at hLocal
    change BuilderUnaryPolynomial.acceptState polynomial =
      BuilderUnaryPolynomial.stateCount polynomial + 2 at hLocal
    unfold BuilderUnaryPolynomial.acceptState at hLocal
    omega
  have hBridges : findWorkRule (bridgeRules problem)
      (cursorState (BuilderUnaryPolynomial.deadState polynomial)) symbol =
        none := by
    unfold bridgeRules
    rw [findWorkRule_append_of_none _ _ _ _ hBridgeOne]
    exact hBridgeTwo
  have hHeader : findWorkRule
      ((BuilderCompleteHeader.machine problem).rules.map
        (renameRule headerState))
      (cursorState (BuilderUnaryPolynomial.deadState polynomial)) symbol =
        none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact headerState_ne_cursorState _ _
  have hLocal : findWorkRule
      (BuilderUnaryPolynomial.machine polynomial).rules
      (BuilderUnaryPolynomial.deadState polynomial) symbol = none := by
    apply findWorkRule_none_of_sources_ne
    intro rule hMem hEqual
    have hBound := BuilderUnaryPolynomial.rule_source_lt_acceptState
      polynomial rule hMem
    change rule.sourceState < BuilderUnaryPolynomial.stateCount polynomial
      at hBound
    rw [hEqual] at hBound
    unfold BuilderUnaryPolynomial.deadState at hBound
    omega
  have hCursor := findWorkRule_rename cursorState cursorState_injective
    (BuilderUnaryPolynomial.machine polynomial).rules
    (BuilderUnaryPolynomial.deadState polynomial) symbol
  rw [hLocal] at hCursor
  have hAppender : findWorkRule
      (BuilderTokenAppender.machine.rules.map (renameRule appenderState))
      (cursorState (BuilderUnaryPolynomial.deadState polynomial)) symbol =
        none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact Ne.symm (cursorState_ne_appenderState _ source)
  unfold machine rules componentRules
  rw [findWorkRule_append_of_none _ _ _ _ hBridges,
    findWorkRule_append_of_none _ _ _ _ hHeader,
    findWorkRule_append_of_none _ _ _ _ hCursor]
  exact hAppender

private theorem cursorDead_workStep_none {language : Language}
    (problem : VerifierTableauProblem language) (tape : WorkTape) :
    workStep? (machine problem)
        (renameConfiguration cursorState
          { state := BuilderUnaryPolynomial.deadState
              (nextTokenSlotPolynomial problem.verifier)
            tape := tape }) = none := by
  have hFind := findWorkRule_cursorDead_none problem tape.head
  unfold workStep?
  rw [machine_isHalted_cursor_false problem]
  change
    (match findWorkRule (machine problem).rules
        (cursorState (BuilderUnaryPolynomial.deadState
          (nextTokenSlotPolynomial problem.verifier))) tape.head with
     | none => none
     | some rule =>
         some (applyWorkRule rule
           (renameConfiguration cursorState
             { state := BuilderUnaryPolynomial.deadState
                 (nextTokenSlotPolynomial problem.verifier)
               tape := tape }))) = none
  rw [hFind]

/-- Every evaluator failure target is isolated from both global halts and
all component tables, so it remains timeout for every fuel budget. -/
theorem cursorDeadState_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (tape : WorkTape) :
    (let config := renameConfiguration cursorState
        { state := BuilderUnaryPolynomial.deadState
            (nextTokenSlotPolynomial problem.verifier)
          tape := tape }
     let result := workRun (machine problem) fuel config
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let bad : WorkConfiguration :=
    { state := BuilderUnaryPolynomial.deadState
        (nextTokenSlotPolynomial problem.verifier)
      tape := tape }
  exact stuck_timeout problem fuel (renameConfiguration cursorState bad)
    (machine_isHalted_cursor_false problem bad)
    (by simpa [bad] using cursorDead_workStep_none problem tape)

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

private theorem findWorkRule_appender_of_none {language : Language}
    (problem : VerifierTableauProblem language)
    (state : Nat) (symbol : WorkSymbol)
    (hFind : findWorkRule BuilderTokenAppender.machine.rules state symbol =
      none) :
    findWorkRule (machine problem).rules (appenderState state) symbol =
      none := by
  have hBridgeOne : findWorkRule (headerCursorBridge problem)
      (appenderState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact headerState_ne_appenderState _ _
  have hBridgeTwo : findWorkRule (cursorAppenderBridge problem)
      (appenderState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact cursorState_ne_appenderState _ _
  have hBridges : findWorkRule (bridgeRules problem)
      (appenderState state) symbol = none := by
    unfold bridgeRules
    rw [findWorkRule_append_of_none _ _ _ _ hBridgeOne]
    exact hBridgeTwo
  have hHeader : findWorkRule
      ((BuilderCompleteHeader.machine problem).rules.map
        (renameRule headerState)) (appenderState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact headerState_ne_appenderState _ _
  have hCursor : findWorkRule
      ((BuilderUnaryPolynomial.machine
        (nextTokenSlotPolynomial problem.verifier)).rules.map
          (renameRule cursorState))
      (appenderState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact cursorState_ne_appenderState _ _
  have hRenamed := findWorkRule_rename appenderState appenderState_injective
    BuilderTokenAppender.machine.rules state symbol
  rw [hFind] at hRenamed
  unfold machine rules componentRules
  rw [findWorkRule_append_of_none _ _ _ _ hBridges,
    findWorkRule_append_of_none _ _ _ _ hHeader,
    findWorkRule_append_of_none _ _ _ _ hCursor]
  exact hRenamed

private theorem appender_workStep_none_of_local {language : Language}
    (problem : VerifierTableauProblem language)
    (config : WorkConfiguration)
    (hLocalHalted : BuilderTokenAppender.machine.isHalted config = false)
    (hLocalStep : workStep? BuilderTokenAppender.machine config = none) :
    workStep? (machine problem) (renameConfiguration appenderState config) =
      none := by
  have hFind := findWorkRule_none_of_workStep_none
    BuilderTokenAppender.machine config hLocalHalted hLocalStep
  have hGlobalFind := findWorkRule_appender_of_none problem
    config.state config.tape.head hFind
  unfold workStep?
  rw [machine_isHalted_appender_false_of_local problem config hLocalHalted]
  change
    (match findWorkRule (machine problem).rules
        (appenderState config.state) config.tape.head with
     | none => none
     | some rule =>
         some (applyWorkRule rule
           (renameConfiguration appenderState config))) = none
  rw [hGlobalFind]

/-- An invalid tally-phase symbol in the separator appender cannot fall
through to a global accept or reject endpoint. -/
theorem malformedAppenderTally_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (request : CNFToken) (left right : List WorkSymbol) :
    (let config := renameConfiguration appenderState
        (BuilderTokenAppender.malformedTallyConfiguration
          request left right)
     let result := workRun (machine problem) fuel config
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let bad := BuilderTokenAppender.malformedTallyConfiguration
    request left right
  have hLocalHalted :=
    BuilderTokenAppender.malformedTallySymbol_isHalted_false
      request left right
  have hLocalStep := BuilderTokenAppender.malformedTallySymbol_workStep_none
    request left right
  have hStep := appender_workStep_none_of_local problem bad
    hLocalHalted hLocalStep
  exact stuck_timeout problem fuel (renameConfiguration appenderState bad)
    (machine_isHalted_appender_false_of_local problem bad hLocalHalted) hStep

/-- An invalid output-phase symbol in the separator appender likewise
remains timeout. -/
theorem malformedAppenderOutput_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (request : CNFToken) (left right : List WorkSymbol) :
    (let config := renameConfiguration appenderState
        (BuilderTokenAppender.malformedOutputConfiguration
          request left right)
     let result := workRun (machine problem) fuel config
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let bad := BuilderTokenAppender.malformedOutputConfiguration
    request left right
  have hLocalHalted :=
    BuilderTokenAppender.malformedOutputSymbol_isHalted_false
      request left right
  have hLocalStep := BuilderTokenAppender.malformedOutputSymbol_workStep_none
    request left right
  have hStep := appender_workStep_none_of_local problem bad
    hLocalHalted hLocalStep
  exact stuck_timeout problem fuel (renameConfiguration appenderState bad)
    (machine_isHalted_appender_false_of_local problem bad hLocalHalted) hStep

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

end BuilderBodyStartPrefix

end CookLevin

end PNP.Concrete
